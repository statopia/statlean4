#!/usr/bin/env bash
# Lightweight fallback prove loop — for CI / non-Claude-Code environments.
# Primary prove path is /prove-deep (DAG scheduler inside Claude Code).
set -euo pipefail

REPO_ROOT=${1:?usage: prove_loop.sh <repo_root>}
REPO_ROOT=$(python3 -c 'import os,sys; print(os.path.abspath(sys.argv[1]))' "$REPO_ROOT")
MAX_ITERS=${MAX_ITERS:-10}
AUTO_AGENT=${AUTO_AGENT:-1}
MAX_PARALLEL=${MAX_PARALLEL:-3}
AGENT_BACKEND=${AGENT_BACKEND:-claude}
PROVE_BUDGET=${PROVE_BUDGET:-3600}   # global time budget in seconds, 0 = unlimited
START_TIME=$(date +%s)
LOG_DIR="$REPO_ROOT/theme/out/logs"
mkdir -p "$LOG_DIR"

# --- List PIPELINE_ID markers in Statlean/ ---
list_pipeline_ids() {
  if command -v rg >/dev/null 2>&1; then
    (rg -o "PIPELINE_ID:[[:space:]]*[^[:space:]]+" "$REPO_ROOT/Statlean/" -t lean 2>/dev/null || true)
  else
    (grep -roE "PIPELINE_ID:[[:space:]]*[^[:space:]]+" "$REPO_ROOT/Statlean/" --include='*.lean' 2>/dev/null || true)
  fi | sed -E 's/^.*PIPELINE_ID:[[:space:]]*//' | awk 'NF && !seen[$0]++'
}

count_pipeline_ids() {
  list_pipeline_ids | wc -l | tr -d ' '
}

# --- Count sorry in Statlean/ ---
count_sorry() {
  if command -v rg >/dev/null 2>&1; then
    rg -c '\bsorry\b' "$REPO_ROOT/Statlean/" -t lean 2>/dev/null | \
      awk -F: '{s+=$NF} END {print s+0}'
  else
    grep -roE '\bsorry\b' "$REPO_ROOT/Statlean/" --include='*.lean' 2>/dev/null | wc -l | tr -d ' '
  fi
}

# --- Generate prompt for a sorry target ---
generate_sorry_prompt() {
  local file="$1"
  local theorem="$2"
  local prompt_file="$3"

  # Build module name for incremental compile
  local module_name
  module_name=$(echo "$file" | sed 's|Statlean/||;s|/|.|g;s|\.lean||')

  # Extract backlog context for this sorry (proof sketch, blocker, previous attempts)
  local backlog_context
  backlog_context=$(python3 -c "
import yaml, json, sys
try:
    data = yaml.safe_load(open('$REPO_ROOT/theme/input/sorry_backlog.yaml'))
    for it in (data.get('sorry_items') or []):
        if it.get('theorem') == '$theorem' and it.get('file') == '$file':
            print(json.dumps(it, indent=2, ensure_ascii=False))
            break
    else:
        print('(no backlog entry found)')
except Exception as e:
    print(f'(backlog read error: {e})')
" 2>&1)

  # Playbook is injected directly into prompt (guaranteed to be seen)
  local playbook="$REPO_ROOT/theme/prove_playbook.md"

  cat > "$prompt_file" <<PROMPT
$(if [ -f "$playbook" ]; then cat "$playbook"; else echo "(prove_playbook.md not found — use standard approach)"; fi)

================================================================
TARGET
================================================================

File: $file
Theorem: $theorem
Module: Statlean.$module_name
Workspace: $REPO_ROOT

Backlog context:
$backlog_context

================================================================
EXECUTION
================================================================

1. Read the target file, locate theorem $theorem
2. Follow the playbook above: strategy selection → API search → write proof → compile → fix
3. Verify: cd $REPO_ROOT && lake build Statlean.$module_name
4. Focus ONLY on theorem $theorem — do NOT modify other declarations
5. Each sub-lemma proved → immediately write to file and lake build verify

Acceptance:
- sorry is eliminated from theorem $theorem
- Incremental build passes (lake build Statlean.$module_name)
PROMPT
}

# --- Run a single Claude agent ---
run_claude_agent() {
  local prompt_file="$1"
  local fix_log="$2"
  local agent_timeout="$3"

  local run_agent_cmd=(
    env -u CLAUDECODE claude --dangerously-skip-permissions
      --verbose
      -p "$(cat "$prompt_file")"
  )

  if command -v timeout >/dev/null 2>&1; then
    timeout --kill-after=30s "${agent_timeout}s" "${run_agent_cmd[@]}" > "$fix_log" 2>&1
  else
    "${run_agent_cmd[@]}" > "$fix_log" 2>&1
  fi
}

# --- Run a single Codex agent ---
run_codex_agent() {
  local prompt_file="$1"
  local fix_log="$2"
  local agent_timeout="$3"

  local run_agent_cmd=(
    codex exec --full-auto "$(cat "$prompt_file")"
  )

  if command -v timeout >/dev/null 2>&1; then
    timeout --kill-after=30s "${agent_timeout}s" "${run_agent_cmd[@]}" > "$fix_log" 2>&1
  else
    "${run_agent_cmd[@]}" > "$fix_log" 2>&1
  fi
}

# --- Dispatch to the configured backend ---
run_agent() {
  case "$AGENT_BACKEND" in
    claude)
      run_claude_agent "$@"
      ;;
    codex)
      run_codex_agent "$@"
      ;;
    *)
      echo "[prove-loop] ERROR: unknown AGENT_BACKEND='$AGENT_BACKEND' (valid: claude, codex)" >&2
      exit 1
      ;;
  esac
}

# --- Select targets from backlog ---
select_targets() {
  python3 -c "
import yaml, json, sys, os
with open('$REPO_ROOT/theme/input/sorry_backlog.yaml') as f:
    data = yaml.safe_load(f) or {}

manifest_path = os.environ.get('MANIFEST', '')
manifest_files = None
if manifest_path and os.path.isfile(manifest_path):
    try:
        with open(manifest_path) as mf:
            manifest = json.load(mf)
        manifest_files = {e['file'] for e in manifest.get('entries', {}).values() if 'file' in e}
        print(f'[prove-loop] pipeline mode: targeting {len(manifest_files)} files from manifest', file=sys.stderr)
        for f_name in sorted(manifest_files):
            print(f'  - {f_name}', file=sys.stderr)
    except (json.JSONDecodeError, KeyError) as exc:
        print(f'[prove-loop] manifest parse error ({exc}), falling back to full backlog', file=sys.stderr)
        manifest_files = None
else:
    print('[prove-loop] standalone mode: targeting full backlog by priority', file=sys.stderr)

items = [it for it in (data.get('sorry_items') or [])
         if it.get('type') not in ('blocked',)]
if manifest_files is not None:
    items = [it for it in items if it.get('file','') in manifest_files]
items.sort(key=lambda x: x.get('priority', 99))
targets = items[:$MAX_PARALLEL]
print(len(targets))
for it in targets:
    print(json.dumps({'file': it['file'], 'theorem': it['theorem']}))
"
}

# === Main loop ===
echo "[prove-loop] fallback mode — backend=$AGENT_BACKEND, working on Statlean/ files directly"
prev_sorry_count=$(count_sorry)
echo "[prove-loop] sorry count: $prev_sorry_count, pipeline IDs: $(count_pipeline_ids)"

for i in $(seq 1 "$MAX_ITERS"); do
  LOG="$LOG_DIR/build_iter_${i}.log"

  # Global time budget check
  elapsed=$(( $(date +%s) - START_TIME ))
  if [[ "$PROVE_BUDGET" -gt 0 && "$elapsed" -ge "$PROVE_BUDGET" ]]; then
    echo "[prove-loop] time budget exhausted (${elapsed}s >= ${PROVE_BUDGET}s)"
    break
  fi

  remaining=$(( PROVE_BUDGET - elapsed ))
  echo "[prove-loop] iteration $i/$MAX_ITERS (elapsed=${elapsed}s, remaining=${remaining}s)"

  # Build check
  build_ok=0
  if (cd "$REPO_ROOT" && lake build) > "$LOG" 2>&1; then
    build_ok=1
  fi

  sorry_count=$(count_sorry)
  pipeline_count=$(count_pipeline_ids)

  if [[ "$build_ok" -eq 1 && "$pipeline_count" -eq 0 ]]; then
    echo "[prove-loop] build ok, no PIPELINE_ID markers remain. sorry=$sorry_count"
    echo "{\"phase\":\"prove-loop\",\"iter\":$i,\"status\":\"ok\",\"sorry\":$sorry_count}" >> "$LOG_DIR/pipeline.jsonl"
    break
  fi

  echo "[prove-loop] build_ok=$build_ok sorry=$sorry_count pipeline_ids=$pipeline_count"
  echo "{\"phase\":\"prove-loop\",\"iter\":$i,\"build_ok\":$build_ok,\"sorry\":$sorry_count,\"pipeline_ids\":$pipeline_count}" >> "$LOG_DIR/pipeline.jsonl"

  # Guard: do not dispatch agents if build is broken
  if [[ "$build_ok" -eq 0 ]]; then
    echo "[prove-loop] ERROR: build failed — cannot dispatch prove agents on broken code"
    echo "[prove-loop] fix build errors first, then re-run prove"
    break
  fi

  # Progress check: if sorry count didn't decrease since last iteration,
  # nothing changed — retrying the same targets with the same prompt is pointless
  if [[ "$i" -gt 1 && "$sorry_count" -ge "$prev_sorry_count" ]]; then
    echo "[prove-loop] no progress (sorry: $prev_sorry_count → $sorry_count) — stopping"
    break
  fi
  prev_sorry_count=$sorry_count

  if [[ "$i" -eq "$MAX_ITERS" ]]; then
    echo "[prove-loop] reached max iterations ($MAX_ITERS)"
    break
  fi

  if [[ "$AUTO_AGENT" != "1" ]]; then
    echo "[prove-loop] AUTO_AGENT=0, stopping"
    break
  fi

  # Check that the configured backend CLI is available
  case "$AGENT_BACKEND" in
    claude)
      if ! command -v claude >/dev/null 2>&1; then
        echo "[prove-loop] claude CLI not found; cannot auto-fix (AGENT_BACKEND=claude)" >&2
        exit 1
      fi
      ;;
    codex)
      if ! command -v codex >/dev/null 2>&1; then
        echo "[prove-loop] codex CLI not found; cannot auto-fix (AGENT_BACKEND=codex)" >&2
        exit 1
      fi
      ;;
    *)
      echo "[prove-loop] ERROR: unknown AGENT_BACKEND='$AGENT_BACKEND' (valid: claude, codex)" >&2
      exit 1
      ;;
  esac

  # Sync backlog and select targets
  echo "[prove-loop] syncing backlog and dispatching agents..."
  (cd "$REPO_ROOT" && python3 theme/scripts/sync_sorry_backlog.py) || true

  # Read targets into array
  target_count=0
  targets=()
  while IFS= read -r line; do
    # Pass through stderr log lines (start with [)
    if [[ "$line" == "["* ]]; then
      echo "$line"
      continue
    fi
    # First numeric line is target count
    if [[ "$target_count" -eq 0 && "$line" =~ ^[0-9]+$ ]]; then
      target_count=$line
      continue
    fi
    targets+=("$line")
  done < <(select_targets)

  if [[ "$target_count" -eq 0 || "${#targets[@]}" -eq 0 ]]; then
    echo "[prove-loop] no actionable targets — stopping"
    break
  fi

  # Dispatch agents: each gets remaining_budget / target_count (min 120s)
  for line in "${targets[@]}"; do
    file=$(echo "$line" | python3 -c "import json,sys; print(json.load(sys.stdin)['file'])")
    theorem=$(echo "$line" | python3 -c "import json,sys; print(json.load(sys.stdin)['theorem'])")
    prompt_file="$LOG_DIR/fix_prompt_${i}_${theorem}.txt"
    fix_log="$LOG_DIR/fix_${i}_${theorem}.log"

    generate_sorry_prompt "$file" "$theorem" "$prompt_file"

    # Dynamic per-agent timeout: remaining_budget / target_count
    agent_elapsed=$(( $(date +%s) - START_TIME ))
    agent_remaining=$(( PROVE_BUDGET - agent_elapsed ))
    if [[ "$PROVE_BUDGET" -gt 0 && "$agent_remaining" -le 0 ]]; then
      echo "[prove-loop] time budget exhausted before agent dispatch"
      break 2
    fi
    effective_timeout=$(( agent_remaining / target_count ))
    # Floor: at least 120s per agent
    if [[ "$effective_timeout" -lt 120 ]]; then
      effective_timeout=120
    fi
    # Cap: no more than remaining budget
    if [[ "$PROVE_BUDGET" -gt 0 && "$effective_timeout" -gt "$agent_remaining" ]]; then
      effective_timeout="$agent_remaining"
    fi

    echo "[prove-loop] attacking $file:$theorem (backend=$AGENT_BACKEND, timeout=${effective_timeout}s, targets=$target_count)"
    if run_agent "$prompt_file" "$fix_log" "$effective_timeout"; then
      echo "[prove-loop] agent for $theorem completed successfully"
    else
      rc=$?
      echo "[prove-loop] agent for $theorem exited with rc=$rc"
    fi
  done
done

echo "[prove-loop] done. Final sorry count: $(count_sorry)"
