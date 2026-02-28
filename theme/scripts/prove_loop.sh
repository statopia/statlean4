#!/usr/bin/env bash
# Lightweight fallback prove loop — for CI / non-Claude-Code environments.
# Primary prove path is /prove-deep (DAG scheduler inside Claude Code).
set -euo pipefail

REPO_ROOT=${1:?usage: prove_loop.sh <repo_root>}
REPO_ROOT=$(python3 -c 'import os,sys; print(os.path.abspath(sys.argv[1]))' "$REPO_ROOT")
MAX_ITERS=${MAX_ITERS:-3}
AUTO_AGENT=${AUTO_AGENT:-1}
AGENT_TIMEOUT_SECONDS=${AGENT_TIMEOUT_SECONDS:-600}
MAX_PARALLEL=${MAX_PARALLEL:-3}
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
  cat > "$prompt_file" <<PROMPT
You are proving a Lean 4 theorem in a statistics library.
Workspace root: $REPO_ROOT

Target: $file — theorem $theorem

Tasks:
1) Open the file and find the sorry in theorem $theorem
2) Search for API — three-level strategy:
   Level 1: Read theme/mathlib_api_index.md (pre-built index of ~650 Mathlib APIs)
   Level 2: Use #check / exact? for precise lookup
   Level 3: grep Mathlib source as last resort
3) Write a proof replacing sorry.
4) Verify: cd $REPO_ROOT && lake build Statlean.$(echo "$file" | sed 's|Statlean/||;s|/|.|g;s|\.lean||')

Focus ONLY on this theorem. Do NOT modify other declarations.

Acceptance:
- sorry is eliminated from theorem $theorem
- Incremental build passes
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

# === Main loop ===
echo "[prove-loop] fallback mode — working on Statlean/ files directly"
echo "[prove-loop] sorry count: $(count_sorry), pipeline IDs: $(count_pipeline_ids)"

for i in $(seq 1 "$MAX_ITERS"); do
  LOG="$LOG_DIR/build_iter_${i}.log"

  echo "[prove-loop] iteration $i/$MAX_ITERS"

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

  if [[ "$i" -eq "$MAX_ITERS" ]]; then
    echo "[prove-loop] reached max iterations" >&2
    exit 1
  fi

  if [[ "$AUTO_AGENT" != "1" ]]; then
    echo "[prove-loop] AUTO_AGENT=0, stopping" >&2
    exit 1
  fi

  if ! command -v claude >/dev/null 2>&1; then
    echo "[prove-loop] claude CLI not found; cannot auto-fix" >&2
    exit 1
  fi

  # Use sync_sorry_backlog.py to get targets, then attack via claude agents
  echo "[prove-loop] syncing backlog and dispatching agents..."
  (cd "$REPO_ROOT" && python3 theme/scripts/sync_sorry_backlog.py) || true

  # Simple sequential attack: read backlog, attack first N by priority
  python3 -c "
import yaml, json, sys
with open('$REPO_ROOT/theme/input/sorry_backlog.yaml') as f:
    data = yaml.safe_load(f) or {}
items = [it for it in (data.get('sorry_items') or [])
         if it.get('type') not in ('blocked',)]
items.sort(key=lambda x: x.get('priority', 99))
for it in items[:$MAX_PARALLEL]:
    print(json.dumps({'file': it['file'], 'theorem': it['theorem']}))
" | while IFS= read -r line; do
    file=$(echo "$line" | python3 -c "import json,sys; print(json.load(sys.stdin)['file'])")
    theorem=$(echo "$line" | python3 -c "import json,sys; print(json.load(sys.stdin)['theorem'])")
    prompt_file="$LOG_DIR/fix_prompt_${i}_${theorem}.txt"
    fix_log="$LOG_DIR/fix_${i}_${theorem}.log"

    generate_sorry_prompt "$file" "$theorem" "$prompt_file"
    echo "[prove-loop] attacking $file:$theorem"
    run_claude_agent "$prompt_file" "$fix_log" "$AGENT_TIMEOUT_SECONDS" || \
      echo "[prove-loop] agent for $theorem exited with rc=$?"
  done
done

echo "[prove-loop] done. Final sorry count: $(count_sorry)"
