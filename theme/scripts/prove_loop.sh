#!/usr/bin/env bash
set -euo pipefail

OUT_DIR=${1:?usage: prove_loop.sh <out_dir> <repo_root>}
REPO_ROOT=${2:?usage: prove_loop.sh <out_dir> <repo_root>}
OUT_DIR=$(python3 -c 'import os,sys; print(os.path.abspath(sys.argv[1]))' "$OUT_DIR")
REPO_ROOT=$(python3 -c 'import os,sys; print(os.path.abspath(sys.argv[1]))' "$REPO_ROOT")
MAX_ITERS=${MAX_ITERS:-3}
AUTO_AGENT=${AUTO_AGENT:-1}
STRICT_TRANSLATION=${STRICT_TRANSLATION:-1}
AGENT_TIMEOUT_SECONDS=${AGENT_TIMEOUT_SECONDS:-600}
BATCH_SIZE=${BATCH_SIZE:-3}
# Agent backend: "codex" (default) or "claude"
AGENT_BACKEND=${AGENT_BACKEND:-codex}
TARGET_FILE="$OUT_DIR/generated/Generated.lean"
TARGET_DIR="$OUT_DIR/generated"

mkdir -p "$OUT_DIR/logs"

list_unresolved_ids() {
  if [[ ! -f "$TARGET_FILE" ]]; then
    return
  fi
  if command -v rg >/dev/null 2>&1; then
    (rg -o "TODO_TRANSLATE_ID:[[:space:]]*[^[:space:]]+" "$TARGET_FILE" 2>/dev/null || true)
  else
    (grep -oE "TODO_TRANSLATE_ID:[[:space:]]*[^[:space:]]+" "$TARGET_FILE" 2>/dev/null || true)
  fi | sed -E 's/^TODO_TRANSLATE_ID:[[:space:]]*//' | awk 'NF && !seen[$0]++'
}

sync_generated_metadata() {
  local unresolved_file="$OUT_DIR/generated/unresolved_ids.txt"
  local manifest_file="$OUT_DIR/generated/manifest.json"
  mapfile -t current_ids < <(list_unresolved_ids)

  : > "$unresolved_file"
  for id in "${current_ids[@]}"; do
    echo "$id" >> "$unresolved_file"
  done

  if [[ -f "$manifest_file" ]]; then
    python3 - "$manifest_file" <<'PY'
import json
import re
import sys

manifest_path = sys.argv[1]
with open(manifest_path, "r", encoding="utf-8") as f:
    data = json.load(f)

target = data.get("compile_target", "")
ids = []
if target:
    try:
        with open(target, "r", encoding="utf-8") as tf:
            for line in tf:
                m = re.search(r"TODO_TRANSLATE_ID:\s*([^\s]+)", line)
                if not m:
                    continue
                theorem_id = m.group(1)
                if theorem_id not in ids:
                    ids.append(theorem_id)
    except FileNotFoundError:
        pass

data["unresolved_count"] = len(ids)
data["unresolved_ids"] = ids

with open(manifest_path, "w", encoding="utf-8") as f:
    json.dump(data, f, indent=2, ensure_ascii=False)
    f.write("\n")
PY
  fi
}

count_unresolved() {
  if [[ ! -d "$TARGET_DIR" ]]; then
    echo 0
    return
  fi
  list_unresolved_ids | wc -l | tr -d ' '
}

for i in $(seq 1 "$MAX_ITERS"); do
  LOG="$OUT_DIR/logs/build_iter_${i}.log"
  FIX_LOG="$OUT_DIR/logs/fix_iter_${i}.log"

  echo "[prove-loop] iteration $i/$MAX_ITERS"
  build_ok=0
  if (cd "$REPO_ROOT" && lake env lean "$TARGET_FILE") > "$LOG" 2>&1; then
    build_ok=1
  fi

  unresolved_count=$(count_unresolved)
  sync_generated_metadata
  mapfile -t unresolved_ids < <(list_unresolved_ids)
  effective_batch_size=$BATCH_SIZE
  if ! [[ "$effective_batch_size" =~ ^[0-9]+$ ]] || [[ "$effective_batch_size" -lt 1 ]]; then
    effective_batch_size=1
  fi
  batch_ids=()
  if [[ "${#unresolved_ids[@]}" -gt 0 ]]; then
    batch_offset=$(( (i - 1) * effective_batch_size ))
    if (( batch_offset >= ${#unresolved_ids[@]} )); then
      batch_offset=$(( batch_offset % ${#unresolved_ids[@]} ))
    fi
    batch_ids=("${unresolved_ids[@]:batch_offset:effective_batch_size}")
    if [[ "${#batch_ids[@]}" -eq 0 ]]; then
      batch_ids=("${unresolved_ids[@]}")
    fi
  fi

  if [[ "$build_ok" -eq 1 ]]; then
    if [[ "$STRICT_TRANSLATION" != "1" || "$unresolved_count" -eq 0 ]]; then
      echo "{\"phase\":\"prove-loop\",\"iter\":$i,\"status\":\"build-ok\",\"unresolved\":$unresolved_count}" >> "$OUT_DIR/logs/pipeline.jsonl"
      echo "[prove-loop] build succeeded"
      break
    fi
    echo "{\"phase\":\"prove-loop\",\"iter\":$i,\"status\":\"build-ok-unresolved\",\"unresolved\":$unresolved_count}" >> "$OUT_DIR/logs/pipeline.jsonl"
    echo "[prove-loop] build ok but unresolved translations remain: $unresolved_count"
  else
    echo "{\"phase\":\"prove-loop\",\"iter\":$i,\"status\":\"build-fail\",\"log\":\"$LOG\",\"unresolved\":$unresolved_count}" >> "$OUT_DIR/logs/pipeline.jsonl"
  fi

  if [[ "$i" -eq "$MAX_ITERS" ]]; then
    echo "[prove-loop] reached max iterations without full closure" >&2
    exit 1
  fi

  if [[ "$AUTO_AGENT" != "1" ]]; then
    echo "[prove-loop] AUTO_AGENT=0, stopping before automatic fixing" >&2
    exit 1
  fi

  # --- Check agent availability ---
  case "$AGENT_BACKEND" in
    claude)
      if ! command -v claude >/dev/null 2>&1; then
        echo "[prove-loop] claude CLI not found; cannot auto-fix" >&2
        exit 1
      fi
      ;;
    codex)
      if ! command -v codex >/dev/null 2>&1; then
        echo "[prove-loop] codex CLI not found; cannot auto-fix" >&2
        exit 1
      fi
      ;;
    *)
      echo "[prove-loop] unknown AGENT_BACKEND=$AGENT_BACKEND (expected: codex or claude)" >&2
      exit 1
      ;;
  esac

  BATCH_IDS_FILE="$OUT_DIR/logs/fix_batch_ids_${i}.txt"
  : > "$BATCH_IDS_FILE"
  BATCH_IDS_BULLETS=""
  if [[ "${#batch_ids[@]}" -eq 0 ]]; then
    BATCH_IDS_BULLETS="- (none)"
  else
    for id in "${batch_ids[@]}"; do
      echo "$id" >> "$BATCH_IDS_FILE"
      BATCH_IDS_BULLETS+="- $id"$'\n'
    done
    BATCH_IDS_BULLETS=${BATCH_IDS_BULLETS%$'\n'}
  fi
  echo "{\"phase\":\"prove-loop\",\"iter\":$i,\"status\":\"agent-batch\",\"agent\":\"$AGENT_BACKEND\",\"batch_size\":$effective_batch_size,\"batch_count\":${#batch_ids[@]},\"batch_ids_file\":\"$BATCH_IDS_FILE\",\"unresolved_before\":$unresolved_count}" >> "$OUT_DIR/logs/pipeline.jsonl"
  echo "[prove-loop] agent=$AGENT_BACKEND batch_size=$effective_batch_size, batch_count=${#batch_ids[@]}"

  PROMPT_FILE="$OUT_DIR/logs/fix_prompt_${i}.txt"
  cat > "$PROMPT_FILE" <<PROMPT
You are fixing a generated Lean 4 project that formalizes mathematical theorems from LaTeX.
Workspace root: $REPO_ROOT
Target file: $TARGET_FILE

Tasks:
1) Open $TARGET_FILE and inspect unresolved TODO_TRANSLATE_ID markers.
2) In this iteration, prioritize these IDs first:
$BATCH_IDS_BULLETS
3) For each unresolved ID:
   a) Read the LaTeX statement and proof hint in the docstring comment above the declaration.
   b) Search the project (Statlean/) and Mathlib (.lake/packages/mathlib/) for similar theorems and useful API.
   c) Replace the placeholder statement with a correct Lean 4 type-checked statement.
   d) Write a proof (prefer sorry-free; if infeasible, use sorry with a comment explaining what's missing).
4) Keep theorems axiom-free. Prefer using existing Mathlib/Statlean lemmas.
5) After all edits, verify: cd $REPO_ROOT && lake env lean $TARGET_FILE
6) If a full proof is infeasible, refactor statement assumptions explicitly so the theorem stays logically honest and compilable.

Acceptance:
- All prioritized IDs above are resolved (TODO_TRANSLATE_ID markers removed)
- Build passes with lake env lean on target file
- You may resolve additional TODO IDs beyond this batch
PROMPT

  # --- Invoke agent ---
  echo "[prove-loop] invoking $AGENT_BACKEND auto-fix (iter $i)"

  case "$AGENT_BACKEND" in
    claude)
      run_agent_cmd=(
        claude --dangerously-skip-permissions
          --verbose
          -p "$(cat "$PROMPT_FILE")"
      )
      ;;
    codex)
      run_agent_cmd=(
        codex exec --full-auto -C "$REPO_ROOT" "$(cat "$PROMPT_FILE")"
      )
      ;;
  esac

  agent_rc=0
  if command -v timeout >/dev/null 2>&1; then
    if timeout --kill-after=30s "${AGENT_TIMEOUT_SECONDS}s" "${run_agent_cmd[@]}" > "$FIX_LOG" 2>&1; then
      agent_rc=0
    else
      agent_rc=$?
    fi
  else
    if "${run_agent_cmd[@]}" > "$FIX_LOG" 2>&1; then
      agent_rc=0
    else
      agent_rc=$?
    fi
  fi

  if [[ "$agent_rc" -eq 0 ]]; then
    unresolved_after=$(count_unresolved)
    echo "{\"phase\":\"prove-loop\",\"iter\":$i,\"status\":\"agent-ran\",\"agent\":\"$AGENT_BACKEND\",\"fix_log\":\"$FIX_LOG\",\"unresolved_after\":$unresolved_after}" >> "$OUT_DIR/logs/pipeline.jsonl"
    echo "[prove-loop] $AGENT_BACKEND completed; unresolved now: $unresolved_after"
  else
    if [[ "$agent_rc" -eq 124 ]]; then
      echo "{\"phase\":\"prove-loop\",\"iter\":$i,\"status\":\"agent-timeout\",\"agent\":\"$AGENT_BACKEND\",\"timeout_seconds\":$AGENT_TIMEOUT_SECONDS,\"fix_log\":\"$FIX_LOG\"}" >> "$OUT_DIR/logs/pipeline.jsonl"
      unresolved_after_timeout=$(count_unresolved)
      echo "[prove-loop] $AGENT_BACKEND auto-fix timed out after ${AGENT_TIMEOUT_SECONDS}s; unresolved now: $unresolved_after_timeout; see $FIX_LOG" >&2
      continue
    fi
    echo "{\"phase\":\"prove-loop\",\"iter\":$i,\"status\":\"agent-failed\",\"agent\":\"$AGENT_BACKEND\",\"fix_log\":\"$FIX_LOG\"}" >> "$OUT_DIR/logs/pipeline.jsonl"
    # Backend-specific error detection
    if [[ "$AGENT_BACKEND" == "codex" ]]; then
      if grep -qE "stream disconnected before completion|error sending request for url|Failed to shutdown rollout recorder" "$FIX_LOG"; then
        echo "[prove-loop] codex backend/network failure detected; see $FIX_LOG" >&2
        exit 2
      fi
      if grep -qE "mcp startup: failed" "$FIX_LOG"; then
        echo "[prove-loop] codex MCP startup failure detected; see $FIX_LOG" >&2
        exit 2
      fi
    elif [[ "$AGENT_BACKEND" == "claude" ]]; then
      if grep -qE "connection refused|ECONNREFUSED|rate.limit|overloaded" "$FIX_LOG"; then
        echo "[prove-loop] claude backend/network failure detected; see $FIX_LOG" >&2
        exit 2
      fi
    fi
  fi
done
