#!/usr/bin/env bash
# Gate check: full project build + sorry count + PIPELINE_ID check
set -euo pipefail

REPO_ROOT=${1:?usage: gate.sh <repo_root>}
REPO_ROOT=$(python3 -c 'import os,sys; print(os.path.abspath(sys.argv[1]))' "$REPO_ROOT")
LOG_DIR="$REPO_ROOT/theme/out/logs"
mkdir -p "$LOG_DIR"

echo "[gate] checking $REPO_ROOT"

# Gate 1: full project build
echo "[gate] running lake build..."
if ! (cd "$REPO_ROOT" && lake build) > "$LOG_DIR/gate_build.log" 2>&1; then
  echo "[gate] FAIL: lake build failed. See $LOG_DIR/gate_build.log" >&2
  exit 1
fi
echo "[gate] build: PASS"

# Gate 2: sorry count (informational, not blocking)
sorry_count=$(grep -roE '\bsorry\b' "$REPO_ROOT/Statlean/" --include='*.lean' 2>/dev/null | wc -l | tr -d ' ' || true)
sorry_count=${sorry_count:-0}
echo "[gate] sorry count: $sorry_count"
if [[ "$sorry_count" -gt 0 ]]; then
  echo "[gate] WARNING: $sorry_count sorry remaining — consider /prove-deep to continue"
fi

# Gate 3: PIPELINE_ID check (unresolved pipeline markers)
STRICT_PIPELINE=${STRICT_PIPELINE:-0}
pipeline_count=$(grep -roE 'PIPELINE_ID:' "$REPO_ROOT/Statlean/" --include='*.lean' 2>/dev/null | wc -l | tr -d ' ' || true)
pipeline_count=${pipeline_count:-0}
echo "[gate] PIPELINE_ID markers: $pipeline_count"

if [[ "$STRICT_PIPELINE" == "1" && "$pipeline_count" -gt 0 ]]; then
  echo "[gate] FAIL: unresolved PIPELINE_ID markers (STRICT_PIPELINE=1)" >&2
  exit 1
fi

# Report
echo "{\"phase\":\"gate\",\"status\":\"ok\",\"sorry\":$sorry_count,\"pipeline_ids\":$pipeline_count}" >> "$LOG_DIR/pipeline.jsonl"
echo "[gate] all checks passed (sorry=$sorry_count, pipeline_ids=$pipeline_count)"
