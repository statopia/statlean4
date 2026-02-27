#!/usr/bin/env bash
set -euo pipefail

OUT_DIR=${1:?usage: stabilize.sh <out_dir> <repo_root>}
REPO_ROOT=${2:?usage: stabilize.sh <out_dir> <repo_root>}
OUT_DIR=$(python3 -c 'import os,sys; print(os.path.abspath(sys.argv[1]))' "$OUT_DIR")
REPO_ROOT=$(python3 -c 'import os,sys; print(os.path.abspath(sys.argv[1]))' "$REPO_ROOT")

APPLY_STABILIZE=${APPLY_STABILIZE:-1}
STABILIZE_MIN_STABLE_RUNS=${STABILIZE_MIN_STABLE_RUNS:-2}
STABILIZE_STATS_ONLY=${STABILIZE_STATS_ONLY:-1}
STABILIZE_MATHLIB_CHECK=${STABILIZE_MATHLIB_CHECK:-1}

mkdir -p "$OUT_DIR/logs" "$OUT_DIR/stabilized"

if [[ "$APPLY_STABILIZE" != "1" ]]; then
  echo "{\"phase\":\"stabilize\",\"status\":\"skipped\",\"reason\":\"APPLY_STABILIZE!=1\"}" >> "$OUT_DIR/logs/pipeline.jsonl"
  echo "[stabilize] skipped"
  exit 0
fi

# Look for candidate from promote step, fall back to legacy AutoPromoted.lean
AUTOPROMOTED="$OUT_DIR/promoted/AutoPromoted.candidate.lean"
if [[ ! -f "$AUTOPROMOTED" ]]; then
  AUTOPROMOTED="$REPO_ROOT/Statlean/AutoPromoted.lean"
fi
if [[ ! -f "$AUTOPROMOTED" ]]; then
  echo "{\"phase\":\"stabilize\",\"status\":\"skipped\",\"reason\":\"no-candidate\",\"searched\":\"$OUT_DIR/promoted/AutoPromoted.candidate.lean,$REPO_ROOT/Statlean/AutoPromoted.lean\"}" >> "$OUT_DIR/logs/pipeline.jsonl"
  echo "[stabilize] skipped (no candidate file found)"
  exit 0
fi

STATE_JSON="$OUT_DIR/stabilized/stability_state.json"
SUMMARY_JSON="$OUT_DIR/stabilized/stabilize_summary.json"

python3 "$(dirname "$0")/stabilize_promoted.py" \
  --repo-root "$REPO_ROOT" \
  --autopromoted "$AUTOPROMOTED" \
  --state-json "$STATE_JSON" \
  --summary-json "$SUMMARY_JSON" \
  --min-stable-runs "$STABILIZE_MIN_STABLE_RUNS" \
  --stats-only "$STABILIZE_STATS_ONLY" \
  --mathlib-check "$STABILIZE_MATHLIB_CHECK" > "$OUT_DIR/logs/stabilize.log"

MIGRATED_COUNT=$(python3 - <<PY
import json
from pathlib import Path
obj = json.loads(Path("$SUMMARY_JSON").read_text(encoding="utf-8"))
print(int(obj.get("migrated_count", 0)))
PY
)

if [[ "$MIGRATED_COUNT" -gt 0 ]]; then
  # Build all modules touched by stabilization, then the root library.
  while IFS= read -r mod; do
    [[ -z "$mod" ]] && continue
    rel_mod=$(python3 - <<PY
from pathlib import Path
p = Path("$mod").resolve()
print(p.relative_to(Path("$REPO_ROOT").resolve()))
PY
)
    (cd "$REPO_ROOT" && lake env lean "$rel_mod") >> "$OUT_DIR/logs/stabilize_build.log" 2>&1
  done < <(python3 - <<PY
import json
from pathlib import Path
obj = json.loads(Path("$SUMMARY_JSON").read_text(encoding="utf-8"))
for p in obj.get("written_modules", []):
    print(p)
PY
)
fi

(cd "$REPO_ROOT" && lake build Statlean) > "$OUT_DIR/logs/stabilize_root_build.log" 2>&1

echo "{\"phase\":\"stabilize\",\"status\":\"ok\",\"summary\":\"$SUMMARY_JSON\",\"migrated_count\":$MIGRATED_COUNT}" >> "$OUT_DIR/logs/pipeline.jsonl"
echo "[stabilize] summary=$SUMMARY_JSON migrated_count=$MIGRATED_COUNT"
