#!/usr/bin/env bash
set -euo pipefail

OUT_DIR=${1:?usage: promote.sh <out_dir> <repo_root>}
REPO_ROOT=${2:?usage: promote.sh <out_dir> <repo_root>}
OUT_DIR=$(python3 -c 'import os,sys; print(os.path.abspath(sys.argv[1]))' "$OUT_DIR")
REPO_ROOT=$(python3 -c 'import os,sys; print(os.path.abspath(sys.argv[1]))' "$REPO_ROOT")

MIN_FANIN=${PROMOTE_MIN_FANIN:-2}
PROMOTE_ALL_NOVEL=${PROMOTE_ALL_NOVEL:-1}
APPLY_PROMOTION=${APPLY_PROMOTION:-0}
IMPORT_AUTOPROMOTED=${IMPORT_AUTOPROMOTED:-0}

mkdir -p "$OUT_DIR/logs" "$OUT_DIR/promoted"
REPORT="$OUT_DIR/reuse_report.txt"
PROMOTE_JSON="$OUT_DIR/promoted/promote_report.json"
PROMOTED_YAML="$OUT_DIR/promoted/theorems.promoted.yaml"
SRC_YAML="$OUT_DIR/input_snapshot/theorems.yaml"

if [[ ! -f "$SRC_YAML" ]]; then
  SRC_YAML="$REPO_ROOT/theme/input/theorems.yaml"
fi

PROMOTE_NOVEL_FLAG=""
if [[ "$PROMOTE_ALL_NOVEL" == "1" ]]; then
  PROMOTE_NOVEL_FLAG="--promote-all-novel --repo-root $REPO_ROOT"
fi

python3 "$(dirname "$0")/promote_layers.py" \
  --in-yaml "$SRC_YAML" \
  --out-yaml "$PROMOTED_YAML" \
  --report-json "$PROMOTE_JSON" \
  --min-fanin "$MIN_FANIN" $PROMOTE_NOVEL_FLAG > "$OUT_DIR/logs/promote_layers.log"

PROMOTED_COUNT=$(python3 - <<PY
import json
from pathlib import Path
p = Path("$PROMOTE_JSON")
obj = json.loads(p.read_text(encoding="utf-8"))
print(int(obj.get("promoted_count", 0)))
PY
)

{
  echo "Statlib Promotion Report"
  echo "repo_root=$REPO_ROOT"
  echo "source_yaml=$SRC_YAML"
  echo "promoted_yaml=$PROMOTED_YAML"
  echo "min_fanin=$MIN_FANIN"
  echo "promoted_count=$PROMOTED_COUNT"
  echo
  echo "Promoted IDs (if any):"
  python3 - <<PY
import json
from pathlib import Path
obj = json.loads(Path("$PROMOTE_JSON").read_text(encoding="utf-8"))
for it in obj.get("promoted", []):
    print(f"- {it['id']} (fanin={it['fanin']})")
PY
  echo
  echo "Heuristic candidates in existing project-layer files:"
  if command -v rg >/dev/null 2>&1; then
    rg -n "Compatibility wrapper|structured wrapper|bridge" "$REPO_ROOT/Statlean" || true
  else
    grep -RInE "Compatibility wrapper|structured wrapper|bridge" "$REPO_ROOT/Statlean" || true
  fi
} > "$REPORT"

if [[ "$APPLY_PROMOTION" == "1" && "$PROMOTED_COUNT" -gt 0 ]]; then
  echo "[promote] applying promotion and running regression build"
  python3 "$(dirname "$0")/generate_project.py" \
    --input-dir "$OUT_DIR/input_snapshot" \
    --out-dir "$OUT_DIR/promoted" \
    --repo-root "$REPO_ROOT" \
    --theorems-file "$PROMOTED_YAML" > "$OUT_DIR/logs/promoted_generate.log"

  if (cd "$REPO_ROOT" && lake env lean "$OUT_DIR/promoted/generated/Generated.lean") > "$OUT_DIR/logs/promoted_build.log" 2>&1; then
    STATLIB_MODULE="$OUT_DIR/promoted/AutoPromoted.candidate.lean"
    STATLEAN_ROOT="$REPO_ROOT/Statlean.lean"
    CANDIDATE_MODULE="$OUT_DIR/promoted/AutoPromoted.candidate.lean"
    APPLY_SUMMARY="$OUT_DIR/promoted/statlib_apply_summary.json"
    SOURCE_GENERATED="$OUT_DIR/generated/Generated.lean"
    if [[ ! -f "$SOURCE_GENERATED" ]]; then
      SOURCE_GENERATED="$OUT_DIR/promoted/generated/Generated.lean"
    fi

    python3 "$(dirname "$0")/promote_to_statlib.py" \
      --source-lean "$SOURCE_GENERATED" \
      --promote-report "$PROMOTE_JSON" \
      --repo-root "$REPO_ROOT" \
      --output-module "$CANDIDATE_MODULE" \
      --exclude-module "$STATLIB_MODULE" \
      --summary-json "$APPLY_SUMMARY" > "$OUT_DIR/logs/statlib_apply.log"

    MODULE_DECL_COUNT=$(python3 - <<PY
import json
from pathlib import Path
obj = json.loads(Path("$APPLY_SUMMARY").read_text(encoding="utf-8"))
print(int(obj.get("module_decl_count", 0)))
PY
)

    if [[ "$MODULE_DECL_COUNT" -eq 0 ]]; then
      echo "[promote] no new promoted declarations to add to Statlean (already present)"
      echo "{\"phase\":\"promote\",\"status\":\"ok\",\"report\":\"$REPORT\",\"applied\":true,\"promoted_count\":$PROMOTED_COUNT,\"regression_build\":\"ok\",\"statlib_apply_summary\":\"$APPLY_SUMMARY\",\"statlib_module\":\"$STATLIB_MODULE\",\"statlib_build\":\"skipped-existing\"}" >> "$OUT_DIR/logs/pipeline.jsonl"
    else
      # Pre-check candidate module compiles
      if (cd "$REPO_ROOT" && lake env lean "$CANDIDATE_MODULE") > "$OUT_DIR/logs/statlib_candidate_build.log" 2>&1; then
        echo "{\"phase\":\"promote\",\"status\":\"ok\",\"report\":\"$REPORT\",\"applied\":true,\"promoted_count\":$PROMOTED_COUNT,\"regression_build\":\"ok\",\"statlib_apply_summary\":\"$APPLY_SUMMARY\",\"candidate\":\"$CANDIDATE_MODULE\",\"statlib_build\":\"candidate-ok\"}" >> "$OUT_DIR/logs/pipeline.jsonl"
        echo "[promote] candidate module ready at $CANDIDATE_MODULE (stabilize step will migrate to target modules)"
      else
        echo "{\"phase\":\"promote\",\"status\":\"ok\",\"report\":\"$REPORT\",\"applied\":true,\"promoted_count\":$PROMOTED_COUNT,\"regression_build\":\"ok\",\"statlib_apply_summary\":\"$APPLY_SUMMARY\",\"candidate\":\"$CANDIDATE_MODULE\",\"statlib_build\":\"candidate-fail\"}" >> "$OUT_DIR/logs/pipeline.jsonl"
        echo "[promote] candidate module pre-check failed (see $OUT_DIR/logs/statlib_candidate_build.log)" >&2
        exit 1
      fi
    fi
  else
    echo "{\"phase\":\"promote\",\"status\":\"ok\",\"report\":\"$REPORT\",\"applied\":true,\"promoted_count\":$PROMOTED_COUNT,\"regression_build\":\"fail\"}" >> "$OUT_DIR/logs/pipeline.jsonl"
    echo "[promote] regression build failed (see $OUT_DIR/logs/promoted_build.log)" >&2
    exit 1
  fi
else
  echo "{\"phase\":\"promote\",\"status\":\"ok\",\"report\":\"$REPORT\",\"applied\":false,\"promoted_count\":$PROMOTED_COUNT}" >> "$OUT_DIR/logs/pipeline.jsonl"
fi

echo "[promote] wrote $REPORT"
