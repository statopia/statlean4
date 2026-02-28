#!/usr/bin/env bash
set -euo pipefail

INPUT_DIR=${1:?usage: plan.sh <input_dir> <out_dir>}
OUT_DIR=${2:?usage: plan.sh <input_dir> <out_dir>}

mkdir -p "$OUT_DIR/logs"

THEOREMS="$INPUT_DIR/theorems.yaml"
PLAN_MD="$OUT_DIR/plan.md"

{
  echo "# Formalization Plan"
  echo
  echo "Generated from: $THEOREMS"
  echo
  echo "## Summary"
  python3 - <<PY
import yaml
from collections import Counter
from pathlib import Path
p = Path("$THEOREMS")
obj = yaml.safe_load(p.read_text(encoding="utf-8")) or {}
ths = list(obj.get("theorems", []) or [])
ids = [str(t.get("id","")) for t in ths]
dups = [k for k,v in Counter(ids).items() if k and v > 1]
deps = sum(1 for t in ths if (t.get("dependencies") or []))
print(f"- theorem_count: {len(ths)}")
print(f"- theorem_with_dependencies: {deps}")
print(f"- duplicate_ids: {len(dups)}")
for d in dups:
    print(f"  - {d}")
PY
  echo
  echo "## Theorem IDs"
  if command -v rg >/dev/null 2>&1; then
    rg -n "^\s*-\s*id:\s*" "$THEOREMS" | sed -E 's/.*id:\s*//g' | sed 's/^/- /'
  else
    grep -nE "^[[:space:]]*-[[:space:]]*id:[[:space:]]*" "$THEOREMS" \
      | sed -E 's/.*id:[[:space:]]*//g' | sed 's/^/- /'
  fi
  echo
  echo "## Dependency Lines"
  if command -v rg >/dev/null 2>&1; then
    rg -n "^\s*dependencies:\s*\[" "$THEOREMS" || true
  else
    grep -nE "^[[:space:]]*dependencies:[[:space:]]*\\[" "$THEOREMS" || true
  fi
} > "$PLAN_MD"

echo "{\"phase\":\"plan\",\"status\":\"ok\",\"plan\":\"$PLAN_MD\"}" >> "$OUT_DIR/logs/pipeline.jsonl"
echo "[plan] wrote $PLAN_MD"
