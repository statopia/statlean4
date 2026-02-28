#!/usr/bin/env bash
set -euo pipefail

INPUT_DIR=${1:?usage: generate.sh <input_dir> <out_dir> <repo_root>}
OUT_DIR=${2:?usage: generate.sh <input_dir> <out_dir> <repo_root>}
REPO_ROOT=${3:?usage: generate.sh <input_dir> <out_dir> <repo_root>}

mkdir -p "$OUT_DIR/logs"
python3 "$(dirname "$0")/generate_project.py" \
  --input-dir "$INPUT_DIR" \
  --out-dir "$OUT_DIR" \
  --repo-root "$REPO_ROOT"

echo "{\"phase\":\"generate\",\"status\":\"ok\"}" >> "$OUT_DIR/logs/pipeline.jsonl"
echo "[generate] wrote generated project"
