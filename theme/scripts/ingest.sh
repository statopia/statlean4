#!/usr/bin/env bash
set -euo pipefail

INPUT_DIR=${1:?usage: ingest.sh <input_dir> <out_dir>}
OUT_DIR=${2:?usage: ingest.sh <input_dir> <out_dir>}

mkdir -p "$OUT_DIR/logs" "$OUT_DIR/input_snapshot"

required=(theorems.yaml notation.yaml scope.yaml)
for f in "${required[@]}"; do
  if [[ ! -f "$INPUT_DIR/$f" ]]; then
    echo "[ingest] missing required file: $INPUT_DIR/$f" >&2
    exit 1
  fi
done

if ! compgen -G "$INPUT_DIR/*.tex" > /dev/null; then
  echo "[ingest] missing LaTeX source (*.tex) under $INPUT_DIR" >&2
  exit 1
fi

cp -f "$INPUT_DIR"/* "$OUT_DIR/input_snapshot/" 2>/dev/null || true

echo "{\"phase\":\"ingest\",\"status\":\"ok\"}" >> "$OUT_DIR/logs/pipeline.jsonl"
echo "[ingest] ok"
