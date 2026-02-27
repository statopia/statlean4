#!/usr/bin/env bash
set -euo pipefail

PDF=${1:?usage: pdf_extract.sh <pdf_file> <output_dir> [backend] [extra_args...]}
OUTPUT_DIR=${2:?usage: pdf_extract.sh <pdf_file> <output_dir> [backend] [extra_args...]}
BACKEND=${3:-claude}
shift 3 2>/dev/null || shift $# 2>/dev/null
EXTRA_ARGS=("$@")

PDF=$(python3 -c 'import os,sys; print(os.path.abspath(sys.argv[1]))' "$PDF")
OUTPUT_DIR=$(python3 -c 'import os,sys; print(os.path.abspath(sys.argv[1]))' "$OUTPUT_DIR")

python3 "$(dirname "$0")/pdf_extract.py" \
  --pdf "$PDF" \
  --output-dir "$OUTPUT_DIR" \
  --backend "$BACKEND" \
  "${EXTRA_ARGS[@]}"

echo "{\"phase\":\"pdf-extract\",\"status\":\"ok\",\"pdf\":\"$PDF\",\"output_dir\":\"$OUTPUT_DIR\",\"backend\":\"$BACKEND\"}"
