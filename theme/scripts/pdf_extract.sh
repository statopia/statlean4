#!/usr/bin/env bash
set -euo pipefail

PDF=${1:?usage: pdf_extract.sh <pdf_file> <output_dir>}
OUTPUT_DIR=${2:?usage: pdf_extract.sh <pdf_file> <output_dir>}
PDF=$(python3 -c 'import os,sys; print(os.path.abspath(sys.argv[1]))' "$PDF")
OUTPUT_DIR=$(python3 -c 'import os,sys; print(os.path.abspath(sys.argv[1]))' "$OUTPUT_DIR")

SKIP_MINERU=${SKIP_MINERU:-0}
SKIP_FLAG=""
if [[ "$SKIP_MINERU" == "1" ]]; then
  SKIP_FLAG="--skip-mineru"
fi

python3 "$(dirname "$0")/pdf_extract.py" \
  --pdf "$PDF" \
  --output-dir "$OUTPUT_DIR" \
  $SKIP_FLAG

echo "{\"phase\":\"pdf-extract\",\"status\":\"ok\",\"pdf\":\"$PDF\",\"output_dir\":\"$OUTPUT_DIR\"}"
