#!/usr/bin/env bash
set -euo pipefail

TEX=${1:?usage: from_tex.sh <tex_path> <input_dir>}
INPUT_DIR=${2:?usage: from_tex.sh <tex_path> <input_dir>}

if [[ ! -f "$TEX" && -f "../$TEX" ]]; then
  TEX="../$TEX"
fi

if [[ ! -f "$TEX" ]]; then
  echo "[from-tex] input tex not found: $TEX" >&2
  exit 1
fi

python3 "$(dirname "$0")/from_tex.py" "$TEX" "$INPUT_DIR"
