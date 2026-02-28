#!/usr/bin/env bash
set -euo pipefail

ROOT_DEFAULT="$(cd "$(dirname "$0")/../.." && pwd)"
ROOT="${1:-$ROOT_DEFAULT}"

add_or_replace() {
  local name="$1"
  shift
  if codex mcp get "$name" >/dev/null 2>&1; then
    codex mcp remove "$name" >/dev/null 2>&1 || true
  fi
  codex mcp add "$name" -- "$@"
}

add_or_replace repo-index python3 "$ROOT/theme/mcp/servers/repo_index_server.py" --workspace "$ROOT"
add_or_replace tex-parser python3 "$ROOT/theme/mcp/servers/tex_parser_server.py" --workspace "$ROOT"
add_or_replace lake-build python3 "$ROOT/theme/mcp/servers/lake_build_server.py" --workspace "$ROOT"
add_or_replace lean-lsp python3 "$ROOT/theme/mcp/servers/lean_lsp_server.py" --workspace "$ROOT"

codex mcp list --json
