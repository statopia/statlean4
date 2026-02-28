#!/usr/bin/env bash
set -euo pipefail

for name in repo-index tex-parser lake-build lean-lsp; do
  codex mcp remove "$name" >/dev/null 2>&1 || true
done

codex mcp list --json
