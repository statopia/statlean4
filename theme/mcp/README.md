# MCP Contract Template

This pipeline expects these MCP capabilities.

## Local MCP Servers Provided

- `servers/repo_index_server.py`
- `servers/tex_parser_server.py`
- `servers/lake_build_server.py`
- `servers/lean_lsp_server.py`

All servers are pure Python (no third-party package required).

## Codex Registration (One Command)

From repo root:

```bash
bash theme/mcp/register_codex.sh
```

Check:

```bash
codex mcp list --json
```

Remove:

```bash
bash theme/mcp/unregister_codex.sh
```

## Config Templates

- `codex.mcp.example.json`: JSON template with this repo's real paths.
- `claude.mcp.example.json`: same for Claude clients.
- `env.example`: optional env vars template.

## Required Operations

- `lean-lsp.get_goal(file, line, col)` (best-effort fallback)
- `lean-lsp.get_diagnostics(file?)`
- `lean-lsp.find_symbol(query)`
- `lake-build.build(target?)`
- `lake-build.lean_file(file)`
- `lake-build.hygiene_scan(scan_root?)`
- `tex-parser.extract_theorems(tex_path, theorem_envs?)`
- `tex-parser.build_input_package(tex_path, input_dir, namespace?, layer?)`
- `repo-index.search(pattern, root?, glob?)`
- `repo-index.list_files(root?, glob?)`
- `repo-index.read_file(path, start_line?, end_line?)`

## Smoke Test

```bash
python3 theme/mcp/scripts/smoke_test_mcp.py
```

## Agent Policy

- Prefer deterministic tool calls before free-form synthesis.
- Do not create new axioms.
- If proof fails, first search `Statlib` for reusable lemma candidates.
- Keep logs machine-readable (`jsonl`) in `theme/out/logs/`.

## Credentials and Permissions

- Configure all tokens outside runtime prompts.
- Avoid interactive auth in the proving loop.
- Keep execution inside workspace to avoid escalation prompts.
