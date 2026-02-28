# Theme: LaTeX to Lean (Statlib-first) Template

This directory is a template for a low-touch pipeline:

1. Ingest theorem-level LaTeX inputs.
2. Generate Lean formalization tasks.
3. Close proofs until the generated Lean file type-checks with no `sorry`.
4. Promote reusable parts into `Statlib`.
5. Stabilize matured declarations into curated stat-oriented modules.
6. Keep project-layer files thin and statlib-first.

## Directory Layout

- `input/`: input contract and examples.
- `mcp/`: required MCP servers and tool contracts.
- `skills/`: 5 skill templates (one folder per skill).
- `scripts/`: pipeline scripts.
- `Makefile`: one-command pipeline entry.

## Input Contract

Required files per run (default location: `theme/input/`):

- `paper.tex` (or segmented `.tex` files)
- `theorems.yaml`
- `notation.yaml`
- `scope.yaml`

See examples and schema in `theme/input/`.

## One-Command Pipeline

```bash
make -C theme formalize
```

Phases:

- `ingest`: validate input package.
- `plan`: produce theorem dependency plan.
- `generate`: produce Lean skeletons.
- `prove-loop`: compile-fix loop until closure.
- `promote`: move reusable lemmas into `Statlib`.
- `stabilize`: migrate stable declarations from `AutoPromoted` into curated `Statlean/*` modules.
- `gate`: enforce zero-sorry and build gates.

Default behavior:

- `AUTO_AGENT=1`: `prove-loop` will call the agent automatically when fixes are needed.
- `AGENT_BACKEND=codex`: use Codex (GPT-4) as the agent. Set `AGENT_BACKEND=claude` for Claude.
- `STRICT_TRANSLATION=1`: unresolved translation markers (`TODO_TRANSLATE_ID`) are treated as failure.

## Start From `./output.tex`

If your raw input is a tex file like `./output.tex`, use:

```bash
cd /home/gavin/statlean
make -C theme from-tex TEX=./output.tex
make -C theme formalize
```

Or one command:

```bash
make -C theme tex-formalize TEX=./output.tex
```

Strict auto-closure mode (recommended):

```bash
AUTO_AGENT=1 STRICT_TRANSLATION=1 make -C theme tex-formalize TEX=./output.tex
```

Strict mode with batched auto-fix (recommended for larger papers):

```bash
AUTO_AGENT=1 STRICT_TRANSLATION=1 BATCH_SIZE=3 MAX_ITERS=8 AGENT_TIMEOUT_SECONDS=180 make -C theme tex-formalize TEX=./output.tex
```

Batch behavior:

- each prove-loop iteration prioritizes a subset of unresolved theorem IDs
- batch IDs are logged in `theme/out/logs/fix_batch_ids_<iter>.txt`
- pipeline log includes `agent-batch` and `unresolved_after` fields

Scaffold-only mode (no agent fixing):

```bash
AUTO_AGENT=0 STRICT_TRANSLATION=0 make -C theme tex-formalize TEX=./output.tex
```

`from-tex` will:

- copy tex to `theme/input/paper.tex`
- extract theorem-like blocks into `theme/input/theorems.yaml`
- keep/create `notation.yaml` and `scope.yaml`

## Quality Gates

`theme/scripts/gate.sh` enforces:

- generated file type-checks: `lake env lean theme/out/generated/Generated.lean`.
- no `sorry` in target Lean output.
- no `axiom` in target Lean output (except explicit allowlist).
- no unresolved `TODO_TRANSLATE_ID` markers (unless `ALLOW_TODO_TRANSLATE=1`).
- generated file imports `Statlean`.

## Output Inspection

After `formalize`, inspect:

- `theme/out/plan.md`: theorem plan summary
- `theme/out/generated/Generated.lean`: generated Lean target file
- `theme/out/generated/manifest.json`: counts + unresolved IDs
- `theme/out/logs/pipeline.jsonl`: phase-by-phase status
- `theme/out/logs/gate_build.log`: final build log
- `theme/out/reuse_report.txt`: statlib promotion candidates

Quick checks:

```bash
test -f theme/out/logs/pipeline.jsonl && tail -n 20 theme/out/logs/pipeline.jsonl
grep -n 'TODO_TRANSLATE_ID:' theme/out/generated/Generated.lean || true
grep -nE '\\bsorry\\b|^\\s*axiom\\b' theme/out/generated/Generated.lean || true
```

Apply auto-promotion with regression build:

```bash
AUTO_AGENT=0 STRICT_TRANSLATION=0 APPLY_PROMOTION=1 PROMOTE_MIN_FANIN=2 make -C theme formalize
```

When `APPLY_PROMOTION=1` and promoted items exist, the pipeline now:

- generates a candidate module and pre-checks it compiles before writing to `Statlean/`
- only writes declarations that are not already present in existing `Statlean/**/*.lean`
- writes promoted declarations to `Statlean/AutoPromoted.lean` only after pre-check passes
- keeps `AutoPromoted` as a staging file by default (set `IMPORT_AUTOPROMOTED=1` if you want it imported by `Statlean.lean`)
- runs regression checks on `theme/out/promoted/generated/Generated.lean`, `Statlean.AutoPromoted`, and `Statlean`
- groups promoted declarations into thematic sections inside `Statlean.AutoPromoted` (currently heuristic groups such as `SPDGeometry` and `SPDMeans`)

Stabilization behavior (default `APPLY_STABILIZE=1`):

- keeps `AutoPromoted` as a staging layer
- only migrates declarations after they are stable for `STABILIZE_MIN_STABLE_RUNS` runs (default `2`)
- enforces statistical focus by default (`STABILIZE_STATS_ONLY=1`)
- checks name collisions against existing `Statlean/**/*.lean` and local mathlib source (if available)
- writes stable declarations into curated targets such as:
  - `Statlean/Statistics/SPD/FrechetMean.lean`
  - `Statlean/Statistics/SPD/Determinant.lean`

Recommended full run (strict + promotion + stabilization):

```bash
AUTO_AGENT=1 STRICT_TRANSLATION=1 APPLY_PROMOTION=1 APPLY_STABILIZE=1 BATCH_SIZE=2 AGENT_TIMEOUT_SECONDS=180 MAX_ITERS=8 make -C theme tex-formalize TEX=./output.tex
```

## Using Claude as Agent Backend

Instead of Codex, you can use Claude Code as the prove-loop agent:

```bash
# One-command: full pipeline with Claude
make -C theme formalize-claude

# Or set the environment variable explicitly
AGENT_BACKEND=claude make -C theme formalize

# Full recommended run with Claude
AGENT_BACKEND=claude AUTO_AGENT=1 STRICT_TRANSLATION=1 BATCH_SIZE=5 MAX_ITERS=5 AGENT_TIMEOUT_SECONDS=300 make -C theme tex-formalize TEX=./output.tex
```

Claude advantages over Codex for this pipeline:
- Better Lean 4 / Mathlib knowledge (specialized training)
- Larger batch sizes feasible (5-10 IDs per iteration vs 3)
- No separate CLI login required (uses `claude` CLI directly)
- Better mathematical reasoning for statistical theorems
- **Parallel mode**: one agent per theorem ID for maximum throughput

Requirements:
- `claude` CLI installed and authenticated
- Recommended: set `BATCH_SIZE=5` (Claude handles larger batches well)

### Parallel Claude Mode

Launch one independent Claude agent per unresolved theorem ID:

```bash
# Parallel mode (all IDs at once, max 4 concurrent agents)
PARALLEL=1 MAX_PARALLEL=4 AGENT_BACKEND=claude make -C theme formalize

# Or use the shortcut
make -C theme formalize-parallel

# Full recommended parallel run
PARALLEL=1 MAX_PARALLEL=4 AUTO_AGENT=1 STRICT_TRANSLATION=1 AGENT_TIMEOUT_SECONDS=300 MAX_ITERS=3 make -C theme tex-formalize TEX=./berry_esseen.tex
```

Each agent receives a focused prompt for its assigned theorem and works independently.
Agents share the target file, so for best results use `MAX_PARALLEL=1` if theorems have inter-dependencies, or split into independent files.

## Troubleshooting

**Codex backend** (`AGENT_BACKEND=codex`):
- If `prove-loop` reports `codex backend/network failure detected`:
  - verify Codex CLI can reach backend (`codex exec "ping"`),
  - verify login state (`codex login`),
  - retry with stable network.
- If it reports `codex MCP startup failure detected`:
  - run `codex mcp list --json`,
  - rerun `bash theme/mcp/register_codex.sh`,
  - run `python3 theme/mcp/scripts/smoke_test_mcp.py`.

**Claude backend** (`AGENT_BACKEND=claude`):
- If `prove-loop` reports `claude backend/network failure detected`:
  - verify `claude --version` works,
  - check API rate limits / account status,
  - retry with `AGENT_TIMEOUT_SECONDS=600`.

## MCP Setup (Codex)

```bash
bash theme/mcp/register_codex.sh
codex mcp list --json
```

If needed, remove all four servers:

```bash
bash theme/mcp/unregister_codex.sh
```

## Low-Touch Operation Guidelines

To minimize manual confirmation and permissions:

- Pre-install toolchain (`elan`, `lake`, mathlib cache).
- Pre-configure MCP endpoints and tokens.
- Use non-interactive scripts only.
- Keep all writes inside repo workspace.
- Fail fast with machine-readable logs in `theme/out/logs/`.

## Integration Pattern

- Keep reusable theorems in `Statlib/*`.
- Keep theorem-instance/project glue in `Formalization/*`.
- Prefer `Formalization` importing `Statlib` over direct `Mathlib` imports where possible.
