---
description: Full pipeline — PDF theorem → Lean 4 formalization (extract → ingest → skeleton → prove → gate)
# KEEP IN SYNC: 14 mcp__statlean_prove__* tools also listed in prove-deep.md frontmatter (W2.S4)
allowed-tools: Read, Edit, Write, Grep, Glob, Bash, Agent, Skill, Task, WebSearch, WebFetch, mcp__statlean_web_ui__request_user_decision, mcp__statlean_prove__write_file, mcp__statlean_prove__replace_sorry, mcp__statlean_prove__edit_lines, mcp__statlean_prove__lake_build, mcp__statlean_prove__check_snippet, mcp__statlean_prove__revert, mcp__statlean_prove__check_type, mcp__statlean_prove__extract_goal, mcp__statlean_prove__suggest_lemma, mcp__statlean_prove__auto_tactic, mcp__statlean_prove__try_fix, mcp__statlean_prove__lean_loogle, mcp__statlean_prove__grep_repo, mcp__statlean_prove__glob_repo
model: opus
argument-hint: <pdf-file> [--theorem <name>] [--pages <range>] [--prove-depth deep|shallow] [--time-budget 1h]
---

# Full Formalization Pipeline

Input: $ARGUMENTS

## Overview

Run the complete pipeline: PDF → LaTeX → YAML → Lean 4 → Prove → Gate

## Step 1: PDF Extract

```bash
# Default for math-heavy papers: mineru (local VLM OCR, preserves LaTeX)
python3 theme/scripts/pdf_extract.py --pdf <pdf> --output-dir <dir> --backend mineru [--theorem "<Kind id>"] [--pages <range>]

# Fallback if mineru is unavailable or the paper is text-only:
python3 theme/scripts/pdf_extract.py --pdf <pdf> --output-dir <dir> --backend pymupdf [...]
```

**`--theorem` form (STRICT — pass kind, not bare id)**: write
`--theorem "Theorem 3.9"` / `--theorem "Lemma S1"` /
`--theorem "Proposition 1"` / `--theorem "Assumption A1"` rather than a
bare id `--theorem "3.9"`. The kind hint disambiguates same-id collisions
across declaration types (Shao p.186 has `Example 3.9`, p.205 has
`Theorem 3.9` — bare `3.9` returns the EARLIEST kind, often wrong).
Recognised kind aliases: Theorem/Thm, Lemma/Lem, Proposition/Prop,
Corollary/Cor, Definition/Def, Assumption, Example/Ex, Remark/Rem.

**Default coarse-screen behavior with `--theorem`** (no extra flags
needed):

- Declaration cluster + 1-page spill (statement)
- `Proof of <Kind> <id>.` block if present (Cox-style supplementary
  appendix proofs that sit far from the statement)
- Citation expansion: parses `by Lemma X.Y`, `under Assumptions
  (A1)–(A10)`, `model (3.25)`, `根据定理 5.1` etc. and unions the
  pages where each cited dep is declared
- Multi-cluster note: when the same id is declared in two non-adjacent
  locations (e.g. main paper + supplementary re-statement), stdout
  prints a `note: <Kind> <id> has N non-adjacent declaration clusters
  at pages [...]` line and returns the first cluster only

Opt-out flags (skeleton-only / minimal queries):

- `--no-proof-span` — skip the deferred-proof scan, return statement
  cluster only (useful when you want only the theorem signature for
  skeleton generation)
- `--no-include-deps` — skip dep expansion, return statement (+ proof
  span unless `--no-proof-span`) only
- Both together → fully minimal extraction (statement page + 1 spill)

`--deps-max-pages N` (default 30) caps the post-expansion total page
count. Dep extras are truncated to fit; target pages always preserved.

`--pages <range>` (e.g. `7,9-12`) takes priority over `--theorem` when
both are passed. With `--pages` alone, dep expansion is OFF by default
(no theorem context to expand against); pass `--include-deps` to opt
in if you still want citation tracing on the supplied page range.

**Backend choice rule (STRICT — do NOT skip):**
- Math-heavy papers (theorems with formulas, integrals, subscripts, matrix
  notation) → **always** `--backend mineru`. pymupdf will emit broken LaTeX
  tokens that cannot be reliably reconstructed and will poison every
  downstream step (LaTeX Ingest, Lean Skeleton, Prove).
- Text-only papers (no math, no diagrams) → `--backend pymupdf` is acceptable
  and ~10× faster.
- When in doubt, pick `mineru`. The script auto-detects mineru availability
  when `--backend` is omitted, but be explicit in this pipeline so the
  choice shows up in the tool_result log.

If mineru's output still has noise (rare), **do not in-session hand-patch
broken LaTeX** — the hand-patching step was the root of past Rule 3
violations where agents invented statements to fill OCR gaps. Instead:
call `mcp__statlean_web_ui__request_user_decision` with
options ["paste_statement","abort"] and let the user supply the raw
theorem text.

**OCR failure cascade (handled inside the wrapper)**: the wrapper retries
automatically:

1. `-b hybrid-auto-engine` (default — VLM, fastest+cleanest on CPU per
   empirical comparison, ~14 s/page on this box)
2. `-b pipeline -d cpu` fallback if attempt 1 silently failed (exit 0
   with empty `.md` output — observed on 83-page PDFs). Pipeline is
   ~1.7× slower and has minor English OCR glitches but reliably produces
   output.

If **both** attempts fail the wrapper raises `SystemExit` with a
`MinerU failed on BOTH ...` message. When you see that error:
**do NOT retry with pymupdf and do NOT hallucinate content**. Call:

```
mcp__statlean_web_ui__request_user_decision({
  question: "MinerU couldn't OCR this PDF. Either paste the theorem statement, or supply a smaller --pages range.",
  options: ["paste_statement", "retry_smaller_pages", "abort"]
})
```

**Page-count sanity**: before invoking the wrapper, if the PDF is longer
than ~15 pages AND `--pages` / `--theorem` was not supplied by the
caller, warn in the Step 1 report: "OCR on N pages ≈ N×15s on CPU —
consider a page range via user input before proceeding."

Report: number of blocks extracted, key theorems found, backend used.

**REQUIRED auto-vs-manual telemetry**: in the Step 1 report narrative, include a line of exactly the form

```
auto_extracted: <integer>  agent_corrected: <true|false>  agent_correction_kind: <none|env_wrap|hand_transcribe|page_clip|other>
```

where:
- `auto_extracted` = number of structured theorem blocks the auto-extractor found unaided (0 means the structural extractor produced nothing usable on this paper).
- `agent_corrected` = true iff you wrote / edited `paper.tex` outside of what the auto-extractor produced (e.g. hand-transcribed a `Theorem 2.3.` plain-text header into a `\begin{theorem}` env so Step 2 can ingest it).
- `agent_correction_kind` = one short tag describing the kind of patch — `env_wrap` (wrapped a plain-text header in a theorem env), `hand_transcribe` (typed the body from clean OCR), `page_clip` (re-extracted a smaller page range), `other`, or `none`.

Reason: the auto-extractor silently returns `0 blocks` on papers that use `Theorem N.` plain text instead of `\begin{theorem}` envs. Without this line, downstream metrics conflate "auto pipeline succeeded" with "agent papered over a broken extractor", and we cannot detect when the extractor regresses.

## Step 2: LaTeX Ingest

```bash
python3 theme/scripts/from_tex.py theme/input/paper.tex -o theme/input/theorems.yaml
```

Report: number of theorem entries in YAML.

**REQUIRED auto-vs-manual telemetry**: in the Step 2 report narrative, include a line of exactly the form

```
auto_canonicalized: <true|false>  agent_corrected: <true|false>  agent_correction_kind: <none|canonical_name|namespace|both|other>
```

where:
- `auto_canonicalized` = true iff `from_tex.py`'s heuristic canonical-name + namespace assignment was kept verbatim.
- `agent_corrected` = true iff you edited the YAML's `canonical_name` and/or `namespace` after the script ran (e.g. the heuristic mis-tagged Shao 2.3 minimal-sufficiency as `student_t` and you fixed it to `minimal_sufficient_tools` under `Statlean.Sufficiency.MinimalSufficiency`).
- `agent_correction_kind` = `canonical_name`, `namespace`, `both`, `other`, or `none`.

Reason: the heuristic canonicalizer keyword-matches and silently mis-tags theorems whose surface text overlaps with a known family. Without this line we cannot detect the canonicalizer's miss rate and the wrong namespace cascades into Step 2.5 (existing-symbol scan looks in the wrong file) and Step 3 (skeleton lands in the wrong module).

## Step 3: Lean Skeleton (use /tex2lean skill)

**Follow `theme/formalize_playbook.md` Steps 2-4** for each theorem:
1. **Check existing code first** — for each yaml entry, locate `Statlean/<namespace-as-path>.lean` and grep for the canonical name + variants (snake/camel; multi-part suffixes like `_of_subfamily`). Skeleton only the missing sub-parts; if all parts already exist, stop the pipeline as "already covered" without writing anything (Shao 2.3 case: (i)+(iii) were `minimalSufficient_of_subfamily`/`_of_densityRatio` in `MinimalSufficiency.lean`, only (ii) was new).
2. Read `theme/mathlib_api_index.md` for Mathlib type mappings
   - 补充：`grep -i '<keyword>' theme/mathlib_full_type_index.tsv`（51K 条全量 Mathlib 索引）
3. Design Lean signature (must reflect precise math content) — apply the **honesty rules below** during signature design, BEFORE `write_file`.
4. Place in appropriate `Statlean/` module
5. Build to verify skeleton compiles
6. Run honesty check: re-read the **honesty rules below** and confirm none are violated.

### Honesty rules (MANDATORY pre-write checklist)

> Inlined here from `theme/skills/lean-skeleton/SKILL.md` per Path A czy
> parity (2026-05-01). The ported content is byte-equal with czy
> `honestyRules.ts:25-46` (SKELETON_HONESTY_RULES) and `:162-200`
> (LEAN_NAMING_CONVENTION). Migration rationale: the SKILL file was a
> dead text in the SDK-bridge runtime — `Skill {skill: "lean-skeleton"}`
> is never invoked by pipeline.md, so the rules never reached the agent
> context. Inlining here makes them unavoidable. SKILL file retained as
> documentation source-of-truth; content here is the runtime dispatch
> path. (Same migration as proof-closure → prove-deep.md on 2026-04-30.)

#### Type encoding + anti-vacuity

<!-- Source: website-czy/src/lib/orchestrator/honestyRules.ts:25-46 (SKELETON_HONESTY_RULES) — body byte-equal; heading adapted per spec §3.3/§3.4 -->

When the source math gives a SPECIFIC object, BIND it as a parameter — never hide it under `∃`:

| Math | Lean (✓) | REJECTED (✗) |
|---|---|---|
| Probability measure / specific noise (e.g. N(0, σ²I)) | `(μ : Measure Ω) [IsProbabilityMeasure μ]` or a Mathlib distribution | `∃ μ : Measure Ω, ...` |
| Almost-sure claim under a given measure | `∀ᵐ ω ∂μ, P ω` (μ is a bound parameter) | `∃ μ, ∀ᵐ ω ∂μ, P ω` ← prover picks μ = 0, claim collapses |
| Random variable | `(X : Ω → ℝ) (hX : Measurable X)` | `∃ X, Measurable X ∧ ...` |
| L² / E[X] / E[X|G] / σ-algebra | `MemLp X 2 μ` / `∫ x, X x ∂μ` / `μ[X|G]` / `[MeasurableSpace Ω]` | — |

#### Anti-vacuity rules (every entry is a known agent failure)

- **Escapable existential** (highest risk): `∃ m, ∀ᵐ _ ∂m, _` — prover picks m = 0; bind m instead.
- **Stub binder**: `(_ : True | False | Unit | PUnit | Empty | 0 = 1)` — vacuously satisfied.
- **Vacuous wrapper**: `True ∧ _`, `_ ∧ True`, `∃ _, True`, `∃ C > 0, True`.
- **Disconnected binder**: type doesn't reference any ambient variable (μ, X, σ, Ω, …) — it's a stub; omit it.
- **Collapsed quantifier**: `∀ θ₁ θ₂, θ₁ = θ₂`, `∃ C > 0, ∀ x, C > 0` (body ignores x).
- **Weakening**: ℝ → ℕ, ∀ → ∃, removed quantifier bounds.

Pre-write self-check: pick trivial witnesses for each ∃ in your conclusion (μ := 0, set := ∅, n := 0, X := fun _ => 0). If the claim becomes vacuously true, the skeleton is wrong — rewrite before `write_file`.

#### Identifier naming (LaTeX-style ASCII for math symbols)

<!-- Source: website-czy/src/lib/orchestrator/honestyRules.ts:162-200 (LEAN_NAMING_CONVENTION) — body byte-equal; heading adapted per spec §3.3/§3.4 -->

When the source math uses one of these symbols, **always** write the
ASCII transliteration as the Lean identifier. Raw Unicode causes lexer
failures that are hard to debug.

##### HARD BAN: `λ` `Π` `Σ` `∀` `∃` (Lean reserved keywords)

These five characters are **reserved keywords** (lambda binder, dependent
function/sigma type, universal/existential quantifier). They MUST NOT
appear ANYWHERE inside an identifier — not as the whole name, not as a
prefix/suffix, **not embedded in a compound name**. The Lean lexer cuts
the identifier at the keyword and reports `unexpected token` at that
column.

Common embedded mistake — these all FAIL to parse:

| Mistake | Why it fails | Fix |
|---|---|---|
| `hλ_pos` (hypothesis name) | `λ` mid-identifier ends `h` early; parser expects `)` | `hlambda_pos` |
| `Σ_inv` (covariance inverse) | `Σ` starts a sigma-type token | `Sigma_inv`, `covInv` |
| `Πₖ` (product symbol) | `Π` starts a Pi-type token | `Pi_k`, `prod_k` |
| `∀_intro` / `∃_witness` | quantifier symbols are keywords | `forall_intro` / `exists_witness` |

Rule of thumb: before you `write_file`, **grep your own draft for the
five characters `λ Π Σ ∀ ∃`** — if any appears inside a name (i.e.
adjacent to a letter, digit, or `_`), rename to ASCII.

##### LaTeX-style transliteration table (other symbols)

| LaTeX in source | DON'T write | DO write |
|---|---|---|
| `\lambda` (eigenvalue, Lagrange mult.) | `λ` (keyword) | `lambda`, `lam`, `eigval` |
| `\Pi` / `\Sigma` (covariance, etc.) | `Π` / `Σ` (keywords) | `Pi`, `Sigma`, `Sigma_mat`, `covMat` |
| `\hat{\beta}`, `\hat{\theta}` | `β̂`, `θ̂` (combining mark) | `hat_beta`, `hat_theta` |
| `\tilde{x}`, `\bar{X}` | `x̃`, `X̄` (combining mark) | `tilde_x`, `bar_X` |

**Always safe** (precomposed, not keywords): `α β γ δ ε ζ η θ ι κ μ ν ξ π ρ τ φ χ ψ ω` (note: `λ Π Σ` are excluded), subscripts `β₀ x₁ ε_n`, superscripts `x² ε⁺ X⁻¹`.

### Step 3 follow-up: drift detection (REQUIRED)

After Step 3 emits its skeleton, compare the source spec against the
generated Lean to catch math-content drift (dimension reduction,
hypothesis externalization, conclusion replacement) the agent didn't
self-report. Pure additive — emits a `formalization_delta` event
(ui-signals.md §6) only when drift is detected; silent on faithful
encodings.

```bash
# Run once per skeleton'd theorem. The script short-circuits on
# byte-identical inputs and uses a cheap haiku model otherwise.
# Failure is non-fatal — the script reports + exits non-zero but the
# pipeline continues. Skip silently when sandbox is unset (CLI-standalone)
# OR when the web server has already spawned the detector (sentinel:
# .web_spawned_detect_delta). Web's server-side spawn is more reliable
# than relying on agent bash compliance, so skipping here when web ran
# it avoids duplicate haiku calls.
if [[ -n "$SANDBOX" && ! -f "$SANDBOX/.web_spawned_detect_delta" ]]; then
  python3 theme/scripts/detect_delta.py \
    --before "$SANDBOX/theorems.yaml" \
    --after "$SANDBOX/Main.lean" \
    --before-rel theorems.yaml --after-rel Main.lean \
    --sandbox "$SANDBOX" --quiet \
    || echo "[pipeline] detect_delta non-zero (informational, continuing)"
fi
```

Why: `theorems.yaml → Main.lean` is the highest-drift transition in
the pipeline — the agent picks Mathlib types, may narrow ℝ→ℕ to make
something typecheck, may wrap conclusions in `True ∧ ...`. If a
breaking delta lands here, the Layer 4 judge at promotion time
(`judge-integrity.ts --events`) sees it as structured context and
biases verdict appropriately.

## Step 4: Build & Fix (use /build-fix skill)

**Pass the changed module(s) as `$ARGUMENTS` to `/build-fix`** — i.e. the namespace you wrote a skeleton into in Step 3 (e.g. `Statlean.Sufficiency.MinimalSufficiency`), comma-separated if more than one. **Never invoke `/build-fix` with empty arguments**: that triggers a default `lake build` which compiles the whole `Statlean` umbrella (and historically pulls in 540+ Web sandbox modules pre-Bug-1-fix), surfacing hundreds of pre-existing errors that have nothing to do with this run. The full-project regression check belongs to Step 6's promotion gate, not Step 4.

Step 4 declares PASS iff `lake build <changed-module>` itself returns clean (allowed-sorry exemptions apply per playbook). Do not invent a "PASS (scoped)" status — narrow build means narrow gate.

Iterate until clean compilation (max 5 cycles).

## Step 4.5: Extract Proof Bodies for R2 Route Search

Before proving, extract proof bodies from the input for use as route hints:
1. Read `theme/input/theorems.yaml` — check each theorem's `proof_body` field
2. For each theorem with a non-empty `proof_body`:
   - Run `python3 scripts/parse_proof_roadmap.py --format latex --inline "<proof_body>" --theorem <name>`
   - Store the parsed roadmap for injection into prove agents
3. These roadmaps will be passed to prove agents as R2 route hints (see Phase 0.5 in `/prove`)

## Step 5: Prove (subagent dispatch — uses Max plan quota, zero API credit)

Parse `--prove-depth` from arguments (default: deep).

`make formalize` already ran `prove` target which wrote `theme/out/prove_targets.json`.

If `--prove-depth shallow`:
  - Skip prove, proceed to Step 6 (sorry 留在 backlog 等后续攻击)

If `--prove-depth deep`:

  **W2.S5 (2026-05-01) — INVOKE /prove-deep, do NOT launch general-purpose.**
  Pre-W2.S5 this section instructed the agent to launch a general-purpose
  subagent with a hand-written R1-R5 prompt — that path bypassed
  prove-deep.md entirely (the agent never loaded the 4-rung stuck recovery
  / helper context inject / czy port priority bias). jobmolu42myoqp5
  trace evidence: 0 of 16 czy port keywords reached the dispatched
  prover prompt. Audit doc §5 Bug 1.

  Replacement (T2 narrative + T1 orchestrator fallback):

  1. Read `theme/out/prove_targets.json` to get the priority-ordered
     target list (typically a single sorry id, or `next`).
  2. Invoke the `/prove-deep` skill ONCE per cycle, passing the top
     target as argument. Use the Skill tool:

     ```
     Skill { skill: "prove-deep", args: "<target_sorry_id> --time-budget <budget>" }
     ```

     `/prove-deep` then runs its full Phase 0-3 narrative with:
     - Phase 0 cheap convergence (H3 library coverage / R6 paper reference
       / R7 citation verify / M5 auto_tactic pre-pass)
     - Phase 1 decompose + alignment loop (Slice 03 + H2 alt-path + H1
       elaborate plan)
     - Phase 2 prover dispatch + 4-rung stuck recovery (czy parity)
     - Phase 3 cycle finalize (commit + ingest_knowledge + MEMORY.md)

  3. After `/prove-deep` returns, verify sorry counts via
     `grep -c '\bsorry\b' Statlean/Web/<jobId>/Main.lean`.
  4. If any target remains unproved AND time budget allows, optionally
     invoke `/prove-deep` again with `next`.
  5. Run `lake build <changed-modules>` (the same set Step 4 used) to
     verify post-prove compile. Do NOT run a bare `lake build`; full-
     project verification is Step 6's job.

  **Orchestrator T1 fallback (proveCli.ts:onEvent)**: if Step 4 done
  fires AND no `/prove-deep` skill invocation is observed within 30
  seconds, the orchestrator pushes a `/prove-deep` user-turn directly.
  This guarantees the deep narrative loads even if the agent's pipeline.md
  compliance drifts. Mirror of the existing dispatch-batch-start
  fallback timer (proveCli.ts:1039-1060). Same rationale as PR2:
  T3 narrative reliability is ~0% on long prompts; T1 lifecycle hooks
  recover the missing call.

**Important**: This uses Claude Code subagents (Max plan quota), NOT the `claude` CLI
(which would consume API credits). The prove_loop.sh fallback is only for CI environments.

## Step 5.5: Infrastructure Extraction (inline, per CLAUDE.md rules)

1. **Zero-sorry infrastructure** → placed in same file, isolated by `section`.
2. **Whole-file zero sorry** → promote to main tree, then update `Verified.lean`. Target path is `Statlean/<MathArea>/<MathObject>.lean` where `<MathObject>` is a PascalCase math-object name (`Talagrand`, `BerryEsseen`, `RemainderTailOp`) — never a paper-section / theorem-number / chapter ref (`LemmaS3`, `Shao32`, `Thm411`, `MainTheorem`). The inner `namespace ...` and matching `end ...` must match the new path. The `/api/statlean/promote-to-statlib` server endpoint enforces this with `validateTargetName` — bad names are rejected before any disk write.
3. **Remaining sorry** → structured comment + `sorry_backlog.yaml` registration.

After any sorry-count change (completion of a prove subagent, extraction,
fresh skeleton write), regenerate the structured sorry list so the web
UI can render it without its own regex scan (roadmap A3):

```bash
python3 theme/scripts/extract_sorries.py \
    --sandbox "$SANDBOX" --output "$SANDBOX/sorry_list.json"
python3 theme/scripts/emit_event.py --sandbox "$SANDBOX" \
    artifact --kind-tag sorry-list --path sorry_list.json
```

The web UI's `JobRunner.onArtifact` replaces `job.sorryTargets` verbatim
from this JSON on every emit, so stale entries from earlier writes are
cleared automatically.

## Step 5.7: Knowledge Ingestion（自动）

对 Step 5 中成功证明的定理，收集 agent 返回的 `new_knowledge` YAML 块并入库：
```bash
python3 scripts/ingest_knowledge.py --input <agent_new_knowledge>
```
汇总多 agent 结果时做全局去重。

## Step 6: Sync Backlog & Gate

1. Run `python3 theme/scripts/sync_sorry_backlog.py` to reconcile code ↔ backlog
2. Run `bash theme/scripts/gate.sh` for full project build + sorry count + PIPELINE_ID check
3. Report metrics (time, tokens, sorry count before/after, knowledge entries added)
4. Commit with structured message

## Progress Reporting

After EACH step, report:
- Step name and status (PASS/FAIL)
- Key outputs
- Time estimate
- Any issues encountered

## Output Conventions (REQUIRED — web UI contract)

See `theme/conventions/ui-signals.md` for full specification.

You MUST announce each step in the report narrative with a line of the
exact form:

```
## Step N: <short title>
```

(two hashes, space, word `Step`, space, integer, colon, space, title).
The web UI's `StepBreakdown` panel parses these lines to render step
cards. Deviating (e.g. `Step 1:` without `## `, or `STEP` in caps,
or `## Step 1 - title` with a dash) makes that step invisible in the
UI. Fallback shapes `### Step N:` / `**Step N:**` / `# Step N:` are
tolerated but MUST NOT be introduced in new skills.

After completing a step, continue narrative on subsequent lines until
the next `## Step N:` marker. The UI treats everything between two
markers as that step's body and extracts an auto-headline (first
"Found" / "✓" / "Result:" line if present, else first line).

### Structured events (REQUIRED)

The `## Step N:` Markdown header is the human-readable signal — the UI
parses it as a fallback when structured events are absent. The
**canonical** signal for step/artifact/error state is the
`events.jsonl` stream described in `theme/conventions/ui-signals.md` §2,
populated via `theme/scripts/emit_event.py`.

For every pipeline job you MUST emit:

1. **One `step start` event** right before each step's main work:
   ```bash
   SANDBOX="$(dirname "$PDF_PATH")"   # derive from the PDF arg
   python3 theme/scripts/emit_event.py --sandbox "$SANDBOX" \
     step --id N --title "<short title>" --status start
   ```

2. **One `step done` event** when the step finishes successfully:
   ```bash
   python3 theme/scripts/emit_event.py --sandbox "$SANDBOX" \
     step --id N --status done
   ```
   (Use `--status error` instead if the step failed.)

   **Plus the matching `milestone` event** for the gate that step
   crossed. The milestone names are fixed (ui-signals.md §7); pair
   them 1:1 with `step done`:
   - Step 1 done → `--name pdf-extracted`
   - Step 2 done → `--name yaml-complete`
   - Step 3 done → `--name skeleton-locked`
   - Step 4 done → `--name lake-build-clean`
   - Step 5 done with `grep -c '\bsorry\b' = 0` across all targets → `--name sorry-zero`
   - Step 6 gate PASS → `--name proof-verified`
   ```bash
   python3 theme/scripts/emit_event.py --sandbox "$SANDBOX" \
     milestone --name <gate-name>
   ```
   Milestones are what `server/services/sandboxWatcher.ts` listens
   for — `proof-verified` paired with `lake-build-clean` and no
   `breaking` formalization_delta triggers the UI's "promote
   suggested" banner. Skip the milestone if the step errored.

3. **One `artifact` event** immediately after writing any file the UI
   should surface (paper.tex, theorems.yaml, Main.lean, sorry_list.json,
   ...). Use the relative path inside the sandbox; `--size` auto-stats
   from disk when omitted:
   ```bash
   python3 theme/scripts/emit_event.py --sandbox "$SANDBOX" \
     artifact --kind-tag <kind> --path <relative/path>
   ```
   Valid `<kind>` values: `pdf-extract`, `yaml`, `lean-skeleton`,
   `lean-live`, `sorry-list`, `sub-agent-result`.

4. **`error` events** for structured failures (instead of only prose):
   ```bash
   python3 theme/scripts/emit_event.py --sandbox "$SANDBOX" \
     error --code <CODE> --msg "<short message>"
   ```

Do not pre-emit the whole sequence at job start. Emit events as the
step boundaries are crossed in real time so the UI updates live.

The script is append-only with atomic POSIX semantics, so parallel
sub-agents (Phase 2 DAG dispatch) can emit concurrently without any
locking.
