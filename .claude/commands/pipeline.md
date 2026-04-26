---
description: Full pipeline — PDF theorem → Lean 4 formalization (extract → ingest → skeleton → prove → gate)
allowed-tools: Read, Edit, Write, Grep, Glob, Bash, Agent, Skill, Task, WebSearch, WebFetch
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
python3 theme/scripts/pdf_extract.py --pdf <pdf> --output-dir <dir> --backend mineru [--theorem <name>] [--pages <range>]

# Fallback if mineru is unavailable or the paper is text-only:
python3 theme/scripts/pdf_extract.py --pdf <pdf> --output-dir <dir> --backend pymupdf [...]
```

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
3. Design Lean signature (must reflect precise math content)
4. Place in appropriate `Statlean/` module
5. Build to verify skeleton compiles
6. Run honesty check (Step 6 of playbook): no trivial wrappers, no hidden sorry

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
  1. Read `theme/out/prove_targets.json`
  2. For each target (up to 3), launch a parallel Agent subagent with:
     - `subagent_type: "general-purpose"`
     - The `prompt` field from prove_targets.json
     - `model: "sonnet"` (good balance of speed and capability)
     - **prompt 必须包含 Phase 0.5 路线搜索 + Phase 0 工具链指令**：
       "Phase 0.5 路线搜索（在 API 搜索之前执行）:
        R1: 检查是否有 --roadmap 参数或用户提供的证明描述
        R2: {如果 Step 4.5 已解析出 roadmap → 直接注入: roadmap_yaml}
        R3: 读 theme/proof_knowledge.yaml 匹配 goal
        R4: 如果 R1-R3 无路线且等级 ≥ C → WebSearch '<theorem> proof Lean 4 Mathlib'
        R5: 自主探索（当前流程）
        Phase 0 工具链:
        先用 python3 scripts/extract_signatures.py 读声明索引，
        如果已有路线 → 按 key_api grep statlean_api_index.tsv 和 mathlib_full_type_index.tsv 查签名，跳过 mathlib_api_index 全文,
        未匹配 → 读 theme/mathlib_api_index.md + grep 两个索引，
        tactic 试错阶段用 bash scripts/check_snippet.sh 增量编译，
        每证完一个子引理立即写入 .lean 文件并 lake build 验证"
  3. Wait for all agents to complete
  4. For each target, verify sorry eliminated: `grep -c '\bsorry\b' <file>`
  5. If any target made progress but still has sorry, optionally re-dispatch
  6. Run `lake build <changed-modules>` (the same set Step 4 used — comma-list if multiple) to verify the touched modules still compile after prove edits. Do NOT run a bare `lake build` here; full-project verification is Step 6's job.

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
