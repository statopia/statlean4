---
description: Deep prove mode — DAG-driven work-stealing scheduler with 3 saturated agents
allowed-tools: Read, Edit, Write, Grep, Glob, Bash(lake:*), Bash(grep:*), Bash(echo:*), Bash(python3:*), Bash(git:*), Task, Agent, WebSearch, WebFetch, mcp__statlean_web_ui__request_user_decision
model: opus
argument-hint: [sorry-id from backlog, or "next" for highest priority, or "all-leaves"] [--time-budget Xh]
---

# Deep Prove Mode — DAG Event-Driven Scheduler

Target: $ARGUMENTS

**Time budget: configurable via `--time-budget` (default: 1h).**
This mode keeps 3 agents saturated, dispatching new work as soon as any agent completes.
When one sorry is proved → incremental commit → unlock downstream → dispatch next ready task.

**Timeout policy (hard enforcement):**
- **Soft deadline** = `--time-budget` (default 1h): stop dispatching new tasks.
- **Hard deadline** = soft deadline + 1h: force-stop all remaining agents via `TaskStop`,
  even if they haven't finished. Before stopping, dump their partial progress to
  `sorry_backlog.yaml` (mark as `stuck`, record last error / partial proof sketch)
  and update `MEMORY.md` with any patterns learned.
- This ensures every `/prove-deep` session terminates within 2× budget at most.

---

## Phase 0: Initialize DAG

0. **Cycle entry (MANDATORY, real bash)**:
   ```bash
   python3 theme/scripts/prove_deep_begin.py \
       --sandbox "$SANDBOX" --target "<TARGET>" --mode "<MODE>" \
       --time-budget-min <N>
   ```
   This emits `dispatch-batch-start` milestone with the ready_queue dump
   so the web orchestrator can derive Round/Step 8 framing and the user
   can see what's being attacked. **Do not skip** — the milestone is
   the only signal of cycle entry; consumers fail-closed when missing.

1. **Sync backlog**: Run `python3 theme/scripts/sync_sorry_backlog.py` to ensure
   `sorry_backlog.yaml` matches actual code.
2. **Load DAG**: Read `theme/input/sorry_backlog.yaml`. Build dependency graph:
   - Each sorry item has `dependencies[]` (what must be proved first) and `unlocks[]` (what becomes ready when this is proved).
   - **ready** = `dependencies` all proved or empty, AND `type != blocked` (or all blockers resolved).
   - **blocked** = has unresolved dependencies.
3. **Select targets** based on argument:
   - **Specific ID** (e.g., `efron_stein.condvar`): Attack that sorry directly (must be ready).
   - **`next`**: Pick the ready sorry with lowest priority number.
   - **`all-leaves`**: Attack ALL ready sorries via the DAG scheduler below.
4. **Priority queue**: Sort ready items by `priority` (lower = first).
5. **Parse time budget**: If `--time-budget 3h` specified, set deadline.

6. **H3 — library-coverage dispatch (czy port slice).** For each
   parent sorry_item where ALL of:

   - `state == INACTIVE_WAIT` (decomposed; has children)
   - At least one child has `coverage_state == "needs_proof"`

   ...dispatch the `helper-library-coverage` Task subagent
   (`theme/skills/helper-library-coverage/SKILL.md`) ONCE per parent.
   Provide sub-problem list (child ids + descriptions) as input:

   ```
   Theorem: <parent theorem name>
   Sub-problems to check:
   1. [<child_id>] <child theorem description>
   2. [<child_id>] <child theorem description>
   ...
   ```

   The subagent runs token-extract → `search_lemmas` tool calls →
   judge-LLM for each child; emits a JSON array to stdout. Capture
   to `$SANDBOX/_library_coverage_$PARENT_ID.json` and run:

   ```bash
   python3 theme/scripts/extract_library_coverage.py \
       --parent-id "$PARENT_ID" \
       --subagent-json-file "$SANDBOX/_library_coverage_$PARENT_ID.json" \
       --sandbox "$SANDBOX"
   ```

   The script writes `coverage_state: cited_by_library` + `library_hit:
   {name, source, location, kind}` on child items (Rule 3 Layer 1: only
   these two fields; `cited_by_reference` is protected — H3 never
   overwrites E4 territory). One `library-coverage-extracted` milestone
   fires per parent_id.

   **Multi-parent dispatch is parallel-safe** (extract_library_coverage
   uses flock + atomic write; same pattern as extract_references).

   **Failures fall through silently to step 7.** SKILL failure or JSON
   parse failure → no mutation; sorry stays `needs_proof` and continues
   through R6/R7 unchanged.

   **czy parity per `helperAgent.ts:245-273`**: czy's `runAlignment`
   runs library check (`checkLibraryCoverage`) FIRST, before reference
   check (`extractReferences`). This step ordering is preserved here:
   H3 (step 6) BEFORE R6 (step 7). czy filters library-covered
   sub-problems out of the reference check (`:276` short-circuit) — in
   SDK-bridge, R6 already skips children with `coverage_state ==
   cited_by_library`, so the same filter applies.

   **T-tier (Rule 9 §3)**: `extract_library_coverage.py` is T2 (single
   named script bundles all side effects); SKILL invocation is T3
   (narrative-driven Task dispatch). Empirical-adjustment escalation
   to T1 if real traces show INACTIVE_WAIT parents with needs_proof
   children but no `library-coverage-extracted` milestone at >25%
   skip rate.

7. **R6 — helper-reference dispatch (E4 slice port).** For each
   parent sorry_item where ALL of these hold:

   - `state == INACTIVE_WAIT` (already decomposed; has children)
   - `coverage_state` is currently `needs_proof` (H3 step 6
     library-coverage dispatch did NOT already mark it
     `cited_by_library`)
   - `pdfProofBody` is available in the sandbox (extracted by the
     latex-ingest / pdf-extract phase) AND its length ≥ 10 chars

   …dispatch the `helper-reference` Task subagent
   (`theme/skills/helper-reference/SKILL.md`) once per parent. The
   subagent emits a JSON array to its stdout; capture it to
   `$SANDBOX/_helper_reference_$PARENT_ID.json` and pipe through:

   ```bash
   python3 theme/scripts/extract_references.py \
       --parent-id "$PARENT_ID" \
       --subagent-json-file "$SANDBOX/_helper_reference_$PARENT_ID.json" \
       --pdf-proof-body-len $LEN \
       --sandbox "$SANDBOX"
   ```

   The script writes `references[]` / `coverage_state` /
   `coverage_citation` ONLY (Rule 3 Layer 1: signature/state/
   parent_id/children/history_log untouched). One
   `reference-extracted` milestone fires per parent_id.

   **Phase 2 control flow is UNCHANGED**: a parent receiving
   `coverage_state: cited_by_reference` is still attacked by the
   prover loop. R6 is annotation-only; promotion to `done` requires
   E11 `citationVerify` (separate slice). Per
   `docs/E4_REFERENCE_SUBAGENT_SPEC.md` §10 Q4, this is the
   conservative path — short-circuiting on an LLM-assessed citation
   would be a Rule 3 statement-integrity failure mode.

   Multi-parent dispatch IS parallel-safe (extract_references uses
   flock + atomic write); fan out via Task subagent concurrency.
8. **R7 — citation-verify dispatch (E11 slice port).** Run AFTER R6
   completes for the whole batch. Iterate eligible sorries in
   deterministic order — sorted by `id` ascending (lexicographic) —
   so L2 reproducibility holds. For each sorry whose
   `coverage_state ∈ {cited_by_library, cited_by_reference}`:

   **Library path** (`coverage_state == cited_by_library`):
   The cited Mathlib name comes from `library_hit.name` (written by
   step 6 H3 library-coverage dispatch). This branch is now ACTIVE
   on jobs where H3 found a match.
   Invoke:

   ```bash
   python3 theme/scripts/verify_citation.py \
       --mode library --sorry-id "<id>" \
       --cited-lemma "<Mathlib.Name>" \
       --sandbox "$SANDBOX"
   ```

   The script (T2 atomic): runs the 4-tactic ladder (`exact <name>`,
   `apply <name> <;> assumption`, `exact <name>.mp`,
   `exact <name>.mpr`); on FIRST PASS short-circuits and writes
   `state=DONE` + `done_reason=library_verified` + `citation_verified=true`;
   on FULL FAIL leaves the source tree byte-identical to its pre-call
   state and writes `citation_verified=false`. Body-level mutation
   only — Rule 3 Layer 1 invariant preserved (locked theorem
   signature untouched).

   **Reference path** (`coverage_state == cited_by_reference`):
   Dispatch the `citation-verify` Task subagent
   (`theme/skills/citation-verify/SKILL.md`) with the sub-problem's
   `original_description`, the `coverage_citation` (E4 wrote it
   stripped of the `-- cited from reference: ` prefix) as the
   `reference_theorem` input, and the `declarationText` (Lean
   signature). Capture stdout JSON to
   `$SANDBOX/_citation_verify_<id>.json`, then:

   ```bash
   python3 theme/scripts/verify_citation.py \
       --mode reference --sorry-id "<id>" \
       --subagent-json-file "$SANDBOX/_citation_verify_<id>.json" \
       --sandbox "$SANDBOX"
   ```

   On PASS: `state=DONE` + `done_reason=reference_axiom` +
   `citation_verified=true`. On FAIL (LLM verified=false OR malformed
   JSON): `citation_verified=false`; `coverage_state` preserved per
   §E11 D9. Reference path is **non-destructive** — never touches
   `.lean`.

   **Phase 1 + Phase 2 are NOT modified.** PASS-verified nodes enter
   Phase 2 already `state=DONE`; the existing "skip DONE" semantic in
   the LOOP picks them up naturally. FAIL nodes are attacked by the
   prover (per `docs/E11_CITATION_VERIFY_SPEC.md` §10 D8 — verifier-
   unsure does NOT skip; statement-integrity over throughput).

   One `citation-verified` milestone fires per invocation. Layer 4
   (`judge-integrity.ts`) at promotion time is the load-bearing audit
   on `reference_axiom` rows (E11 verifier is a soft signal; Layer 4
   has the trust pivot).

9. **M5 — auto_tactic pre-pass (czy port slice).** Run AFTER R7
   completes for the whole batch, BEFORE Phase 1 entry. ONE invocation
   per cycle — no per-sorry agent decision, no judgment loop. The
   script iterates the backlog itself.

   ```bash
   python3 theme/scripts/auto_tactic_pre_pass.py \
       --sandbox "$SANDBOX" \
       --statlean-root "$STATLEAN_ROOT" \
       --max-sorries 20
   ```

   The script (T2 atomic per eligible sorry; T3 at the narrative
   level — see docs/M5_AUTO_TACTIC_SPEC.md §10 D-5 for the honest
   tier framing): for each sorry with `state=INITIALIZED, no
   children, simple file, coverage_state ∉ {cited_by_library,
   cited_by_reference}`, runs the 9-tactic ladder
   (`rfl, trivial, decide, ring, linarith, omega, norm_num, simp,
   aesop` — czy `proofLoop.ts:1227` verbatim). First tactic that
   closes the goal short-circuits → `_try_tactic` mutates the body
   in place; `process_sorry_result.py --status proved
   --closer auto_tactic` writes `state=DONE / status=proved /
   done_reason=proved` and emits `sorry-proved` with `closer:
   auto_tactic`. Layer 1 invariant preserved (body-only mutation;
   `_try_tactic` reverts on FAIL).

   **Cost ceilings** (spec §8 R1; D-6 degraded mechanism vs czy's
   current LSP):
   - Complex-file skip: files mentioning any of `MeasureTheory /
     ProbabilityTheory / ENNReal / IsProbabilityMeasure /
     FiniteMeasure / StochasticProcess` (czy `:1218-1219` regex
     verbatim) are skipped — lake-build × 9 tactics is too slow on
     measure-theory contexts.
   - First-pass-wins: the ladder exits at the first PASS, not after
     all 9.
   - `--max-sorries 20`: per-cycle hard cap.
   - 60s per-tactic lake-build timeout (inherited from `_try_tactic`).

   **Failures fall through silently to Phase 1.** No mutation, no
   milestone, no error. The pre-pass is purely a cost-saver for
   trivial leaves; non-closeable sorries enter Phase 1
   decomposition / Phase 2 prover loop unchanged.

   **MUST run real bash — fail-loud on script error.** A non-zero
   exit indicates sandbox / backlog / IO failure; report it and do
   NOT enter Phase 1 with a half-applied pre-pass. (Per-sorry
   exceptions inside the ladder are handled by the script itself —
   they fall through to the next tactic; the script exits 0 in
   that case.)

---

## Phase 1: Sub-Task Decomposition (MANDATORY for complex sorry)

Decompose BEFORE launching prove agents when ANY of these apply:
- `estimated_lines > 150`
- The proof involves **3+ chained Mathlib APIs** (e.g., condExp + rnDeriv + setIntegral + pullout)
- The proof requires **MeasurableSpace instance juggling** (sub-σ-algebra, comap, trim)
- A previous agent attempt on this sorry was `stuck`

Decomposition steps:
1. Launch ONE research agent (haiku) to analyze the sorry goal + surrounding context.
2. Identify independent sub-lemmas (e.g., integrability, measurability, core equality).
3. Write sub-lemma declarations with sorry + compile-check them.
4. Call **`decompose_node.py`** to atomically register the children in the backlog
   (czy newloop port slice 3.A; replaces the older "manually edit yaml" recipe):
   ```bash
   python3 theme/scripts/decompose_node.py \
       --parent-id "<parent sorry id>" \
       --sub-problems-json '[{"id":"parent.sub1","theorem":"...","blocker":"..."},
                             {"id":"parent.sub2",...}]' \
       --decision-reason "<why this decomposition; will be stashed on parent
                          and surfaced in retreat history if children fail>" \
       --sandbox "$SANDBOX"
   ```
   The script (T2 atomic): inserts sub-rows with `state=INITIALIZED`, sets
   parent `state=INACTIVE_WAIT` + `children=[...]`, stashes `decision_reason`
   on the parent (consumed by record_retreat if children fail), emits
   `subtasks-split` milestone. **Locked theorem signature on the parent is
   never touched** (Rule 3 Layer 1 invariant — verified in unit tests).
5. **Refinement loop (slice 03 — czy parity)**: after `decompose_node.py`
   commits the initial children (Step A), wrap the decomposition with up to
   2 refinement rounds (Step B). czy `proofLoop.ts:807-920` runs this loop
   per-parent at decomposition time; SDK-bridge mirrors directly.

   Loop body (czy parity — `for alignRound = 0; alignRound < 3` maps to
   1 initial decompose + up to 2 refinements; cap = `informal_round >= 2`
   structurally enforced):

   ```
   WHILE parent.informal_round < 2
         AND parent.coverage_stable == false
         AND at least one child is non-converged
         (coverage_state ∈ {partial_coverage, needs_proof, no_coverage}
          OR (cited_by_* AND citation_verified == false)):

     Round body — for each parent eligible for refinement:

     a. Dispatch helper-reference SKILL (R6 — E4 helper-reference) on
        the current children. Idempotent re-run if children unchanged
        (E4 L2 idempotence test). NO citation-verify dispatch here —
        E11 R7 runs in Step C on converged children only (czy parity:
        czy's citationVerify.ts fires post-loop, never per-round; this
        avoids the lossy interaction where round-N R7 PASSes a child
        the round-N+1 refinement then drops).

     a.5. **R6.5 — alignment-phase alt-path detection (H2 detect_alt_path).**
        After R6 has populated `references[]` + `coverage_state` per
        child, optionally dispatch the `detect-alt-path` SKILL to
        determine whether the reference proof uses a fundamentally
        DIFFERENT and MORE EFFICIENT approach than the current
        decomposition. Fires ONCE per alignment cycle per parent —
        the G3 cache gate ensures subsequent rounds skip dispatch.

        **Gate checks (in order):**

        1. **G3 (cache):** `parent.alternative_path` non-null → skip
           dispatch; invoke `detect_alt_path.py --bypass-skill --gate-only`
           (script emits `verdict=cached` milestone). Continue to step b.

        2. **G2 (reference text):** `$SANDBOX/paper_body.txt` length
           < 10 chars after `.strip()` → skip dispatch; invoke with
           `--bypass-skill --gate-only` (G2 emits `no_reference_text`).
           czy parity per `helperReferenceSubAgent.ts:250-252`.

        3. **G1 (R6 output):** ≥1 child with non-empty `references[]`
           list → pass; otherwise skip dispatch with
           `--bypass-skill --gate-only` (G1 emits `no_reference_results`).
           czy parity per `helperAgent.ts:304` `referenceResults.length > 0`.

        **When all gates pass — dispatch the SKILL:**

        ```bash
        # Build user-message with 3 sections:
        #   "Reference proof text:\n${PDF_PROOF_BODY[:4000]}\n\n"
        #   "Current sub-problem decomposition:\n<list of children>\n\n"
        #   "Current plan coverage by reference:\n<per-child coverage + assessment[:200]>"
        # Dispatch detect-alt-path Task subagent; capture stdout to:
        ALT_PATH_FILE="$SANDBOX/_alt_path_${PARENT_ID}_$(date +%s%3N).json"

        python3 theme/scripts/detect_alt_path.py \
            --parent-id "$PARENT_ID" \
            --subagent-json-file "$ALT_PATH_FILE" \
            --sandbox "$SANDBOX" \
            --paper-body-path "$SANDBOX/paper_body.txt" \
            --backlog-path "$BACKLOG"
        ```

        **Outcome signals:**
        - `verdict=detected`: `parent.alternative_path` is now a non-null
          dict; slice 03's `refine_decomposition.py` (step c below) reads
          it and threads the 4-field reduced shape `{approach_name,
          description, key_tools, efficiency_reason}` into the
          informal-refine SKILL user-message under "## Alternative proof
          approach detected in reference" (czy `:1578-1583` reduction).
        - `verdict=no_alternative`: alt-path stays null; informal-refine
          continues without the alt-path section.
        - `verdict=cached | no_reference_results | no_reference_text`:
          gate-skip; non-fatal; alignment continues.
        - `verdict=parse_error | skill_dispatch_failed`: SKILL had a
          problem; alt-path stays null; alignment continues without it
          (czy parity: catch-all empty fallback at `:293-295`).

        **Reset hook:** `record_retreat.py` and `restrategize_node.py`
        reset `parent.alternative_path = None` alongside their other
        resets, so a new alignment cycle after retreat/restrategize
        re-detects fresh (D-7 architectural translation).

        **T-tier:** `detect_alt_path.py` is T2 (single named script
        bundles 3-gate check + JSON parse + atomic yaml write +
        milestone emit). SKILL invocation is T3 (narrative-driven Task
        dispatch). Empirical adjustment rule per Rule 9 §3 if drift
        observed in production.

     b. Dispatch informal-refine Task subagent
        (theme/skills/informal-refine/SKILL.md) with the helper
        feedback (per-child coverage_state + references[].assessment
        + replacement_statement). **CRITICAL**: when building the
        user message for the subagent, render each current child as
        `id: <yaml_row_id>     theorem: <theorem>     line: <N>     deps: [...]`
        with the yaml row id (e.g. `parent.s2`) — NOT just the
        theorem name. The script's `_diff_subproblems` matches by
        exact-string id; if the LLM uses theorem names instead of
        ids, the diff treats EVERY child as "removed + new" and
        wipes any verified citations. The SKILL prompt now includes
        an explicit "id stability rule" but the agent must still
        supply the ids in the rendering. Capture stdout JSON to
        $SANDBOX/_informal_refine_${PARENT_ID}_round_${N}.json.

     c. Pipe the JSON through refine_decomposition.py:

        python3 theme/scripts/refine_decomposition.py \
            --parent-id "<parent_id>" \
            --subagent-json-file "$SANDBOX/_informal_refine_${PARENT_ID}_round_${N}.json" \
            --sandbox "$SANDBOX"

        Script (T2 atomic): convergence pre-check (czy "all covered"
        exit), parses JSON, on noAdjustment → coverage_stable=true; on
        refined → diff applied (drop + descendants removed; add new
        children with INITIALIZED defaults; KEPT children's `theorem`
        UNTOUCHED — Layer 1 D-6); bumps informal_round. Emits one
        informal-round milestone with verdict ∈ {refined, noAdjustment,
        converged_pre_dispatch, cap_reached, parse_error}.

     d. Re-evaluate the WHILE condition based on the milestone verdict.
        cap_reached / converged_pre_dispatch / noAdjustment → loop exits.
        refined → loop continues to next round; round body re-dispatches
        R6 on the new children list.
   ```

   **Step C-pre — plan elaboration (H1, czy parity per
   `informalAgent.ts:477-513`).** After the slice 03 alignment loop
   exits — detected as
   `parent.coverage_stable == true OR parent.informal_round >= 2`
   (czy `proofLoop.ts:929-940` fires elaboratePlan UNCONDITIONALLY
   after the for-loop exits, regardless of whether it exited via
   noAdjustment / converged_pre_dispatch / cap_reached) — and BEFORE
   sub-autoformalize, dispatch the `elaborate-plan` Task subagent
   (`theme/skills/elaborate-plan/SKILL.md`). The SKILL has two modes:

   - **assembly mode** (parent has children — decomposed): emit a
     step-by-step proof plan that cites each child lemma in
     topological order. Closed children (`cited_by_*` /
     `state=DONE`) ARE enumerated by id (czy `:204-205`); the LLM
     cites them as "already covered" without re-proving.
   - **direct mode** (parent has no children — non-decomposed):
     emit a sketch of how to prove the parent directly, filtering
     to uncovered remaining sorries (czy `uncoveredFinal`
     `:927-932`).

   Inputs (built by the agent before dispatch): theorem name,
   lean_code excerpt, mode-specific child or remaining-sorries list,
   the parent's brief seed (`parent.direct_assembly` for assembly
   mode OR `parent.proof_sketch` for direct mode — both persisted
   by slice 03's patched scripts per H1 D-11), helper coverage
   feedback, gotchas, statlean_index.

   Capture the SKILL's stdout (plain text, NO JSON wrapping) to
   `$SANDBOX/_elaborate_plan_${PARENT_ID}.txt`, then:

   ```bash
   python3 theme/scripts/elaborate_plan.py \
       --parent-id "<parent_id>" \
       --mode "{assembly|direct}" \
       --subagent-text-file "$SANDBOX/_elaborate_plan_${PARENT_ID}.txt" \
       --sandbox "$SANDBOX"
   ```

   Verdicts: `elaborated` (plan written to `parent.detailed_proof_plan`),
   `skipped_already_present` (idempotence — non-null plan exists),
   `skipped_empty_plan` (LLM produced empty / whitespace — yaml
   stays None; prover falls back to brief seed per czy `:1120`
   fallback chain `detailedProofPlan ?? directAssembly ?? proofSketch`).
   One `plan-elaborated` milestone per dispatch.

   Layer 1: script mutates ONLY `detailed_proof_plan`. Strictest
   single-field write of any port slice.

   **Step C — final commit + post-loop verification**: after the loop
   converges (and H1 elaboration has fired), sub-autoformalize
   fires on the FINAL children (existing flow); Layer 1 signature
   locks apply to FINAL signatures only. Then E11 R7 (citation-
   verify) dispatches per spec §6.1 on the converged children.
   PASS-verified children get state=DONE + done_reason and bypass
   Phase 2 prover.

6. The parent enters INACTIVE_WAIT and exits the ready queue automatically;
   sub-lemmas become the new leaves the next ready_queue computation picks up.

**Rationale**: Agents that discover decomposition ad-hoc waste cycles on instance
resolution and type-juggling. Pre-decomposition isolates each API interaction into
a focused sub-goal, dramatically improving agent success rate. The refinement loop
(steps 5a-5d) gives the InformalAgent up to 2 chances to adjust the decomposition
based on what helper-reference found — closing the alignment-quality gap that
slice 03 ports from czy.

Skip step 5 (refinement loop) only for genuinely simple decompositions where the
agent is confident at round 0. Skip steps 1-5 entirely for genuinely simple sorry
(single tactic, obvious API — no decomposition needed).

---

## Phase 2: Tree-Walker Scheduling Loop (CORE — czy newloop port)

### Pitfalls knowledge base

<!-- Source: website-czy/src/lib/orchestrator/honestyRules.ts:261-274 (LEAN_KB_REFERENCES) + PITFALL_FILES rendered inline — byte-equal -->

These files are KB-preloaded; `read_file path="docs/pitfalls/<name>.md"`
is instant. Each covers one or two related error categories. Read the
relevant file BEFORE writing on any non-trivial Lean construct, and
ALWAYS read the file the routing hint points at when a write fails.

| File | Topic |
|---|---|
| `docs/pitfalls/README.md` | Index + error→file:§ routing table. |
| `docs/pitfalls/lean_syntax_errors.md` | Parser, lexer, elaboration errors (unexpected token, type mismatch, exact failed, no goals). |
| `docs/pitfalls/typeclass_errors.md` | Instance synthesis failures, OrderBot ℝ, heartbeat timeouts, termination. |
| `docs/pitfalls/instance_pollution.md` | Multiple MeasurableSpace Ω instances — the dominant CE-proof failure mode. |
| `docs/pitfalls/measure_theory_patterns.md` | Templates: condExpWith, 3-condition uniqueness, set-integral, AE patterns, σ-algebra plumbing, indicator rewriting. |
| `docs/pitfalls/statistics_domain.md` | Distributions (gaussianReal, expMeasure), variance, IndepFun, matrix algebra, OLS skeleton, convergence. |
| `docs/pitfalls/mathlib_style.md` | Promotion-grade style: header, naming, line-length, calc, binders, pre-submit checklist. |

When in doubt, the README acts as the master index:
`read_file path="docs/pitfalls/README.md"`.

If a write/edit fails, `last_wrong_attempt.lean` is saved in the
sandbox root. Re-read it next turn to see the broken code with error
markers at the exact failing lines and pitfall routing hints in the
footer. Call `read_file path="last_wrong_attempt.lean"` immediately
after any WRITE-FAIL / EDIT-FAIL / REPLACE-FAIL before retrying.

On WRITE-FAIL / EDIT-FAIL:
1. Call process_sorry_result.py with `--status write_fail` or `--status edit_fail`:
   ```bash
   python3 theme/scripts/process_sorry_result.py \
       --sandbox "$SANDBOX" --sorry-id "<id>" \
       --status write_fail \
       --blocker "<first error line>" \
       [--content <tempfile>] [--diagnostics '<json>']
   ```
   This T1-bundles: `save_last_wrong_attempt.lean` write + `"last-wrong-attempt-saved"` emit.
2. Call `read_file path="last_wrong_attempt.lean"` immediately to see the
   annotated broken code with error markers + pitfall routing hints.
3. If a 📚 ROUTING HINT appears in the summary, call
   `read_file path="docs/pitfalls/<name>.md"` before retrying.

On REPLACE-FAIL (Phase 03 stub):
1. Call process_sorry_result.py with `--status replace_fail`:
   ```bash
   python3 theme/scripts/process_sorry_result.py \
       --sandbox "$SANDBOX" --sorry-id "<id>" \
       --status replace_fail \
       --blocker "<first error line>"
   ```
   (Phase 03: logs a warning "replace_fail last-wrong-attempt deferred to Phase 04".
    No last_wrong_attempt.lean written for `mcp__statlean_prove__replace_sorry` failures in this phase.)


The scheduling model is the **decision tree** ported from czy's
`proofState.ts` + `controlAgent.ts` (replacing the prior flat-DAG queue).
Every sorry_item has a `state` ∈ {INITIALIZED, INACTIVE_WAIT, ACTIVE_PROVING, DONE}
and a `parent_id` (None for top-level). Decomposition turns a parent into
INACTIVE_WAIT with `children` populated; retreat clears the children and
returns the parent to INITIALIZED with a `history_log` entry.

**Ready-queue rule** (recomputed every iteration; replaces the static
priority-sorted queue):

```
A node is ready iff state == "INITIALIZED" AND either:
  (a) parent_id is None AND every dep in dependencies has status="proved"
      (top-level: classic DAG-style cross-sorry dependency)
  OR
  (b) parent_id is not None AND parent_id's state == "INACTIVE_WAIT"
      (sub-problem: parent suspended pending us)

Order ready_queue by priority (higher first), break ties on insertion order.
```

```
MAX_SLOTS = 3
active_agents = {}   # {task_id → sorry_id}
start_time = now()

# NOTE: dispatch-batch-start milestone was emitted at Phase 0 step 0
# via prove_deep_begin.py. Don't re-emit here.

LOOP:
  # ── Compute ready_queue dynamically (czy tree-walker semantics) ──
  ready_queue = compute_ready_queue(sorry_backlog)   # see rule above

  # ── Fill slots to MAX_SLOTS ──
  while len(active_agents) < MAX_SLOTS and ready_queue is not empty:
    sorry = ready_queue.pop(0)
    agent = launch_background_agent(sorry)
    active_agents[agent.task_id] = sorry.id
    set sorry.state = "ACTIVE_PROVING" in backlog

  # ── If no active agents and no ready tasks → done ──
  if active_agents is empty:
    break

  # ── Poll for completion (non-blocking round-robin) ──
  for each task_id in active_agents:
    result = TaskOutput(task_id, block=false)
    if result is complete:
      sorry_id = active_agents.pop(task_id)
      process_result(sorry_id, result)
      # After processing, loop back to fill slots immediately
      goto LOOP

  # ── Check time budget ──
  if soft_deadline exceeded:
    stop dispatching new tasks (but keep polling active agents)
  if hard_deadline exceeded (soft + 1h):
    for each active agent:
      TaskStop(task_id)
      record partial progress in sorry_backlog.yaml (status: stuck)
    break

  # ── Brief pause then re-poll ──
  (poll again immediately — TaskOutput block=false is ~zero cost)
```

### `launch_background_agent(sorry)` — Agent Prompt Template

For each sorry, launch a background Agent with `subagent_type: "general-purpose"`,
`run_in_background: true`. **Before constructing the prompt, check if this sorry
has prior-attempt history** (czy newloop port — `informalAgent.ts:741-763`):

```bash
# If sorry.history_log is non-empty (i.e., this sorry was retreated
# from at least once before), prepend the history block to the agent
# prompt so the LLM sees what was tried and can pick a DIFFERENT
# decomposition strategy.
HISTORY=$(python3 theme/scripts/read_history_log.py \
              --node-id "<sorry.id>" \
              --backlog-path theme/input/sorry_backlog.yaml)
# HISTORY is empty string if no history. Only prepend when non-empty
# (else we'd waste prompt tokens on a blank line):
if [ -n "$HISTORY" ]; then
    PROMPT_PREFIX="${HISTORY}\n\n"
else
    PROMPT_PREFIX=""
fi
```

The output (when non-empty) follows czy's exact format:

```
## Previous attempt history (DO NOT repeat failed strategies)
- Iteration N: decomposed into [...]
    Reason: <decision_reason>
  - <sub_id>: stuck (<fail_reason>)
  Retreat reason: <reason>
ACTION: Choose a DIFFERENT decomposition strategy from previous attempts.
```

Prepend this block to the body that follows.

**Detailed proof plan injection (H1, czy parity per
`proverAgent.ts:570-572`).** If the sorry's parent — i.e. for a
sorry produced by Phase 1 decomposition, the parent of the sorry's
sorry_item — has a non-null `detailed_proof_plan` field (written
by H1's `elaborate_plan.py` at Step C-pre), prepend a guidance
block ABOVE the goal statement. czy's prover treats the elaborated
plan as PRIMARY guidance (not just additional context). Fallback
chain matches czy `:1120`:
`detailed_proof_plan ?? direct_assembly ?? proof_sketch`. If none
are set (e.g. flat top-level sorry with no decomposition), no
guidance block is added.

```bash
# §8 review S2.8 fix: use $BACKLOG env var (set by orchestrator) for
# absolute-path resilience, and shell-interpolate ${SORRY_ID} OUTSIDE
# the python -c body so a literal "<sorry.id>" can't silently
# fall through (which would degrade to empty plan).
BACKLOG="${BACKLOG:-theme/input/sorry_backlog.yaml}"
SORRY_ID="<sorry.id>"   # ← Agent MUST template-substitute this with
                        #   the actual sorry id BEFORE invoking the
                        #   block; literal "<sorry.id>" produces empty
                        #   plan (defensive: see PLAN check below).
PLAN=$(SORRY_ID="$SORRY_ID" BACKLOG="$BACKLOG" python3 -c "
import os, yaml
backlog_path = os.environ['BACKLOG']
sorry_id = os.environ['SORRY_ID']
data = yaml.safe_load(open(backlog_path))
items = {it['id']: it for it in data.get('sorry_items', [])}
sorry_item = items.get(sorry_id, {})
parent_id = sorry_item.get('parent_id')
parent = items.get(parent_id, {}) if parent_id else sorry_item
plan = (parent.get('detailed_proof_plan')
        or parent.get('direct_assembly')
        or parent.get('proof_sketch')
        or '')
print(plan)
")
if [ -n "$PLAN" ]; then
    PLAN_PREFIX="## Detailed proof plan (Informal Agent — use this as primary guidance)\n\n${PLAN}\n\n"
else
    PLAN_PREFIX=""
fi
```

Inject `$PLAN_PREFIX` into the prompt body BEFORE the `目标:` line,
AFTER the `$PROMPT_PREFIX` history block. So the order is:
HISTORY (if any) → PLAN (if any) → goal statement → Phase 0.5
narrative.

The agent prompt body:

```
{HISTORY block prepended here when sorry.history_log is non-empty}

{PLAN block prepended here when parent has detailed_proof_plan / brief seed}

目标: 证明 {sorry.theorem} (文件 {sorry.file}:{sorry.line})
Goal type: [read from file]
{如有路线: "路线已获取（来自 R1/R2/R3/R4），按路线执行：\n" + roadmap_yaml}

Phase 0.5 路线搜索 (在 API 搜索之前执行):
  0. 如果主会话已提供路线（见上方 roadmap）→ 直接按路线 key_api 查签名，跳过后续搜索
  1. 否则：先读 theme/proof_knowledge.yaml 查找与当前 goal 匹配的 L3 strategy / L2 chain / L1 tip
     - 注意 anti: true 条目 = 不要走这条路（如 Stein identity 不给 LSI）
  2. 如果 R3 仍无路线，且 sorry 等级 ≥ C，且定理是已知数学结果：
     - WebSearch "<theorem_name> proof Lean 4 Mathlib"（快速探测，~3-5K token）
     - 有 Lean 形式化 → WebFetch 提取 API 名称
     - 有 ProofWiki/教材证明 → WebFetch 获取骨架
     - 无结果 → 停止 Web 搜索，进入自主探索

Phase 0 工具链 (强制):
  0. 用 python3 scripts/extract_signatures.py {sorry.file} 读声明索引，定位目标行号后再 Read 指定范围（不盲读全文件）
  1. 如果 Phase 0.5 已获得路线 → 按 key_api 定向 grep 查签名（省 8.5K token）:
     - StatLean API: grep -i '<name>' theme/statlean_api_index.tsv
     - Mathlib API: grep -i '<name>' theme/mathlib_full_type_index.tsv
  2. 如果未匹配 → 读 theme/mathlib_api_index.md + grep 两个索引
  3. 仍未找到 → #check / exact?
  4. 最后手段: grep Mathlib 源码 (必须注明升级理由)

增量编译:
  - tactic 试错阶段: bash scripts/check_snippet.sh {sorry.file} <start> <end>
  - 全模块验证: lake build Statlean.{Module}

## Available write tools (Phase 2 priority order)

<!-- czy parity per proverAgent.ts:268-270 (3 write-tool bullets verbatim).
     Path A inline (Phase 03 §8 follow-up via Batch B spec review S3.1):
     czy interpolates these via TS template literal into prover prompt;
     SDK-bridge inlines directly into launch_background_agent body. -->

<!-- W2.S4 (2026-05-01): prove-side tools live under the SDK MCP server
     `statlean_prove`. Their tool catalog names use the SDK prefix:
     `mcp__statlean_prove__<bare_name>`. The bullet items below show
     both names; agents calling the tool MUST use the prefixed form
     (it's the only entry in the tool list). The bare name is kept
     in prose for readability + cross-reference to the legacy
     /api/tool-exec catalog in src/lib/tools.ts. -->

- `mcp__statlean_prove__replace_sorry` (alias `replace_sorry`) — **preferred** for closing a single sorry — replace one sorry with a tactic; auto-verifies and reverts on failure
- `mcp__statlean_prove__edit_lines` (alias `edit_lines`) — replace a specific line range (`start_line`..`end_line`); `new_content` may have any number of lines including zero, so it can grow, shrink, or delete the range. Auto-verifies and reverts on failure (returns [EDIT-OK] / [EDIT-FAIL]). Use this for localized rewrites — adding helpers above the theorem, fixing a few mid-proof lines, deleting dead branches — instead of retyping the whole file.
- `mcp__statlean_prove__write_file` (alias `write_file`) — full file rewrite (last resort, expensive in output tokens); auto-verifies and reverts on failure (returns [WRITE-OK] / [WRITE-FAIL])

Note: heavy read/search tools are NOT available in proof-writing phase. `lean_local_search` and `mcp__statlean_prove__lean_loogle` (alias `lean_loogle`) are available for on-demand lemma lookup when you encounter an unknown API or a sorry that Phase 0 research didn't cover.

## Anti-trivial-witness rule

<!-- czy parity verbatim per honestyRules.ts:148-149 (PROOF_WITNESS_HONESTY_RULE).
     Phase 03 §8 follow-up via Batch B spec review S3.1: moved from
     proof-closure/SKILL.md to here per Path A (czy template-literal interpolation
     parity; SKILL fold introduced SDK-bridge-specific indirection czy doesn't have). -->

- Do NOT pick trivial witnesses for `∃` goals that vacuously discharge the conclusion. Specifically: `μ := 0` (zero measure) for `∃ μ, ∀ᵐ _ ∂μ, _` collapses via `MeasureTheory.ae_zero`; `s := ∅` for `∃ s, ∀ x ∈ s, _` is vacuous; `f := fun _ => 0` for a non-trivial random variable / estimator is a stub; `C := 1` (or any value) when the predicate body reduces to `True` via your refine. The witness MUST be the object the source mathematics specifies (the noise measure, the OLS estimator, the limit point). If that witness is not visible in the hypotheses, leave the sorry with a `-- blocker:` comment instead of substituting a trivial fill-in.

## Identifier naming (LaTeX-style ASCII for math symbols)

<!-- czy parity verbatim per honestyRules.ts:162-200 (LEAN_NAMING_CONVENTION).
     Same Path A migration as above. -->

When the source math uses one of these symbols, **always** write the ASCII transliteration as the Lean identifier. Raw Unicode causes lexer failures that are hard to debug.

### HARD BAN: `λ` `Π` `Σ` `∀` `∃` (Lean reserved keywords)

These five characters are **reserved keywords** (lambda binder, dependent function/sigma type, universal/existential quantifier). They MUST NOT appear ANYWHERE inside an identifier — not as the whole name, not as a prefix/suffix, **not embedded in a compound name**. The Lean lexer cuts the identifier at the keyword and reports `unexpected token` at that column.

Common embedded mistake — these all FAIL to parse:

| Mistake | Why it fails | Fix |
|---|---|---|
| `hλ_pos` (hypothesis name) | `λ` mid-identifier ends `h` early; parser expects `)` | `hlambda_pos` |
| `Σ_inv` (covariance inverse) | `Σ` starts a sigma-type token | `Sigma_inv`, `covInv` |
| `Πₖ` (product symbol) | `Π` starts a Pi-type token | `Pi_k`, `prod_k` |
| `∀_intro` / `∃_witness` | quantifier symbols are keywords | `forall_intro` / `exists_witness` |

Rule of thumb: before you `mcp__statlean_prove__write_file`, **grep your own draft for the five characters `λ Π Σ ∀ ∃`** — if any appears inside a name (i.e. adjacent to a letter, digit, or `_`), rename to ASCII.

### LaTeX-style transliteration table (other symbols)

| LaTeX in source | DON'T write | DO write |
|---|---|---|
| `\lambda` (eigenvalue, Lagrange mult.) | `λ` (keyword) | `lambda`, `lam`, `eigval` |
| `\Pi` / `\Sigma` (covariance, etc.) | `Π` / `Σ` (keywords) | `Pi`, `Sigma`, `Sigma_mat`, `covMat` |
| `\hat{\beta}`, `\hat{\theta}` | `β̂`, `θ̂` (combining mark) | `hat_beta`, `hat_theta` |
| `\tilde{x}`, `\bar{X}` | `x̃`, `X̄` (combining mark) | `tilde_x`, `bar_X` |

**Always safe** (precomposed, not keywords): `α β γ δ ε ζ η θ ι κ μ ν ξ π ρ τ φ χ ψ ω` (note: `λ Π Σ` are excluded), subscripts `β₀ x₁ ε_n`, superscripts `x² ε⁺ X⁻¹`.

## Quick error reference (try these BEFORE searching APIs)

<!-- czy parity per honestyRules.ts:209-248 (LEAN_QUICK_ERROR_TABLE) — body byte-equal; heading adapted (czy heading is "Phase 2 — Quick error reference"; SDK-bridge drops "Phase 2 — " prefix because the surrounding context already establishes Phase 2). Per Batch B §8 code review S2.3/S4.1 fixup 2026-04-30. -->-

When `mcp__statlean_prove__{write_file,edit_lines,replace_sorry}` returns an error, scan this table FIRST. If the pattern matches, apply the right-column fix immediately. The right-most column also points at `docs/pitfalls/<file>.md` sections — read those when the inline fix isn't enough.

The tool result for any failed write also carries a `📚 ROUTING HINT` block automatically — that block names the matching file:§section explicitly, so prefer reading the indicated file over guessing.

| Error pattern | First action | Detail file |
|---|---|---|
| `unexpected token 'λ'` / `'Π'` / `'Σ'` / `'∀'` / `'∃'` | Reserved keyword in identifier (standalone OR embedded — e.g. `hλ_pos`, `Σ_inv`). Rename **every** occurrence to ASCII (`λ`→`lambda`, `Π`→`Pi`, `Σ`→`Sigma`, `∀`→`forall`, `∃`→`exists`). | `docs/pitfalls/lean_syntax_errors.md` §A.1 |
| `unexpected token 'in' / 'and' / 'or' / 'not'` | English-word operator. Use Lean ops: `∈`, `∧`, `∨`, `¬`. | `docs/pitfalls/lean_syntax_errors.md` §A.2 |
| `unexpected token 'theorem'/'def'/'lemma'` mid-file | Previous declaration unclosed — count parens 5–20 lines above. | `docs/pitfalls/lean_syntax_errors.md` §A.3 |
| `Unknown identifier 'X'` + auto-bound implicit Note | X used as binder before declaration. Move declaration before use site. | `docs/pitfalls/lean_syntax_errors.md` §A.4 |
| `expected token` on `β̂` / `X̄` / `x̃` etc. | Combining mark in identifier. Rename to ASCII (`β̂`→`hat_beta`, `X̄`→`bar_X`). | `docs/pitfalls/lean_syntax_errors.md` §A.6 |
| `unknown identifier '<name>'` (Tendsto, atTop, 𝓝, IndepFun, condExp) | Missing `open`. Add `open Filter Topology MeasureTheory ProbabilityTheory ENNReal`. | `docs/pitfalls/lean_syntax_errors.md` §B.9 |
| `unknown identifier '<name>'` (gaussianVolume, expectation, Variance) | API does NOT exist — guessed name. Real names: `gaussianReal`, `variance`. `mcp__statlean_prove__check_type` first. | `docs/pitfalls/statistics_domain.md` §B |
| `type mismatch (ℕ vs ℝ)` | Coerce: `(n : ℝ)` or `↑n`. | `docs/pitfalls/lean_syntax_errors.md` §B.2 |
| `tactic 'exact' failed, type mismatch` | Try `apply`, or use `refine ?_` to inspect expected type. | `docs/pitfalls/lean_syntax_errors.md` §B.3 |
| `no goals to be solved` | Previous tactic already closed it — delete the redundant tactic. | `docs/pitfalls/lean_syntax_errors.md` §B.6 |
| `failed to synthesize OrderBot ℝ` (Finset.sup) | Use `⨆ j : Fin p, f j` instead, or `Finset.sup'` with nonempty proof. | `docs/pitfalls/typeclass_errors.md` §A.1 |
| `failed to synthesize IsProbabilityMeasure μ` / `IsFiniteMeasure` | `haveI : IsProbabilityMeasure μ := ⟨measure_univ⟩`. | `docs/pitfalls/typeclass_errors.md` §A.2 |
| `failed to synthesize Integrable f μ` | Add hypothesis `(hf : Integrable f μ)` or derive via `Integrable.of_bound`. | `docs/pitfalls/typeclass_errors.md` §A.4 |
| `synthesized type X, inferred type inst✝N` (sub-σ-algebra) | Multiple MeasurableSpace Ω in scope. Pin ambient with `let m0 := ‹_›` and `@` annotate ambient facts. | `docs/pitfalls/instance_pollution.md` (whole file) |
| `(deterministic) timeout` / 500k heartbeats | Use three-tier strategy for sub-σ-algebras, or `set_option maxHeartbeats 800000 in`. | `docs/pitfalls/typeclass_errors.md` §B.2 |
| `unexpected identifier; expected command` after `/-! ... -/` | Section comment terminated proof — replace with `-- ...` line comment. | `docs/pitfalls/lean_syntax_errors.md` §A.5 |
| Error line N seems "wrong" / unrelated | Check 5-20 lines BEFORE line N (elaboration fails downstream of the actual mistake). | `docs/pitfalls/lean_syntax_errors.md` §B.1 |

**Working with conditional expectation / sub-σ-algebra?** Pre-read `docs/pitfalls/instance_pollution.md` BEFORE writing — it documents the single biggest source of wasted turns on CE proofs.

**If your error doesn't match any row above**, the failed-attempt tool result already includes a routing hint when one matches. If not, browse `docs/pitfalls/README.md` (the file index) and pick the file whose topic best matches your error.

## Pitfalls knowledge base (`docs/pitfalls/`)

<!-- czy parity verbatim per honestyRules.ts:261-274 + PITFALL_FILES rendered.
     Phase 03 already inlined this in Phase 2 preamble (line ~490);
     replicating here in launch_background_agent prompt body so the prover
     sub-agent (general-purpose, no SKILL invocation) actually sees it. -->

These files are KB-preloaded; `read_file path="docs/pitfalls/<name>.md"` is instant. Each covers one or two related error categories. Read the relevant file BEFORE writing on any non-trivial Lean construct, and ALWAYS read the file the routing hint points at when a write fails.

| File | Topic |
|---|---|
| `docs/pitfalls/README.md` | Index + error→file:§ routing table. |
| `docs/pitfalls/lean_syntax_errors.md` | Parser, lexer, elaboration errors (unexpected token, type mismatch, exact failed, no goals). |
| `docs/pitfalls/typeclass_errors.md` | Instance synthesis failures, OrderBot ℝ, heartbeat timeouts, termination. |
| `docs/pitfalls/instance_pollution.md` | Multiple MeasurableSpace Ω instances — the dominant CE-proof failure mode. |
| `docs/pitfalls/measure_theory_patterns.md` | Templates: condExpWith, 3-condition uniqueness, set-integral, AE patterns, σ-algebra plumbing, indicator rewriting. |
| `docs/pitfalls/statistics_domain.md` | Distributions (gaussianReal, expMeasure), variance, IndepFun, matrix algebra, OLS skeleton, convergence. |
| `docs/pitfalls/mathlib_style.md` | Promotion-grade style: header, naming, line-length, calc, binders, pre-submit checklist. |

When in doubt, the README acts as the master index: `read_file path="docs/pitfalls/README.md"`.

约束:
  - 只修改 {sorry.file}
  - 最多 5 轮 build 循环
  - 每轮: 尝试证明 → build → 分析错误 → 修复
  - 每证完一个子引理立即写入 .lean 文件并 lake build 验证，不要攒到最后一起写
  - **API 名称错误快速修复**: 如果 build 报 `unknown identifier` 或 `unknown constant`:
    1. 先查 `grep -i '<name>' theme/api_gotchas.tsv`（秒级，~12 条高频坑）
    2. 命中 → 按 correct_api 替换
    3. 未命中 → `grep -i '<name>' theme/mathlib_full_type_index.tsv`（51K 条）
    4. 仍未命中 → API 可能真不存在，考虑替代路线
    不要猜第二个名字直接写代码。
完成后报告:
  - status: proved | stuck | need_sub_lemma
  - 如果 stuck: 说明卡在哪里 (缺 API / 类型不匹配 / 策略不对)
  - 如果 need_sub_lemma: 列出需要的 sub-lemma 签名
  - 如果有新 pattern（正面或负面）: 输出 new_knowledge YAML 块供主会话入库
    （主会话收到后用 `python3 scripts/ingest_knowledge.py --input <file>` 标准流程入库）
    new_knowledge:
      - level: L3/L2/L1
        trigger: "<goal 形状>"
        strategy/chain/tip: "<内容>"
        workflow: "<证明组织方式（可选，见下）>"
        anti: true/false    # true = 不要走这条路
        confidence: <3-5>
  - **效率反思（build 循环 ≥ 5 轮时强制）**:
    回顾哪些轮次是重复劳动（同类错误反复出现），提取 workflow pattern：
    不是"用了什么 API"，而是"证明应该怎么组织以避免试错"。
    将 workflow pattern 写入 new_knowledge 的 workflow 字段。
    例: workflow: "先用 have 块建立所有子项的 Integrable/MemLp，再组装 integral_add/sub rewrite 链"
```

### `process_result(sorry_id, result)` — Result Handler

```
Each terminal branch ends with `process_sorry_result.py` (real bash,
MANDATORY for proved/stuck/lake_build_fail). The need_sub_lemma branch
DOES NOT use process_sorry_result anymore — it calls validate_decomposition
+ decompose_node directly (decompose_node carries the sorry_list-refresh
+ sorry-pool-snapshot emit responsibility internally so the telemetry
invariant is preserved across this fork).

process_sorry_result.py bundles for proved/stuck/lake_build_fail:
backlog status update + sorry_list.json refresh + per-status milestone +
sorry-pool-snapshot telemetry + (proved branch only) cascade DONE
propagation upward via propagate_done.py. Skipping any individual step
breaks downstream consumers — bundling makes that structurally impossible.

```bash
python3 theme/scripts/process_sorry_result.py \
    --sandbox "$SANDBOX" \
    --sorry-id "<sorry_id>" \
    --status "proved|stuck|need_sub_lemma|lake_build_fail" \
    --module "Statlean.<Module>" \
    --lean-file "<path/to/file.lean>" \
    [--blocker "<one-line>"] \
    [--children-decomposition '<JSON>'] \
    [--parent-metrics '<JSON>']
```

```
if result.status == "proved":
  1. lake build Statlean.<Module>  — incremental verify
  2. if build OK:
     - Check whole-file zero sorry → update Verified.lean
     - git add + commit "prove: {theorem_name}"
     - Call process_sorry_result.py --status proved --sorry-id ... --module ...
       (czy newloop port: process_sorry_result internally also sets
        state=DONE + done_reason=proved AND calls propagate_done.py to
        cascade DONE up the tree. The next ready_queue computation will
        automatically pick up any newly-eligible nodes — no manual
        unlocks/dependencies handling needed in this branch.)
  3. if build FAIL:
     - Log error, mark sorry as pending, priority += 3
     - Call process_sorry_result.py --status lake_build_fail --sorry-id ... --blocker ...

if result.new_knowledge:
  - 将 new_knowledge YAML 块写入临时文件（如 /tmp/new_knowledge_{sorry_id}.yaml）
  - run("python3 scripts/ingest_knowledge.py --input /tmp/new_knowledge_{sorry_id}.yaml")
  - 脚本自动：验证 level/trigger/confidence → 去重 → 追加到 proof_knowledge.yaml → 输出摘要

elif result.status == "stuck":
  - Mark sorry as pending
  - Increase priority by 5 (deprioritize)
  - Log blocker info for future reference
  - Call process_sorry_result.py --status stuck --sorry-id ... --blocker ...
    (czy newloop port: process_sorry_result internally bumps stuck_rounds
     by 1; this is the field record_retreat thresholds against.)
  - **Two-counter stuck gate** (czy newloop port + A1 — see
    `controlAgent.ts:604-614` and `docs/A1_RESTRATEGIZE_SPEC.md` §7):
    Re-read the parent (parent_id of the failed sorry) from the backlog
    and apply this discrimination on `parent.attempts` and
    `parent.stuck_rounds`:

    1. **If `attempts >= 3` → call `record_retreat.py`** (decomposition
       itself wrong; full reset, attempts→0):

       ```bash
       python3 theme/scripts/record_retreat.py \
           --parent-id "<parent_id>" \
           --retreat-reason "attempts reached 3; decomposition exhausted" \
           --results-json '[{"sub_problem_id":"<sorry_id>","status":"stuck",
                             "fail_reason":"<blocker, sliced 200 char>"}]' \
           --sandbox "$SANDBOX"
       ```

       Bundles: removes ALL descendants, resets parent state→INITIALIZED,
       stuck_rounds→0, **attempts→0**, children→[], appends HistoryLogEntry
       with full retreat context, emits `retreat-triggered`.

    2. **Else if `stuck_rounds >= 3` → call `restrategize_node.py`**
       (proof STRATEGY wrong; preserve decomposition strategy via
       attempts++ bookkeeping):

       ```bash
       python3 theme/scripts/restrategize_node.py \
           --parent-id "<parent_id>" \
           --sandbox "$SANDBOX"
       ```

       Bundles: removes ALL descendants (parent stays — D-2 deviation
       per A1 spec §2.3), resets parent state→INITIALIZED,
       stuck_rounds→0, children→[], **bumps parent.attempts**, appends
       HistoryLogEntry with structured `retreat_reason: "restrategize:
       cleared N children, M proved"`, emits `restrategize-triggered`.

       The script enforces the gate at script level too: refuses if
       attempts >= 3 (caller should retreat instead). One less footgun.

    3. **Else if `stuck_rounds >= 1` → dispatch_helper flow** (czy
       parity per `controlAgent.ts:604-614` else-branch; per
       `docs/H4_DISPATCH_HELPER_SPEC.md` §6.1 + D-5):

       This rung fires on EVERY stuck below the retreat/restrategize
       thresholds (i.e. `attempts < 3` AND `stuck_rounds < 3`). It
       gives helpers up to 3 chances — once each at `stuck_rounds=1`,
       `=2`, `=3-but-restrategize-not-yet` — to unstick the proof
       before A1's restrategize gate fires.

       NOTE: `stuck_rounds >= 1` is the SDK-bridge **encoding** of
       czy's "increase_prover_cycles else-branch," NOT a literal czy
       threshold. czy itself has no `>= 1` check; its equivalent gate
       is "neither retreat nor restrategize fires AND a stuck just
       happened." `process_sorry_result.py` has already bumped
       `stuck_rounds` 0→1 by the time this ladder is evaluated, so
       once a stuck has just landed, `stuck_rounds` is necessarily
       ≥ 1; the literal `>= 1` only guards the degenerate
       `stuck_rounds == 0` no-prior-stuck case in rung 4 below.

       Wiring status (post H5/H6 + PROVER_INJECT):
       - `need:assumption` arm — fully wired (H7 `extract_assumption.py`
         + H4-reauto `reautoformalize_node.py`/`commit_reautoformalize.py`).
       - `need:websearch` arm — H5 `extract_web_probe.py` landed,
         `dispatch_helper.py` wired via `_dispatch_websearch`.
       - `need:reference` arm — H6 `extract_reference_probe.py` landed,
         `dispatch_helper.py` reference branch still uses placeholder
         (H6 dispatch-wire deferred per H6_REFERENCE_PROBE_SPEC.md §3.5).
       - `webprobe_context` + `referenceprobe_findings[-1]` injection
         into prover — wired by PROVER_INJECT (`assemble_helper_context.py`
         + step d'' below).

       a) **Dispatch `decide-helper-markers` Task subagent.** Build
          the prompt with:
          - `theorem_name` — the parent's theorem text
          - `stuck_node` — `{theorem, node_id: <sorry_id>,
            last_error: <from events.jsonl most-recent
            subagent-stuck.details.blocker for this sorry, sliced 200
            chars>, dead_ends: <last 5 unique blockers, de-duped by
            80-char prefix; augmented with parent's last 3
            history_log[].retreat_reason strings>,
            reference_coverage: <parent's coverage_state, mapped to
            no_coverage|partial_coverage|cited_by_reference|unknown>,
            coverage_assessment: <best-effort, may be null>}`
          - `iteration` — current proof-loop iteration index
          - `stuck_rounds` — current `stuck_rounds` value for the sorry
          - `stalled_iterations` — best-effort, may be 0

          Capture stdout to:
          `$SANDBOX/_marker_<sorry_id>_<ts>.txt`

          The SKILL output is a single line of comma-separated markers
          from `{need:full, need:assumption, need:websearch,
          need:reference}`, OR an empty line if the SKILL judges no
          helper needed.

       b) **For each `need:assumption` marker the SKILL returned**
          (or for `need:full`, which expands to all three):
          dispatch the `helper-assumption` Task subagent (H7 SKILL,
          per `docs/H7_HELPER_ASSUMPTION_SPEC.md`). Capture stdout to:
          `$SANDBOX/_assumption_<sorry_id>_<ts>.json`

          The H7 SKILL's prompt and output contract are unchanged —
          this rung simply provides the caller. If the marker SKILL
          did not return `need:assumption` or `need:full`, skip this
          step.

       c) **Run `dispatch_helper.py`** (real bash, MANDATORY):

          ```bash
          python3 theme/scripts/dispatch_helper.py \
              --sub-problem-id "$SORRY_ID" \
              --marker-file "$SANDBOX/_marker_${SORRY_ID}_${TS}.txt" \
              --assumption-json-file "$SANDBOX/_assumption_${SORRY_ID}_${TS}.json" \
              --sandbox "$SANDBOX" \
              --stuck-rounds "$STUCK_ROUNDS"
          ```

          The `--assumption-json-file` flag is REQUIRED only when the
          marker file contains `need:assumption` or `need:full`. When
          it isn't (e.g. SKILL returned `need:websearch` only), the
          flag may be omitted; the dispatcher records
          `helper_script_failed` for the assumption branch with reason
          `missing_assumption_json` if encountered, but for pure
          websearch / reference markers no assumption invocation
          happens.

          The script emits ONE `helper-dispatched` milestone with verdict
          ∈ {`dispatched`, `no_helpers_needed`, `all_deferred`,
          `marker_decider_failed`, `parse_error`}. See
          `docs/H4_DISPATCH_HELPER_SPEC.md` §4 for the full payload schema.

       d') **Re-autoformalize from assumption hints** (H4-reauto port
          slice; fires ONLY when `dispatch_helper.py` returned
          `verdict=dispatched` AND the sorry's `assumption_hints[]`
          is non-empty in yaml after `dispatch_helper.py` exits).
          Skipped entirely when verdict ∈ {`all_deferred`,
          `no_helpers_needed`, `marker_decider_failed`}.

          (d'-i) Run `reautoformalize_node.py` (real bash, T2):

          ```bash
          python3 theme/scripts/reautoformalize_node.py \
              --sub-problem-id "$SORRY_ID" \
              --sandbox "$SANDBOX"
          ```

          Read the `reautoformalized` milestone verdict from
          events.jsonl (or stdout):
          - `no_hints` → exit 0 silently; skip to step (d).
          - `locked_fallback_prompt` → Lean skeleton already locked
            (`.integrity.json` present in sandbox); script wrote hint
            context to `$SANDBOX/_assumption_context_${SORRY_ID}.txt`;
            proceed to step (d'-ii-b) prompt-augment path.
          - `enriching` → enriched description written to
            `$SANDBOX/_enrich_desc_${SORRY_ID}_${TS}.txt`; proceed to
            step (d'-ii-a) skeleton-rewrite path.
          - `parse_error` → log; skip to step (d) (non-blocking
            degradation; prover continues on existing skeleton).

          (d'-ii-a) [skeleton-rewrite path — `enriching` verdict]

          Read enriched description from
          `$SANDBOX/_enrich_desc_${SORRY_ID}_${TS}.txt`. Rewrite the
          Lean skeleton for this sorry using the enriched description
          (same behavior as Phase 1 sub-autoformalize step). The
          skeleton MUST declare missing hypotheses as formal Lean
          parameters or `have` bindings derived from hint text.

          After writing the new skeleton, commit the enriched theorem
          back to yaml (T2):

          ```bash
          python3 theme/scripts/commit_reautoformalize.py \
              --sub-problem-id "$SORRY_ID" \
              --enriched-theorem-file \
                  "$SANDBOX/_enrich_desc_${SORRY_ID}_${TS}.txt" \
              --sandbox "$SANDBOX"
          ```

          Verdicts: `committed` (success, exit 0) | `parse_error`
          (exit 2; log error but continue — non-blocking).

          Then proceed to step (d) to continue the prover loop.

          (d'-ii-b) [prompt-augment path — `locked_fallback_prompt`]

          Script wrote hint context to
          `$SANDBOX/_assumption_context_${SORRY_ID}.txt`. Proceed to
          step (d'') which reads this file and assembles it into
          `_helper_context_${SORRY_ID}.md` for prover injection
          (PROVER_INJECT slice). DO NOT separately read the file
          here — step (d'') handles all three helper context sources
          (assumption / webprobe / refprobe) in one pass.

          DO NOT modify the locked Lean skeleton (Layer 1 violation).
          The locked-file fallback is structurally enforced by the
          `.integrity.json` gate in `reautoformalize_node.py`.

          Then proceed to step (d) to continue the prover loop.

          **T-tier**: `reautoformalize_node.py` is T2; skeleton
          rewrite (d'-ii-a) is T3 (LLM judgment); `commit_reautoformalize.py`
          is T2; hint-context injection (d'-ii-b) is T3 narrative.
          Empirical-adjustment escalation per Rule 9 §3 if traces show
          `helper-dispatched(verdict=dispatched)` events without
          `reautoformalized` milestone within ~15 s.

          See `docs/H4_REAUTOFORMALIZE_SPEC.md` for full slice spec.

       d'') **Assemble helper context for prover injection** (PROVER_INJECT
          port slice; fires after d' completes, regardless of d'
          verdict — including when d' was skipped because verdict was
          all_deferred / no_helpers_needed):

          ```bash
          python3 theme/scripts/assemble_helper_context.py \
              --sub-problem-id "$SORRY_ID" \
              --sandbox "$SANDBOX"
          ```

          The script reads (read-only, Layer 1 enforced):
          - `webprobe_context` from sorry_backlog.yaml (H5 output)
          - `referenceprobe_findings[-1]` from sorry_backlog.yaml (H6
            output; latest entry only per PROVER_INJECT D-3 architectural
            translation)
          - `_assumption_context_${SORRY_ID}.txt` from sandbox if present
            (H4-reauto `locked_fallback_prompt` path), OR `assumption_hints[]`
            from yaml otherwise; D-2 enriching-path gate skips this section
            when `_enrich_desc_${SORRY_ID}_*.txt` is present (skeleton
            rewrite already applied)

          Per-source caps (PROVER_INJECT D-5 deliberate +1 deviation):
          webprobe ≤3000 chars, refprobe ≤3000, assumption ≤2000;
          aggregate ≤6000.

          Outputs `$SANDBOX/_helper_context_${SORRY_ID}.md` with sections
          `### Web Probe (most-recent)` / `### Reference Probe (most-recent)`
          / `### Diagnosed missing hypotheses` (only the present arms).
          Emits `helper-context-assembled` milestone with verdict ∈
          {`assembled`, `empty`, `parse_error`}.

          **Read the output file:**

          ```bash
          HELPER_CTX=$(cat "$SANDBOX/_helper_context_${SORRY_ID}.md" 2>/dev/null || echo "")
          ```

          If `$HELPER_CTX` is non-empty: include its content in the
          next prover agent's Task prompt by appending it to
          `task_reference.md` (alongside route search context or
          reference context) under outer header
          `## Helper context (stuck recovery)` — this matches czy's
          `proverAgent.ts:610-611` `## Helper coverage context`
          injection slot. (The script writes only `### subsections`
          so the agent's outer `##` wrapper does not collide; per
          PROVER_INJECT §8 code review S5.1.)

          If `$HELPER_CTX` is empty: proceed to step (d) with no
          additional context (graceful degradation; non-blocking
          per PROVER_INJECT D-6 deliberate +1).

          **After the prover attack completes** (regardless of status),
          clear `webprobe_context` via consume-once clear (PROVER_INJECT
          D-4 H5/H6 asymmetric semantics):

          ```bash
          python3 theme/scripts/extract_web_probe.py \
              --sub-problem-id "$SORRY_ID" \
              --clear-context \
              --sandbox "$SANDBOX"
          ```

          NOTE: `referenceprobe_findings[]` is NOT cleared (accumulate
          semantics per H6 D-2). The `[-1]` read always picks up the
          latest probe result.

          **T-tier**: `assemble_helper_context.py` is T2. Context-file
          inclusion in prover prompt is T3 narrative.
          `extract_web_probe.py --clear-context` is T2.

          **czy fix**: this step closes czy's `proofLoop.ts:1314
          helperContext: undefined` bug, independently verified across 5
          §8 reviews (H4-reauto / H5 / H6 / PROVER_INJECT spec /
          PROVER_INJECT code). Per CZY_NEW_PUSH_AUDIT §3, czy 9ff6536
          deleted its own probe persistence — SDK-bridge intentionally
          retains it via skill artifacts and is strictly more correct.

          See `docs/PROVER_INJECT_SPEC.md` for full slice spec.

       d) **Continue the prover loop** on the next iteration. (Catch-all
          when step d' did not fire — verdict was all_deferred /
          no_helpers_needed / marker_decider_failed / no_hints; OR
          d' completed and rejoins here for the next attack via d''.)
          Helpers' yaml writes (`assumption_hints[]` / `assumption_analysis`
          / `webprobe_context` / `referenceprobe_findings[]`) feed back
          via d''.

       **Determinism tier (Rule 9 §3)**: `dispatch_helper.py` is T2
       (single named script, side-effect chain bundled). The
       `decide-helper-markers` Task dispatch (step a) and
       `helper-assumption` Task dispatch (step b) are T3
       (narrative-driven). Empirical adjustment rule: if real
       prove-deep traces show `subagent-stuck` events with
       `stuck_rounds >= 2` but no `helper-dispatched` milestone within
       ~10 s, escalate the trigger to T1 by detecting the lifecycle
       boundary in the orchestrator-side stream-json hook. Acceptable
       interim since missed dispatches degrade gracefully (next
       round's `stuck_rounds=3` fires restrategize anyway).

    4. **Else** (`stuck_rounds == 0` — pre-stuck; the very-first prover
       attempt before any stuck has been recorded): continue the prover
       loop directly. Higher stuck_rounds will accumulate from
       process_sorry_result on subsequent stucks; once stuck_rounds
       crosses 1, rung 3 (helper-dispatch) fires; once it crosses 3,
       rung 2 (restrategize) fires.

    Locked theorem signature on the parent is UNTOUCHED in either path
    (Rule 3 Layer 1).

    After EITHER script runs, the parent re-enters INITIALIZED with
    full history; the next iteration's ready_queue picks it up. When
    the next prove agent is dispatched, `read_history_log.py` (called
    by launch_background_agent above) will surface the prior attempts
    in the prompt with the "ACTION: Choose a DIFFERENT decomposition
    strategy" trailer (for retreat) or context that 3 prior strategy
    rounds failed (for restrategize).

    **Determinism tier (Rule 9 §3)**: T2. The agent reads two yaml
    fields and dispatches one named script — no LLM judgment in the
    gate itself. Skipping a script is detectable by absence of the
    matching milestone (`retreat-triggered` or `restrategize-triggered`).
  - **User-trust gate** (web-UI only — silently skipped in CLI-standalone
    mode when the tool is unavailable):
    If the blocker description mentions missing Mathlib infrastructure
    (patterns: "unknown identifier", "unknown constant", "no such lemma",
    "API doesn't exist", "需要 X 但 Mathlib 没有") OR the sorry has been
    stuck twice in a row, call
    `mcp__statlean_web_ui__request_user_decision` with these REQUIRED
    fields:

    ```
    question: <prose>. MUST use $...$ inline math and $$...$$ block math
              for any formula — the UI renders KaTeX. Don't leave LaTeX
              as plain text (it'll display as "$\sum_j..." which is
              unreadable).

    options:  ["trust_as_axiom", "trust_and_finish", "investigate_deeper", "abort"]
              · trust_as_axiom    → trust this one, KEEP attacking other
                                    items in ready_queue
              · trust_and_finish  → trust this one AND immediately wrap
                                    up the round (skip remaining queue,
                                    jump to Phase 3). Use when user
                                    likely wants to stop early.
              · investigate_deeper → re-dispatch with extra budget
              · abort              → give up

    trust_description: <plain Chinese, REQUIRED when options contain
                       trust_*>. Bulleted list naming each Mathlib /
                       Statlean infra gap or math fact being trusted.
                       Example for the χ² case:
                         "1. Mathlib 无 χ² 分布定义 (Probability.Distributions.ChiSquared 缺)
                          2. Mathlib 无 Hilbert-Schmidt 紧算子谱展开
                          3. Mathlib 无非 Gaussian iid 级数收敛 ∑_j λ_j(χ²-1) 判据"
                       Surfaces in UI as a separate audit panel so user
                       sees and the cross-job decisions table records
                       exactly what got trusted.

    ready_queue: <array — REQUIRED when options contain trust_*>.
                 Snapshot of remaining ready_queue (excluding current
                 sorry). One entry per item, with id + theorem + priority
                 + estimated_lines. Top 50 by priority. Lets user see
                 "if I trust_and_finish, this is what I'm skipping".
    ```

    Act on the reply:
      - USER_CHOICE: trust_as_axiom    → leave the sorry with comment
        `-- TRUSTED (user-approved infra gap: <one-line summary of
        trust_description>)`, skip further dispatches for this id,
        continue DAG loop attacking remaining ready_queue.
      - USER_CHOICE: trust_and_finish  → leave the sorry with comment
        `-- TRUSTED (user-approved infra gap: <reason>)`, mark all
        remaining ready_queue items as `pending (user requested early
        finish)`, **exit Phase 2 LOOP immediately and proceed to Phase 3
        finalize**. Do NOT dispatch additional items.
      - USER_CHOICE: investigate_deeper → keep in ready_queue with
        original priority, re-dispatch with time budget ×1.5.
      - USER_CHOICE: <free-text hint>  → treat as R1 proof-route hint
        for the next dispatch of this sorry (inject via
        `parse_proof_roadmap.py --inline "<hint>" --theorem <name>`).
      - USER_ABORTED: <reason>         → mark sorry as stuck in backlog,
        never re-dispatch this session.
      - Tool not found / tool error    → fall back to CLI-default
        (keep as pending with deprioritized priority, continue).

elif result.status == "need_sub_lemma":
  Two-step process (czy newloop port — replaces the older
  validate_decomposition.py + manual yaml edit recipe):

  1. **Validate the decomposition** (still T2 — keep validate_decomposition
     as the size-monotone "pushing the pea" guard):

     ```bash
     python3 theme/scripts/validate_decomposition.py \
         --parent-metrics  '<JSON: goal_pp_lines, estimated_lines, deps_count>' \
         --children-metrics '<JSON: same shape, one per sub-lemma>'
     ```
     Exit 0 → continue to step 2. Exit 1 → emit decomposition-rejected,
     mark parent pending, do NOT add children.

  2. **Apply the decomposition atomically** via decompose_node.py
     (replaces the manually-written yaml mutation):

     ```bash
     python3 theme/scripts/decompose_node.py \
         --parent-id "<sorry_id>" \
         --sub-problems-json '[{"id":"<sorry_id>.sub1","theorem":"...",
                                "blocker":"...","estimated_lines":...},
                               {"id":"<sorry_id>.sub2",...}]' \
         --decision-reason "<why this decomposition; surfaces in retreat
                            history if children later fail>" \
         --sandbox "$SANDBOX"
     ```
     The script (T2 atomic):
      - Inserts sub-rows with state=INITIALIZED, parent_id=<parent>,
        children=[], history_log=[], stuck_rounds=0
      - Sets parent.state=INACTIVE_WAIT, parent.children=[new ids]
      - Stashes `--decision-reason` on parent as `_pending_decision_reason`
        (consumed by record_retreat if children later fail)
      - Locked theorem signature on parent UNTOUCHED (Rule 3 Layer 1)
      - Emits subtasks-split milestone
      - Validates: parent must exist; parent.state must be INITIALIZED
        (cannot decompose an already-decomposed parent without retreat
        first); sub ids globally unique (no collision; no dup in request)

  After step 2 the parent is INACTIVE_WAIT and the new sub-rows are
  INITIALIZED. The next ready_queue computation picks up the sub-rows
  automatically (parent is INACTIVE_WAIT → its children with
  state=INITIALIZED qualify as ready under the tree-walker rule above).
  No manual queue manipulation needed.
```

---

## Phase 3: Checkpoint

After the scheduling loop exits (all done, or time budget reached):

1. **Commit**: Any uncommitted proved work (incremental commits are
   handled by `process_sorry_result.py` per result; this is just for
   stragglers like Verified.lean updates).

2. **Collect new_knowledge** YAML blocks from this cycle's sub-agents
   into `/tmp/new_knowledge.yaml` (will be ingested by step 3 below).

3. **Cycle finalize (MANDATORY, real bash)**:
   ```bash
   python3 theme/scripts/prove_deep_end.py \
       --sandbox "$SANDBOX" \
       --target "<TARGET>" \
       --proved <K> --stuck <J> --remaining <R> \
       --memory-summary "<NATURAL LANGUAGE — see below>" \
       [--new-knowledge-file /tmp/new_knowledge.yaml]
   ```
   The script bundles: sync_sorry_backlog.py + MEMORY.md append +
   ingest_knowledge.py + `memory-md-updated` + `dag-cycle-done`
   milestones. **`--memory-summary` MUST be ≥ 20 chars after trim**;
   the script exits 1 (cycle NOT finalized) on empty/placeholder values.
   This makes "Update MEMORY.md" structural rather than aspirational —
   you don't get to skip it by forgetting.

   `--memory-summary` content guidelines: 1-3 sentences in natural
   language. Cover any of: (a) what new Mathlib pattern was learned,
   (b) which routes did NOT work and why (anti-patterns), (c) what
   blockers persisted and what would be needed upstream. Format is
   free; the script just appends under a dated header in MEMORY.md.

4. **Screen output** — see "屏幕输出" block below for the canonical
   compact-summary format.

**屏幕输出**（紧凑摘要，≤5 行）：
```
DAG PROVE: Xmin | sorry N→M (proved K, stuck J) | 入库 P 条
  Next: [highest priority item]
详情: reports/prove_deep_<target>.md
```

**文件存档**（完整详情，写入 `reports/prove_deep_<target>.md`）：
```
DAG PROVE REPORT
  Duration: X min
  Sorries before: N
  Sorries after:  M (proved K, stuck J, remaining R)
  Proved:         [list with theorem names]
  Unlocked:       [downstream items now ready]
  Infrastructure: [new defs/lemmas added]
  Stuck:          [list with blockers]
  Next targets:   [highest priority ready items for next session]

  已入库 proof_knowledge.yaml:
  - [L1/L2/L3] <trigger> — <正面/anti> — <来源>
```

用 Write 工具写入报告文件，屏幕只输出摘要行。

**`<target>` 命名规则**：单目标 → 定理名（如 `gaussian_lsi`）；`all-leaves` → `all_leaves`。

**Agent launch/result 屏幕输出也精简**：
```
[agent] 启动: <sorry_name> (file:line)
[agent] 完成: <sorry_name> — proved/stuck
```
不在屏幕输出 agent prompt 全文或详细结果分析。

---

## Single-Target Mode (specific ID or `next`)

When not `all-leaves`, skip the DAG scheduler:

1. Select the single target sorry.
2. Run Phases 1-style research (parallel haiku agents for API search).
3. Decompose into sub-lemmas if large.
4. Prove sub-lemmas depth-first (leaf → intermediate → hard).
5. Each proved sub-lemma: incremental build + commit.
6. Report.

This follows the original `/prove-deep` flow but with:
- **No batch waiting** — process results as they come.
- **Incremental commits** — don't wait for full theorem.
- **sync_sorry_backlog.py** integration.

---

## Acceleration Rules

1. **Phase 0 工具链强制执行**:
   - 大文件先用 `python3 scripts/extract_signatures.py <file>` 读声明索引
   - 攻击 sorry 前先查 `theme/proof_knowledge.yaml` 匹配 goal pattern
   - tactic 试错阶段用 `bash scripts/check_snippet.sh` 增量编译
2. **条件跳过搜索（省 token）**:
   - proof_knowledge.yaml L3/L2 匹配 → **跳过 mathlib_api_index**（省 8.5K token/agent）
   - 未匹配 → 读 `theme/mathlib_api_index.md` + `grep theme/mathlib_full_type_index.tsv`
   - 仍未找到 → `#check` / `exact?` → grep Mathlib 源码（必须注明升级理由）
3. **Incremental build**: `lake build Statlean.<Module>` not `lake build`.
4. **No redundant search**: Trust subagent results.
5. **Parallel research**: Use haiku agents for API search.
6. **入库不等待**: 证完子引理立即 commit，不等主定理。
7. **Knowledge 入库**: 成功证明后，new_knowledge 通过 `python3 scripts/ingest_knowledge.py --input <file>` 自动入库
8. **上下文满处理**:
   - 等待 active agents 返回
   - sync backlog + commit
   - 更新 MEMORY.md
   - 输出: "上下文已满，用 /prove-deep all-leaves 继续"
9. **同文件写互斥（强制，DPI 教训）**:
   - 多个 agent **不得同时修改同一 .lean 文件**
   - 同一文件的不同 sorry → 串行攻击（A 完成 → commit → B 从新状态启动）
   - 不同文件的 sorry → 可并行
   - 违反此规则 → agent 在过时代码上浪费 token（实测 ~220K token 损失）
10. **snippet check 优先于 lake build（强制）**:
    - tactic 试错 → `bash scripts/check_snippet.sh`（~10s）
    - 全模块验证 → `lake build Statlean.<Module>`（~150s）
    - **比例要求**：snippet check ≥ 3× lake build 次数
    - DPI 教训：80 次 lake build ≈ 3.5h 纯编译 = 42% 墙钟时间
11. **跨会话 agent 处理**:
    - 新会话开始后，检查旧 agent 目标代码是否已变更
    - 若已变更 → 不等旧 agent，从当前文件状态启动新 agent
    - 旧 agent 返回后若与当前文件冲突 → 丢弃结果

## Key Context

- Project: `/home/gavin/statlean`
- Build: `lake build Statlean.<Module>` (incremental) or `lake build` (full)
- Backlog: `theme/input/sorry_backlog.yaml`
- Sync tool: `python3 theme/scripts/sync_sorry_backlog.py`
- Memory: `.claude/projects/-home-gavin-statlean/memory/MEMORY.md`
- Mathlib index: `theme/mathlib_api_index.md`
- Mathlib full index: `theme/mathlib_full_type_index.tsv` (51K entries, grep)
- Tactic patterns: `theme/proof_knowledge.yaml` (58 patterns, match before search)
- Signature extractor: `python3 scripts/extract_signatures.py` (replaces blind file reads)
- Snippet checker: `bash scripts/check_snippet.sh` (incremental single-decl compile)
- Classifier: `theme/scripts/classify.py`

## 输出预算规则（强制）

- 屏幕文本输出（非工具调用）总预算 ≤ 5K token（多 sorry DAG 模式）
- 超预算时自动切换为"极简模式"：只输出 sorry 计数变化 + 文件路径
- Agent launch → 1 行 `[agent] 启动: <name> (file:line)`
- Agent result → 1 行 `[agent] 完成: <name> — proved/stuck`
- DAG 报告 → 3-5 行屏幕摘要 + 完整报告写 `reports/prove_deep_<target>.md`
- 知识入库 → "入库 N 条 pattern"（YAML 和脚本输出在 Bash 工具内）
- 经验报告 → "经验报告已写入 reports/session_report.md"
- 工具调用输出（Bash、Read、Grep 等）不计入此预算

## Output Conventions (web UI contract)

See `theme/conventions/ui-signals.md` for the event + Markdown-header
protocol.

`/prove-deep` runs as a subagent of `/pipeline` (Step 5 = "prove").
The Step-number namespace on `events.jsonl` is owned by the outer
pipeline — this skill MUST NOT emit `## Step N:` Markdown headers or
`emit_event.py step` events for its internal DAG Phases. Doing so
collides with pipeline's Step 5 and the UI renders confusing merged
cards.

DAG Phase narrative (Phase 0 route search → Phase 1 decomposition →
Phase 2 parallel dispatch → Phase 3 reassembly) goes in normal prose,
which lands in the Report stream where the user can follow along.

**Artifact events** remain welcome (e.g. `sorry_list.json`,
per-sub-agent result files). Those are namespaced by `kind_tag`,
not by integer step id, and don't collide.
