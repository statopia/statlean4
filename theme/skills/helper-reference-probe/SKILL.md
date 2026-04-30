---
name: helper-reference-probe
description: Stuck-recovery reference probe. Given a stuck sub-problem (its Lean error, current proof goal, and dead-ends from prior attempts) and the full reference proof text, identifies the most relevant reference passage and explains how it might break the impasse. Outputs a flat JSON object with matchedPassage, analysis, and suggestion. Fires PER-STUCK when the marker decider selects need:reference.
---

# helper-reference-probe

Use this skill in `prove-deep` Phase 2 stuck-recovery (H4 dispatch_helper —
rung 3c', fires after `decide-helper-markers` SKILL returns `need:reference`
in the markers) to find the reference proof passage most likely relevant to
the current stuck point and suggest a concrete Lean tactic next step.

This is a **port** of czy's `ReferenceSubAgent.referenceProbe`
(`~/website-czy/src/lib/orchestrator/helperReferenceSubAgent.ts:312-376`).
The system prompt below is verbatim per `docs/H6_REFERENCE_PROBE_SPEC.md`
§3 mapping table — REFERENCE_PROBE_SYSTEM byte-equal to czy `:106-119`.
Do not edit the prompt body without §8 review.

**Do NOT confuse with E4** (`helper-reference/SKILL.md`). E4 is alignment-
phase, takes all sub-problems, returns a coverage taxonomy array. H6 (this
skill) is stuck-recovery, takes ONE sub-problem + StuckContext + reference
text, returns a flat JSON object. The two are structurally incompatible
(E4 returns JSON array; H6 returns JSON object). If an agent mistakenly
dispatches E4 for a stuck-recovery event, `extract_reference_probe.py`
will fail at parse time (array root → parse_error verdict, no yaml
mutation).

## Inputs

The orchestrator (Phase 2 stuck-recovery, H4 narrative rung 3c') supplies,
via the Task tool prompt:

- `theorem_name` — the top-level theorem name
- `sub_problem_id` — the sorry_item id that is stuck
- `sub_problem_description` — the NL description of the stuck sub-problem
- `stuck_context` — rendered StuckContext (see User Message format below):
  - `lastError` — the Lean error text (≤800 chars)
  - `currentGoal` — the current Lean proof goal (≤1200 chars)
  - `deadEnds` — list of prior dead-ends (last 5, each ≤200 chars)
  - Note: `codeAttempted` is intentionally NOT included — the probe's job
    is to find reference content, not analyse Lean code. Layer separation:
    referenceProbe is fed *facts* about the stuck point, not Lean source code.
    See czy `:302-305` doc comment.
- `pdfProofBody` — the full reference proof text from `paper_body.txt`
  (no truncation; the full text is passed; SDK provider context window
  handles length implicitly)
- No `leanCodeSnippet` — this field is in czy's ReferenceProbeInput type
  but was NEVER populated by czy's caller (`helperAgent.ts:145-149`).
  Reserved for future use; not currently supplied. Do not expect or require it.

## Model selection

D-1 czy parity: this skill uses the **fast model** (not the strong model).
`helperReferenceSubAgent.ts:327` uses `getDefaultModel` — fast model, same
as H7 `helper-assumption` (`:84`). Helper sub-agents are diagnostic passes,
not proof-writing passes. CLAUDE.md Rule 2 fast-model constraint applies.
SDK-bridge: the Task tool inherits the parent session's model. The parent
should invoke this skill in a context where the fast model is selected.

## Workflow

1. **Build the user message** with the five inputs (czy `:330-335` +
   `renderStuckContext` `:506-516`):

   ```
   ## Theorem
   <theorem_name>

   ## Stuck sub-problem
   [<sub_problem_id>] <sub_problem_description>

   ## Stuck context
   Lean error: <lastError|(none)>
   Current Lean goal: <currentGoal|(not probed)>
   Dead ends from prior attempts: <deadEnds_joined|"(none)">

   ## Reference proof text
   <pdfProofBody>
   ```

   Dead-ends rendering: join the last 5 dead-ends with `"; "`. If dead-ends
   list is empty, use the string `(none)`. Do NOT include `codeAttempted`
   in the rendered context (czy `:505` layer-separation design).

2. **Single LLM call** (this is the Task subagent's own LLM turn).
   System prompt is the `REFERENCE_PROBE_SYSTEM` block below. User message
   is from step 1. The output MUST be a valid JSON object per the schema
   in the system prompt (three fields: `matchedPassage`, `analysis`,
   `suggestion`). Do NOT wrap in markdown fences — output raw JSON.

3. **Persist via `extract_reference_probe.py`** (T2 bundling). Write the
   subagent's stdout JSON to
   `$SANDBOX/_reference_probe_<sub_problem_id>_<ts>.json`, then call:

   ```bash
   python3 theme/scripts/extract_reference_probe.py \
       --sub-problem-id "$SUB_PROBLEM_ID" \
       --subagent-json-file "$SANDBOX/_reference_probe_${SUB_PROBLEM_ID}_${TS}.json" \
       --sandbox "$SANDBOX" \
       --backlog-path "$BACKLOG"
   ```

   The script validates JSON, appends to `referenceprobe_findings[]` on
   the targeted sorry row (Rule 3 Layer 1 invariant — only this field
   is written), and emits one `reference-probe-completed` milestone.
   Maximum 10 entries per sorry_item (oldest dropped on overflow).

## Output Contract

- The subagent emits a JSON OBJECT (not array, not scalar) on stdout.
  Three fields exactly (dari czy `:106-119` REFERENCE_PROBE_SYSTEM schema).
- The orchestrator writes that to a temp file and passes the path to
  `extract_reference_probe.py`; the script's exit code (0/2) is the
  success signal.
- One `reference-probe-completed` milestone with verdict ∈
  {`probed`, `probed_no_content`, `skipped_no_reference`, `parse_error`}
  is the consumer-side signal.

## Clamping (post-processing by extract_reference_probe.py)

The script clamps each field before assembly (czy `:355-357`):
- `matchedPassage`: ≤500 chars
- `analysis`: ≤300 chars
- `suggestion`: ≤500 chars
- Total `assembledContext` output: ≤3000 chars (truncated with `"..."`)

The SKILL LLM output is not required to pre-clamp — the script enforces.
However, the SKILL system prompt asks for ≤300 and ≤500 char fields so the
LLM self-limits (mirrors czy prompt text).

## Pre-check gate (czy parity)

The orchestrator MUST check `paper_body.txt` BEFORE dispatching this SKILL.
If `paper_body.txt` is absent or its content is < 10 chars, do NOT dispatch
the SKILL (saves one LLM call). Pass no `--reference-json-file` to
`dispatch_helper.py`; the dispatcher records `verdict=skipped_no_reference`
for the reference marker. See czy `:319-321` early return.

## Guardrails

- Do NOT mutate `Main.lean` or any `.lean` file. This skill is purely
  a reference-probe annotate operation; it does NOT advance proof state.
- Do NOT mark any sorry as `state=DONE`. This skill annotates; it does
  not verify or close.
- Do NOT inject `assembledContext` into the prover prompt yourself.
  H6-mvp faithfully reproduces czy's gap where `assembledContext` is
  computed but NOT routed to the ProverAgent (D-3 czy parity). The
  H6-prover-inject follow-on slice will add injection. For now,
  `assembledContext` is written to `referenceprobe_findings[]` yaml only.
- Do NOT call `extract_references.py` (E4's script). H6 uses
  `extract_reference_probe.py` (a separate script, separate yaml field,
  separate milestone). They are not interchangeable.
- If the LLM returns malformed JSON, the wrapping script exits with
  code 2, verdict=`parse_error`, and yaml unchanged. Do not try to
  "rescue" the JSON manually.
- Output ONLY a raw JSON object. No markdown fences, no prose before
  or after.

---

## REFERENCE_PROBE_SYSTEM (verbatim port from czy `:106-119`)

> Byte-equal port of czy's `REFERENCE_PROBE_SYSTEM` template literal at
> `helperReferenceSubAgent.ts:106-119`. H6 §8 code review S2.1 (2026-04-30)
> caught an earlier draft that paraphrased and dropped: (1) the "NOT
> classifying coverage" task-scoping paragraph, (2) "no markdown fences"
> in the JSON directive, (3) detailed JSON field descriptions, (4) the
> final hallucination guard. Post-fixup body restores czy literal text.

You are a reference proof analyst helping a Lean theorem prover that is stuck.

Task: given the prover's current stuck point (the Lean error, the current proof goal, and the dead-ends from prior attempts) and the full reference proof text, identify the most relevant reference passage and explain how it might help break the impasse.

You are NOT classifying coverage; you are NOT proving anything; you are NOT diagnosing the Lean code. You are a research assistant: take the stuck point as given, find the relevant reference content, explain its connection, and suggest a concrete next step.

Output ONLY valid JSON, no markdown fences:
{
  "matchedPassage": "the most relevant 1-2 paragraphs from the reference text, verbatim or near-verbatim, ≤500 chars",
  "analysis": "explain how this passage connects to the stuck point — which error / dead-end / goal it addresses, ≤300 chars",
  "suggestion": "concrete next step: which Lean tactic to try, which Mathlib lemma to apply, which sub-goal to introduce, or which proof restructuring to attempt, ≤500 chars"
}

If no part of the reference is genuinely relevant to the stuck point, return all three fields as empty strings — do NOT fabricate connections.
