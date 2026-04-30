---
name: helper-assumption
description: Diagnose mathematical hypotheses likely missing from a stuck sub-problem's statement. Outputs a JSON object with a per-call list of natural-language missing-assumption suggestions plus a short analysis of why they would unstick the proof.
---

# helper-assumption

Use this skill in `prove-deep` Phase 2 stuck-recovery (H4 dispatch_helper —
not yet wired in this repo; H7 ships standalone per spec D-3) to identify
mathematical hypotheses that are likely **missing** from a stuck sub-
problem's statement (regularity / measurability / integrability /
independence / etc.). The result is persisted as a per-call list of NL
hint strings on the targeted sorry row so a future caller can re-
autoformalize the enriched description.

This is a **port** of czy's `helperAssumptionSubAgent.ts`
(`~/website-czy/src/lib/orchestrator/helperAssumptionSubAgent.ts:1-183`).
The system prompt below is verbatim per `docs/H7_HELPER_ASSUMPTION_SPEC.md`
§3 mapping table — calibration list + 7 example missing-condition
categories + JSON output schema preserved byte-for-byte. Do not edit the
prompt body without §8 review.

## Inputs

The orchestrator (Phase 2 stuck-recovery, H4 territory; or test harness
today) supplies, via the Task tool prompt:

- `theorem_name` — the top-level theorem name
- `sub_problem_id` — the sorry_item id whose statement is being
  diagnosed for missing hypotheses
- `sub_problem_description` — the NL `theorem` text from yaml
- `lean_code` — optional Lean skeleton excerpt from the sandbox
  (≤3000 chars; czy `:152` clamps to this)
- `sandbox` — sandbox dir (passed through to `extract_assumption.py`)

## Workflow

1. **Build the user message** with the four inputs (czy `:139-158`):

   ```
   Theorem: <theorem_name>
   Sub-problem: <sub_problem_id>
   Description: <sub_problem_description>

   ## Lean skeleton (for context)
   ```lean
   <lean_code, sliced to 3000 chars>
   ```

   Identify mathematical hypotheses or regularity conditions that are likely MISSING from the sub-problem statement above. Only list conditions whose absence would explain why a Lean prover would get stuck.
   ```

   The `## Lean skeleton` block is omitted entirely if `lean_code` is
   empty or whitespace (czy `:148-154`).

2. **Single LLM call** (this is the Task subagent's own LLM turn).
   System prompt is the `DIAGNOSE_SYSTEM` block below; user message is
   from step 1. The output MUST be a JSON object per the schema in the
   system prompt. Note: D-2 — model selection via SDK-bridge runtime
   inheritance. Task tool inherits the parent claude session's model
   (same mechanism as helper-reference, citation-verify, informal-refine).
   Do NOT explicitly select a model here.

3. **Persist via `extract_assumption.py`** (T2 bundling). Write the
   subagent's stdout JSON to
   `$SANDBOX/_helper_assumption_$SUB_PROBLEM_ID.json`, then call:

   ```bash
   python3 theme/scripts/extract_assumption.py \
       --sub-problem-id "$SUB_PROBLEM_ID" \
       --subagent-json-file "$SANDBOX/_helper_assumption_$SUB_PROBLEM_ID.json" \
       --sandbox "$SANDBOX"
   ```

   The script validates JSON, mutates `sorry_backlog.yaml`
   (`assumption_hints` + `assumption_analysis` ONLY — Rule 3 Layer 1
   invariant), and emits one `assumption-extracted` milestone.

## Output Contract

- The subagent emits a JSON OBJECT (not array) on stdout in the format
  below.
- The orchestrator pipes that to `extract_assumption.py`; the script's
  exit code (0/2/3/4 per its docstring) is the success signal.
- One `assumption-extracted` milestone per sub_problem_id is the
  consumer-side signal. Verdict ∈ {`extracted`, `empty`, `parse_error`,
  `task_dispatch_failure`} where `task_dispatch_failure` is reserved
  for caller-emitted use (D-5 — the script itself emits only the
  first three).

## Guardrails

- Do NOT mutate `Main.lean` or any `.lean` file. This skill is purely
  an annotate operation; it does NOT advance proof state.
- Do NOT include Lean syntax in the missingAssumptions strings. The
  caller (H4, eventually) re-runs sub-autoformalize on the enriched
  NL description; mixing Lean syntax into the NL would break that
  pipeline.
- Do NOT mark any sorry as `state=DONE`. This skill annotates; it does
  not verify or close.
- Do NOT mention proof tactics or Lean-specific advice in the analysis.
  The diagnostician's job is mathematical hypothesis identification, not
  proof guidance.
- Do NOT repeat hypotheses already stated in the sub-problem
  description — the caller wants NEW hypotheses to add.
- If the LLM returns malformed JSON, the wrapping script exits 0 with
  verdict=`parse_error` and yaml unchanged. Do not try to "rescue" the
  JSON manually — the orchestrator (eventually H4) decides whether to
  retry.
- **D-1 OVERWRITE semantic.** Each invocation of this skill OVERWRITES
  the prior `assumption_hints` list on the targeted sorry row. czy
  parity — the dormant `AssumptionVersion` chain semantic was intended
  but never wired in czy itself; cross-round chain emerges through
  description-enrichment cycle (H4's territory), NOT yaml accumulation.

---

## DIAGNOSE_SYSTEM (verbatim port from czy `:32-60`)

You are a mathematical assumption diagnostician for Lean 4 theorem proving.

A prover agent has become stuck while attempting to prove a sub-problem. Your task is to identify mathematical hypotheses or regularity conditions that are likely MISSING from the statement — conditions whose absence would explain why the proof is stuck.

Rules:
- Output ONLY conditions that are not already stated in the sub-problem description.
- Each condition must be a self-contained mathematical statement in natural language (no Lean syntax).
- Be specific: write "the function f is Lipschitz continuous on a compact set K" rather than "regularity condition".
- Do NOT suggest proof tactics or Lean-specific advice.
- Do NOT repeat what is already stated in the sub-problem.
- If nothing is clearly missing, return an empty list.

Common missing conditions in measure-theoretic / statistical theorems:
- Measurability of auxiliary functions
- Integrability / finite expectation conditions
- Independence / i.i.d. assumptions
- Compact support or boundedness
- Regularity (Lipschitz, differentiable, continuous)
- Sigma-finiteness of the measure
- Completeness of the probability space

Output ONLY valid JSON, no markdown fences:
```
{
  "missingAssumptions": [
    "Natural language statement of missing assumption 1",
    "Natural language statement of missing assumption 2"
  ],
  "analysis": "Brief explanation (≤200 chars) of why the proof is likely stuck and what adding these assumptions would fix."
}
```
