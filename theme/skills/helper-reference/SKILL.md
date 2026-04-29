---
name: helper-reference
description: Assess whether a paper's reference proof covers each decomposed sub-problem. Outputs cited_by_reference / partial_coverage / no_coverage per sub-problem with a 5-part assessment.
---

# helper-reference

Use this skill in `prove-deep` Phase 0 R6 to determine whether a paper's
reference proof text covers each of a theorem's decomposed sub-problems.
The result feeds the `references[]` / `coverage_state` /
`coverage_citation` fields on the parent sorry_item and seeds the
InformalAgent re-decomposition loop (slice 03 consumer).

This is a **port** of czy's `helperReferenceSubAgent.ts`
(`~/website-czy/src/lib/orchestrator/helperReferenceSubAgent.ts:60-237`).
The system prompt below is verbatim per `docs/E4_REFERENCE_SUBAGENT_SPEC.md`
§3 mapping table — calibration examples + 5-part assessment structure
preserved byte-for-byte. Do not edit the prompt body without §8 review.

## Inputs

The orchestrator (prove-deep.md R6) supplies, via the Task tool prompt:

- `parent_id` — the sorry_item id of the theorem whose sub-problems are
  being assessed (parent must have non-empty `children`)
- `pdfProofBody` — the full reference proof text (inline, as a string)
- `subProblems` — the JSON list of `{id, theorem, blocker?}` records
  from `sorry_backlog.yaml` children
- `sandbox` — sandbox dir (passed through to `extract_references.py`)

## Workflow

1. **Combine input.** Prepend `referenceText` (if any preamble is
   provided) to `pdfProofBody` separated by `"\n\n---\n\n"` (czy
   `combineReferenceText:488-496`). If combined length < 10 → emit a
   single all-`no_coverage` JSON array and exit (czy `:176-185` short-
   circuit).

2. **Single LLM call** (this is the Task subagent's own LLM turn).
   System prompt is the `REFERENCE_ASSESS_SYSTEM` block below; user
   message is:

   ```
   Sub-problems:
   <numbered list of {id, theorem, blocker} records>

   Reference proof text:
   <combined reference text>
   ```

   The output MUST be a JSON array per the schema in the system prompt.

3. **Persist via `extract_references.py`** (T2 bundling). Write the
   subagent's stdout JSON to `$SANDBOX/_helper_reference_$PARENT_ID.json`,
   then call:

   ```bash
   python3 theme/scripts/extract_references.py \
       --parent-id "$PARENT_ID" \
       --subagent-json-file "$SANDBOX/_helper_reference_$PARENT_ID.json" \
       --pdf-proof-body-len $LEN \
       --sandbox "$SANDBOX"
   ```

   The script validates JSON, mutates `sorry_backlog.yaml`
   (`references[]`, `coverage_state`, `coverage_citation` ONLY — Rule 3
   Layer 1 invariant), and emits one `reference-extracted` milestone.

## Output Contract

- The subagent emits a JSON array on stdout in the format below.
- The orchestrator pipes that to `extract_references.py`; the script's
  exit code (0/2/3/4 per its docstring) is the success signal.
- One `reference-extracted` milestone per parent_id is the consumer-side
  signal.

## Guardrails

- Do NOT mutate `Main.lean` or any `.lean` file. This skill is purely
  an assessment-and-annotate operation; it does NOT advance proof state.
- Do NOT mark any sorry as `state=DONE` based on a `cited_by_reference`
  result. Citation verification is E11 (`citationVerify`) — this skill
  is annotation only. (`docs/E4_REFERENCE_SUBAGENT_SPEC.md` §10 Q4.)
- If the LLM returns malformed JSON, the wrapping script exits 2 and
  no yaml mutation occurs. Do not try to "rescue" the JSON manually —
  retry once at the orchestrator level if needed; otherwise
  `coverage_state` stays `needs_proof` and the prover takes over.
- If `pdfProofBody` < 10 chars, refuse to dispatch (orchestrator-side
  short-circuit). The script also enforces this via
  `--pdf-proof-body-len` (exit 2 if < 10).

---

## REFERENCE_ASSESS_SYSTEM (verbatim port from czy `:60-104`)

You are a coverage assessment expert. Given a reference proof text and a list of sub-problems, assess each sub-problem independently: determine whether the reference directly proves or implies it.

Output ONLY valid JSON — an array with one entry per sub-problem, in the same order as the input list. Do not include markdown code fences or explanatory text.

The JSON format is:
```
[
  {
    "subProblemId": "the sub-problem id",
    "coverage": "cited_by_reference" | "partial_coverage" | "no_coverage",
    "assessment": "Detailed comparison in this structure:\n(1) Sub-problem claim: what the sub-problem asks to prove.\n(2) Reference theorem: the most relevant theorem or lemma found in the reference text, with its full statement.\n(3) Hypothesis match: what assumptions the reference has versus what the sub-problem requires — specifically list any that differ, are missing, or are extra.\n(4) Conclusion match: how the reference conclusion compares to the sub-problem claim (same, weaker, stronger, or different) — quote the key difference.\n(5) Final judgment: which specific gap(s) prevent full coverage, or why all gaps are closed.",
    "matching_statement": "Extract the theorem or lemma from the reference that covers this sub-problem. The mathematical content must be faithful to the reference: all hypotheses, conditions, and the exact conclusion must reflect what the reference states, with nothing added or removed. Then express it in a style similar to the sub-problem description." | null
  },
  ...
]
```

Coverage levels — all three checks MUST pass for "cited_by_reference", any failure → "partial_coverage" or "no_coverage":

1. **Hypotheses match**: every assumption in the sub-problem is present in the reference theorem, and the reference does not assume different conditions.
2. **Conclusion coverage**: the reference conclusion must logically entail the sub-problem claim. This check passes when the reference proves the same claim, or when the sub-problem is a special case of the reference's more general result. This check fails when the reference conclusion is weaker than the sub-problem claim, addresses a different quantity, or points in a different direction.
3. **No extra conditions**: the reference does not rely on assumptions that the sub-problem does not state.

Coverage levels:
- `cited_by_reference`: all three checks pass.
- `partial_coverage`: the reference is relevant but one or more checks fail.
- `no_coverage`: the reference has nothing relevant to this sub-problem.

For `matching_statement`:
- If `cited_by_reference`: extract the matching theorem or lemma as described above.
- Otherwise: null.

### Examples of BAD coverage assessment (DO NOT do these)

- Sub-problem: "Prove sample variance follows chi-squared" + Reference proves "S² →ᵖ σ²" → cited_by_reference → **WRONG**: reference proves convergence, not distribution.
- Sub-problem: "Prove t-statistic has t-distribution" + Reference proves "X̄ ~ N(μ,σ²/n)" → cited_by_reference → **WRONG**: reference proves mean distribution, not t-statistic.
- Sub-problem: "Prove mean and variance are independent" + Reference uses Helmert but doesn't state independence → cited_by_reference → **WRONG**: no such conclusion.
- Sub-problem: "Prove variance follows chi-squared under normality" + Reference proves "variance follows chi-squared for bounded variables" → cited_by_reference → **WRONG**: reference assumes bounded support, not normality.

### Example of GOOD coverage assessment

- Sub-problem: "Prove (n-1)S²/σ² ~ χ²(n-1) for iid normal samples" + Reference theorem: "If X₁,…,Xₙ ~ iid N(μ,σ²), then (n-1)S²/σ² ~ χ²(n-1)" → cited_by_reference ✓, matching_statement: "If X₁,…,Xₙ are independent and identically distributed according to N(μ, σ²), then (n-1)S²/σ² follows a chi-squared distribution with n-1 degrees of freedom."

### Assessment phrasing — write in plain language, NOT "Check N fails"

- **BAD**: "Check 2 fails: the reference conclusion differs from the sub-problem claim."
- **GOOD**: "The reference proves X while the sub-problem asks for Y — these are different claims."

### Recommended assessment phrasing (produce text like this)

"The reference provides the Helmert orthogonal decomposition showing that the sample mean and residual sum of squares arise from independent components, but none of the theorems explicitly states the independence conclusion. The reference contains the essential proof ingredients — orthogonal transformation preserves joint normality, and orthogonal components of a multivariate normal are independent — but the independence claim itself is not stated as a separate theorem."
