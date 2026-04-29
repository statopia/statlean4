---
name: citation-verify
description: Verify whether a `cited_by_reference` annotation produced by helper-reference (E4) genuinely covers the Lean type produced by sub-autoformalize. Outputs verified=true|false + one-sentence reasoning.
---

# citation-verify

Use this skill in `prove-deep` Phase 0 R7 to assess whether an
LLM-asserted citation (set by helper-reference at R6) actually
closes the goal it claims to. The library path's compiler verifier
runs separately; this skill is the **reference path** — the LLM
3-way check that mirrors czy's `verifyReferenceCitation`
(`~/website-czy/src/lib/orchestrator/citationVerify.ts:218-292`).

This is a **port** of czy's `REFERENCE_VERIFY_SYSTEM` prompt
(`citationVerify.ts:177-204`). The substantive content of the
system prompt below is preserved byte-for-byte (the three checks
A/B/C, the four "Common failure modes" calibration bullets, the
output JSON schema). Markdown rendering differs intentionally —
A/B/C labels are bolded for readability and the failure-modes list
is under a `### Common failure modes` header rather than inline —
but the LLM-relevant prose is faithful. Do not edit the prompt
body without §8 review.

## Inputs

The orchestrator (prove-deep.md R7) supplies, via the Task tool prompt:

- `sorry_id` — the sorry whose `coverage_state: cited_by_reference`
  annotation is being verified
- `original_description` — the NL sub-problem text (from the upstream
  decomposition step)
- `reference_theorem` — the citation excerpt; this is the body of
  E4's `coverage_citation` field (with the `-- cited from reference: `
  prefix stripped) or the matching `references[].matching_statement`
- `declaration_text` — the Lean signature produced by
  sub-autoformalize for this sub-problem
- `sandbox` — sandbox dir (passed through to `verify_citation.py`)

## Workflow

1. **Build the user message** with the three inputs (czy `:243-247`):

   ```
   Original sub-problem (natural language):
   <original_description>

   Reference theorem (natural language):
   <reference_theorem>

   Lean signature (declarationText):
   <declaration_text>
   ```

2. **Single LLM call.** System prompt is the
   `REFERENCE_VERIFY_SYSTEM` block below; user message is from step 1.
   Output MUST be a JSON object per the schema in the system prompt.

3. **Persist via `verify_citation.py`** (T2 bundling). Write the
   subagent's stdout JSON to `$SANDBOX/_citation_verify_$SORRY_ID.json`,
   then call:

   ```bash
   python3 theme/scripts/verify_citation.py \
       --mode reference \
       --sorry-id "$SORRY_ID" \
       --subagent-json-file "$SANDBOX/_citation_verify_$SORRY_ID.json" \
       --sandbox "$SANDBOX"
   ```

   The script parses the JSON, validates, mutates `sorry_backlog.yaml`
   (`citation_verified` + `done_reason: reference_axiom` ONLY on PASS;
   Rule 3 Layer 1 invariant), and emits one `citation-verified`
   milestone with `verifier: reference_llm`.

## Output Contract

- The subagent emits a JSON OBJECT (not array) on stdout in the format
  below.
- The orchestrator pipes that to `verify_citation.py --mode reference`;
  the script's exit code (0/2/3/4) is the success signal.
- One `citation-verified` milestone per invocation.

## Guardrails

- Do NOT mutate `Main.lean` or any `.lean` file. The reference path is
  **non-destructive** by design (czy `:215`); only the library path
  mutates source.
- Do NOT mark `state=DONE` on FAIL. Statement integrity (Rule 3) is
  the priority over throughput; an unverified citation must NOT be
  promoted.
- If the JSON parse fails, the wrapping script writes
  `citation_verified: false` (treats as FAIL per czy `:268-272`). The
  prover takes over for this sorry in Phase 2.
- This skill produces a **soft verdict** — Layer 4
  (`judge-integrity.ts`) is the load-bearing audit at promotion time.
  An LLM-verified `reference_axiom` is NOT a type-correct proof, just
  a semantically-aligned NL claim.

---

## REFERENCE_VERIFY_SYSTEM (verbatim port from czy `:177-204`)

You are verifying whether a PDF reference citation legitimately covers a sub-problem that has been formalized into a Lean signature.

You see THREE inputs:
  1. Original sub-problem (natural language) — what the prover was asked to prove.
  2. Reference theorem (natural language) — the PDF excerpt that helperReferenceSubAgent claims covers the sub-problem.
  3. Lean signature (declarationText) — the actual type produced by sub-autoformalize for input (1).

Your job: confirm that the reference theorem (2) genuinely closes the Lean type (3), which represents the sub-problem (1).

ALL three checks MUST pass for verified=true:

**A. Hypothesis match** — every assumption in (3)'s Lean signature is implied by what (2) provides; (2) does not require extra hypotheses absent from (3).

**B. Conclusion coverage** — (2)'s conclusion must logically entail (3)'s conclusion. This check passes when (2) proves the same claim as (3), or when (3) is a special case of (2)'s more general result. This check fails when (2)'s conclusion is weaker than (3), addresses a different quantity, or points in a different direction.

**C. Type-level coherence** — the mathematical content of (2) must be semantically compatible with (3)'s Lean type. PDF references naturally omit Lean-specific boilerplate (MeasureSpace, ProbabilityMeasure instances, FiniteDimensional, etc.) that sub-autoformalize adds; their absence from (2) does not affect this check. This check fails when (2) addresses a fundamentally different mathematical structure (e.g., discrete vs. continuous, finite vs. infinite-dimensional) that cannot plausibly instantiate (3).

### Common failure modes (DO NOT mark these as verified)

- (2) proves convergence in probability while (3) is about almost-sure convergence.
- (2) assumes bounded support while (3) assumes only finite variance.
- (2) gives a one-sided bound while (3) requires two-sided.
- (2) is stated for a different mathematical object that cannot specialize to what (3) requires.

Output ONLY valid JSON, no fences:
```
{
  "verified": true | false,
  "reasoning": "<one sentence: which check passes/fails and why, in plain language>"
}
```
