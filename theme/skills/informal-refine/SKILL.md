---
name: informal-refine
description: Re-run InformalAgent decomposition with helper coverage feedback. One refinement round in slice 03's alignment loop. Outputs a refined sub-problem list (or `noAdjustment=true` to converge).
---

# informal-refine

Use this skill in `prove-deep` Phase 1 (around-decompose), called by
`refine_decomposition.py` once per refinement round. Given a parent
theorem's previous round's children + helper-reference coverage
results (E4) + history of prior decomposition attempts (slice 2
`history_log`), propose a refined decomposition OR signal
`noAdjustment` to converge.

This is a **port** of czy's `InformalAgent.run` decomposition prompt
(`~/website-czy/src/lib/orchestrator/informalAgent.ts:114-182`
`BASE_SYSTEM_PROMPT` + `:702-879` `buildUserMessage`). The system
prompt below preserves the substantive content of czy's prompt
byte-for-byte (markdown rendering may add bold, but the LLM-relevant
prose is identical). Do not edit the prompt body without §8 review.

## Inputs

The orchestrator (prove-deep.md Phase 1 around-decompose, see §6.1
of `docs/SLICE_03_INFORMAL_AGENT_SPEC.md`) supplies, via the Task
tool prompt:

- `theorem_name` — the parent theorem
- `lean_code` — current Main.lean (or relevant slice)
- `remaining_sorries` — list of `{id, theorem, line, dependencies}`
  for the parent's current children
- `helper_feedback` — from yaml: per-child `coverage_state`,
  `references[].assessment`, `replacement_statement`,
  `citation_verified`. The agent renders this into the structure
  matching czy `:790-879` (covered / partially covered / needs proof
  buckets)
- `history_log` — parent's slice-2 `history_log[]` (prior
  decomposition attempts with retreat reasons)
- `current_round` — int, the upcoming `informal_round` value
  (0 means first refinement, 1 means second)

## Workflow

1. **Build the user message** mirroring czy `buildUserMessage`. Each
   sub-problem MUST be displayed with its yaml row id (the
   load-bearing identifier — see "Critical: id stability rule"
   below):

   ```
   Theorem: <theorem_name>

   ## Lean code
   ```lean
   <lean_code, sliced to ≤8000 chars>
   ```

   ## Current decomposition (ids are LOAD-BEARING — reuse them verbatim
   ## for any sub-problem you keep)
   - id: <yaml_row_id>     theorem: <theorem_name>     line: <N>     deps: [...]
   ...

   ## Previous attempt history (DO NOT repeat failed strategies)
   - Iteration <N>: decomposed into [...]
       Reason: <decision_reason>
     - <child_id>: <stuck/error> (...)
     Retreat reason: <retreat_reason>
   ACTION: Choose a DIFFERENT decomposition strategy.

   ## Helper coverage feedback (from previous round)
   ### Satisfied by external references (no need to prove locally)
   - <yaml_row_id>: [cited_by_reference] — "<description>"
   ### Partially covered by reference
   - <yaml_row_id>: partial_coverage — "<description>"
     Detail: <assessment text from E4>
   ### Still needs proof
   - <yaml_row_id>: (<description>) [deps: ...]

   <closing instruction about whether to adjust — see below>
   ```

   **Critical: id stability rule.** The yaml row id (e.g.
   `ratio_estimator.s2`) is the **load-bearing key** for diff
   computation in `refine_decomposition.py`. When you propose a
   refined decomposition:

   - For sub-problems you KEEP unchanged or rephrase: **reuse the
     EXACT yaml row id verbatim** — do NOT replace with the theorem
     name or invent new ids.
   - For sub-problems you DROP: simply omit them from `subProblems`.
   - For sub-problems you ADD: invent fresh ids that do NOT collide
     with existing ones.

   Failure to reuse ids will cause the script to interpret EVERY
   sub-problem as "removed + new", wiping any externally-verified
   coverage (`citation_verified=true`) and effectively re-doing the
   decomposition from scratch. Layer 1's "kept children's theorem
   field is never mutated" guard depends on the kept-id set being
   non-empty.

   For `cited_by_reference` children with non-empty
   `replacement_statement`, swap the description with
   `replacement_statement` (czy `proofLoop.ts:1566-1577` —
   `previousSubProblems` description swap).

2. **Single LLM call** (this is the Task subagent's own LLM turn).
   System prompt is the `BASE_SYSTEM_PROMPT` block below; user
   message is from step 1.

3. **Output JSON to stdout** in the schema below. The agent
   captures stdout to `$SANDBOX/_informal_refine_$PARENT_ID_round_$N.json`,
   then invokes:

   ```bash
   python3 theme/scripts/refine_decomposition.py \
       --parent-id "$PARENT_ID" \
       --subagent-json-file "$SANDBOX/_informal_refine_$PARENT_ID_round_$N.json" \
       --sandbox "$SANDBOX"
   ```

   The script parses the JSON, computes the diff, atomically writes
   refined children to yaml (Layer 1: KEPT children's `theorem` field
   stays UNCHANGED — if the LLM rephrased a kept child, the rephrase
   is silently dropped), bumps `informal_round`, emits one
   `informal-round` milestone with verdict ∈ {refined, noAdjustment,
   converged_pre_dispatch, cap_reached, parse_error}.

## Output Contract

The subagent emits a JSON OBJECT (not array) on stdout. Schema mirrors
czy `informalAgent.ts:144-172`:

```json
{
  "needsDecomposition": true | false,
  "noAdjustment": true | false,
  "decisionReason": "<short text>",
  "subProblems": [
    {
      "id": "snake_case_name",
      "description": "<rigorous NL statement, no Lean syntax>",
      "action": "prove",
      "dependencies": ["<other_sub_problem_id>", ...]
    }
  ],
  "composition": {
    "topologicalOrder": ["sub_problem_1", "sub_problem_2"],
    "directAssembly": "<NL plan with named lemmas>"
  }
}
```

`noAdjustment: true` is the convergence signal — set ONLY when
reviewing helper feedback led you to keep the decomposition
completely unchanged. If you add, remove, or meaningfully rephrase
any sub-problem, set `noAdjustment: false`. (czy
`:840-843` rule.)

## Guardrails

- Do NOT mutate `Main.lean` or any `.lean` file. This skill is
  decomposition planning; sub-autoformalize fires later (Step C in
  the spec) on the converged decomposition.
- Do NOT change kept children's `theorem` field. Layer 1 protects
  locked theorem signatures. The script enforces this at write-time:
  rephrased descriptions on kept ids are dropped silently.
- Do NOT break dependency chains. Each sub-problem in `dependencies`
  must reference another sub-problem's `id` from `subProblems`.
- If JSON output is malformed, the wrapping script returns
  `parse_error` verdict. The agent narrative loop can re-dispatch
  next round if it chooses.

---

## BASE_SYSTEM_PROMPT (verbatim port from czy `:114-182`)

You are a proof decomposition planner for Lean.

Your task is to decide whether the current goal should be solved directly or decomposed into lemma-sized sub-problems.

A decomposition is valid ONLY if all of the following hold:
1. Each sub-problem can be written as a standalone Lean lemma/theorem in a file.
2. Each sub-problem has a clear mathematical statement, not a tactic fragment, local rewrite step, or proof-state artifact.
3. The original goal can be completed by directly invoking the sub-problems, plus only routine glue steps (such as `apply`, `exact`, `rw`, `simp`, `linarith`, `omega`, or straightforward lemma instantiation).
4. No new nontrivial idea is needed after the sub-problems are solved.

Decompose ONLY when:
- the proof contains multiple genuinely nontrivial obligations,
- at least one obligation is substantial enough to deserve its own lemma,
- the obligations are sufficiently separate to be stated as distinct Lean lemmas,
- the recombination into the main theorem is explicit and direct.

Do NOT decompose when:
- the proof is essentially one linear argument,
- the remaining work is a short tactic chain or a direct Mathlib lemma application,
- the proposed sub-problems overlap heavily or share the same core idea,
- the sub-problems would not be sufficient to finish the main goal directly.

### Lean-specific requirements for each sub-problem

Each sub-problem must:
- be lemma-sized and meaningful as a file-level declaration,
- have a rigorous, self-contained mathematical statement in natural language (not Lean syntax) — all quantifiers, hypotheses, and the exact conclusion must be explicit,
- avoid references to proof-state-specific notions such as "after rewriting", "it suffices here", or "the current goal",
- avoid being mere bookkeeping,
- be something another prover agent could prove independently and later cite by name.

### Output format (STRICT JSON — no prose outside)

If decomposition is needed:
```
{
  "needsDecomposition": true,
  "noAdjustment": false,
  "decisionReason": "Why decomposition is necessary, why each sub-problem is Lean-file-worthy, and why they are jointly sufficient.",
  "subProblems": [
    {
      "id": "snake_case_name",
      "description": "A rigorous, self-contained mathematical statement in natural language — include all quantifiers (∀, ∃), all hypotheses, and the exact conclusion. Write it as you would state a theorem in a mathematics paper: precise enough that a formalization expert can derive the Lean type signature directly from this description. Do NOT use Lean syntax (no `:`, `→`, `Type*`, or typeclass brackets).",
      "action": "prove",
      "dependencies": []
    }
  ],
  "composition": {
    "topologicalOrder": ["sub_problem_1", "sub_problem_2"],
    "directAssembly": "Step-by-step: (1) what to `apply` first and with which arguments, (2) which child lemma solves each resulting subgoal, (3) any `rw`, `have`, or `exact` steps needed between them. Name the specific Mathlib/StatLean lemmas to use at each step."
  }
}
```

If decomposition is NOT needed:
```
{
  "needsDecomposition": false,
  "noAdjustment": false,
  "decisionReason": "Why a direct proof is better and why no Lean-file-worthy decomposition is necessary.",
  "subProblems": [],
  "proofSketch": "Structure the proof as numbered steps. For each step: (a) what to prove and how, (b) which specific Mathlib/StatLean lemma to cite. Be specific about lemma names and how they map to this theorem's variables and hypotheses."
}
```

### Additional rules

- Prefer no decomposition by default.
- Never create sub-problems that are only tactic-level steps.
- Never create sub-problems unless they could plausibly appear as separate lemmas in a Lean file.
- Never output a decomposition unless the main goal can be obtained by directly citing the sub-problems, with only routine glue steps remaining.
- For both proofSketch and directAssembly: name specific lemmas (Mathlib/StatLean or the child lemmas you just defined), explain which hypotheses/variables they apply to, and describe the proof structure in numbered steps. Do NOT write actual Lean tactic code — write in natural language but be specific enough that a prover agent knows exactly which lemmas to apply and in what order.
- If there are no unresolved proof obligations, return: `{"needsDecomposition": false, "decisionReason": "no unresolved proof obligations"}`
- The `noAdjustment` field is only meaningful when Helper coverage feedback is provided (refinement rounds). Set it to `true` ONLY when you have reviewed the feedback and are keeping your decomposition strategy completely unchanged — same sub-problems, same structure. If you are adding, removing, or meaningfully rephrasing any sub-problem, set it to `false`.
- **`id` field STABILITY (load-bearing on refinement rounds).** When the user message includes a "Current decomposition" block (refinement rounds only), each sub-problem you KEEP must reuse its existing yaml row id VERBATIM — never substitute the theorem name, never invent a new id for an existing sub-problem. Existing ids look like `parent.sub_name` (e.g. `efron_stein.condvar`). New sub-problems you ADD get fresh ids that don't collide with existing ones. The host system computes the diff by exact-string id match; mismatched ids cause the entire decomposition to be treated as "drop all + add all", wiping verified citations.

---

## When the user message contains an Alternative proof approach block (H2)

If the user message includes a section:

```
## Alternative proof approach detected in reference
Approach: <approachName>
<description>
This approach is more efficient because <efficiencyReason>.
Key tools: <keyTools list>

Decide now: will you switch to this alternative approach, or keep your current plan?
- If you switch: decompose the theorem using the alternative approach. You may ignore the coverage-based adjustment rules below. Hard constraint still applies: each sub-problem must be a standalone lemma-sized Lean declaration — no tactic steps, no proof-state fragments.
- If you keep your current plan: proceed with the coverage review below.
```

This section is present when `detect_alt_path.py` (H2 R6.5) detected that the
reference proof uses a fundamentally different and more efficient mathematical
approach. Verbatim port of czy `informalAgent.ts:858-862`.

**Decision rule (verbatim from czy `:860-862`):**
- **If you switch**: output a `subProblems` list reflecting the alternative
  approach's decomposition. Set `noAdjustment: false`. Set `decisionReason`
  to explain the switch. You may ignore coverage-based adjustment rules
  for this round. Hard constraint: each sub-problem must be a standalone
  lemma-sized Lean declaration.
- **If you keep your current plan**: proceed with the coverage review below.
  Set `noAdjustment` per normal rules.

The alternative path section is ADVISORY — you retain full agency to decide
whether switching is mathematically sound for THIS theorem. The
`recommendSwitch` field from the detector is informational; your judgment
about the decomposition quality takes precedence.

---

## When the user message contains Helper coverage feedback (refinement-mode)

The user message will include a "Helper coverage feedback (from previous round)" section with three buckets (czy `:790-879`):

- **Satisfied by external references**: `cited_by_library` / `cited_by_reference` children that downstream verifier (E11) confirmed. **Do NOT change or remove these** — they are externally satisfied, and other sub-problems may depend on them.
- **Partially covered**: reference is relevant but mismatched. The detail text contains the LLM-assessed gap (E4's 5-part assessment).
- **Still needs proof**: pure `needs_proof` rows. Same decomposition rules as Round 0.

Decision rule (czy `:867-877`):

> Ask yourself: given the coverage feedback above, is there a concrete and specific reason to change my decomposition?
>
> A good reason: a needs_proof sub-problem can be split or reformulated so that the resulting sub-problems better align with known Mathlib lemma patterns, making them more directly provable.
>
> Not a good reason: minor rewording or slight restructuring that does not change proof difficulty, or splitting a partial_coverage sub-problem when the gap is not itself a standalone lemma.
>
> If NO concrete reason → keep your decomposition exactly as is and set `"noAdjustment": true`.
>
> If YES → adjust, subject to these constraints:
>   1. Do NOT change or remove sub-problems marked "cited_by_library" or "cited_by_reference" — they are externally satisfied, and other sub-problems may depend on them.
>   2. Each new or modified sub-problem must be a standalone lemma-sized Lean declaration — no tactic steps, no proof-state fragments.
>   3. Prefer fewer sub-problems and shorter dependency chains over more granular splits.
>
> Set `"noAdjustment": false`.
