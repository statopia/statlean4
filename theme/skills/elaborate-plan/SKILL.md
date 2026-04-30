---
name: elaborate-plan
description: Expand a brief proof sketch (direct mode) or assembly outline (assembly mode) into a step-by-step detailed Lean proof plan that the prover consumes as primary guidance. One LLM call per parent, AFTER slice 03's alignment loop converges.
---

# elaborate-plan

Use this skill in `prove-deep` Phase 1 Step C-pre, called by
`elaborate_plan.py` once per parent immediately after slice 03's
refinement loop exits (either via `coverage_stable=true` or
`informal_round >= 2`). Given a parent theorem's converged
decomposition + brief seed (`directAssembly` for decomposed parents,
`proofSketch` for non-decomposed) + helper coverage feedback, expand
the brief seed into a detailed step-by-step plan citing specific
Mathlib/StatLean lemma names, hypothesis bindings, and intermediate
`have` / `obtain` types.

This is a **port** of czy's `InformalAgent.elaboratePlan`
(`~/website-czy/src/lib/orchestrator/informalAgent.ts:477-513`),
dispatching ONE of two system prompts based on the `mode` arg:

- `mode=direct` → `ELABORATION_DIRECT_PROMPT`
  (czy `informalAgent.ts:188-205`) — for parents with NO children
  (the parent IS the leaf the prover will attack directly)
- `mode=assembly` → `ELABORATION_ASSEMBLY_PROMPT`
  (czy `:207-223`) — for parents with children (the prover writes
  the parent body that combines children proved separately)

Both prompts forbid Lean tactic syntax in the output — natural
language only. The prover translates the NL plan into tactics.

The prompt bodies below preserve the substantive content of czy's
prompts byte-for-byte (markdown rendering may add bold, but the
LLM-relevant prose is identical). Do not edit either prompt body
without §8 review.

## Inputs

The orchestrator (prove-deep.md Phase 1 Step C-pre, see §6.1 of
`docs/H1_ELABORATE_PLAN_SPEC.md`) supplies, via the Task tool prompt:

- `mode` — `"direct"` or `"assembly"` (selects which embedded prompt
  block becomes the system prompt this turn)
- `theorem_name` — the parent theorem
- `lean_code` — current Main.lean (sliced to ≤4000 chars per czy
  `:950`)

For `mode=direct`:
- `remaining_sorries` — list of `{id, theorem, line, dependencies}`
  for sub-problems still in `coverage_state ∈ {needs_proof,
  partial_coverage}`. Closed sub-problems (`cited_by_library` /
  `cited_by_reference` with `citation_verified=true`) are noted in
  `confirmed_lemmas` instead.
- `brief_strategy` — the parent's `proof_sketch` field (slice 03's
  persisted seed)
- `confirmed_lemmas` — list of `{id, coverage, context}` for
  children with `cited_by_library` / `cited_by_reference` (use these
  directly; matching_statement / assessment provides the canonical
  reference text)
- `partial_lemmas` — list of `{id, context}` for children with
  `partial_coverage`

For `mode=assembly`:
- `child_lemmas` — list of `{id, description, dependencies}` for
  **every child including closed (cited_by_*) ones**. czy's
  `ELABORATION_ASSEMBLY_PROMPT` (`:207-223`) explicitly tells the
  LLM to "assemble the proof by citing the child lemmas in
  topological order"; closed children are still cited by id, just
  don't need to be "proved" first because they're already done.
  This is distinct from `mode=direct` where the renderer FILTERS to
  uncovered children.
- `brief_assembly` — the parent's `direct_assembly` field (slice 03's
  persisted seed for decomposed parents)

Both modes also carry:
- `gotchas` — workspace API gotchas (≤1500 chars)
- `statlean_index` — workspace StatLean local API index (≤2000 chars)

## Workflow

1. **Build the user message** mirroring czy `buildElaborationMessage`
   (`informalAgent.ts:934-1025`). Sections rendered in order, gated
   by `mode`:

   ```
   Theorem: <theorem_name>

   ## Lean code
   ```lean
   <lean_code, sliced to ≤4000 chars>
   ```

   ## (mode=assembly) Child sub-lemmas (already proved — cite by exact ID)
   - <id>: <description> (depends on: <deps...>)
   ...

   ## (mode=assembly) Brief assembly sketch (expand this into a detailed plan)
   <brief_assembly>

   ## (mode=direct) Sorry sites to prove
   - <theorem> at line <line> (deps: <deps...>)
   ...

   ## (mode=direct) Brief proof strategy (expand this into a detailed plan)
   <brief_strategy>

   ## (mode=direct) Confirmed Mathlib/reference lemmas (use these directly)
   - <id>: [<coverage>] <context, sliced to ≤400 chars>
   ...

   ## (mode=direct) Partially covered (reference exists but may need adaptation)
   - <id>: <context, sliced to ≤400 chars>
   ...

   ## API gotchas
   <gotchas>

   ## StatLean local API index
   <statlean_index>

   <closing instruction — assembly: "Write a numbered assembly plan
   citing each child by exact id." direct: "Write a numbered step-by-
   step plan for each remaining sorry site.">
   ```

2. **Single LLM call** (this is the Task subagent's own LLM turn).
   System prompt is **either** `ELABORATION_DIRECT_PROMPT` (mode=direct)
   **or** `ELABORATION_ASSEMBLY_PROMPT` (mode=assembly), embedded
   below. User message is from step 1. czy uses `max_tokens: 8000`;
   the Task subagent's default budget covers this.

3. **Output plain text to stdout** — NO JSON wrapping, NO markdown
   fences. The agent captures stdout verbatim to
   `$SANDBOX/_elaborate_plan_${PARENT_ID}.txt`, then invokes:

   ```bash
   python3 theme/scripts/elaborate_plan.py \
       --parent-id "$PARENT_ID" \
       --subagent-text-file "$SANDBOX/_elaborate_plan_${PARENT_ID}.txt" \
       --mode "$MODE" \
       --sandbox "$SANDBOX"
   ```

   The script (T2 atomic): convergence pre-check, idempotence pre-check,
   atomic yaml write of `parent.detailed_proof_plan`, emits one
   `plan-elaborated` milestone with verdict ∈ {elaborated,
   skipped_already_present, skipped_empty_plan}.

## Output Contract

Plain text body of the elaborated plan. NO JSON, NO markdown wrapping
fences (the prover renders the plan into its task_objectives.md as-is
under the header "Detailed proof plan (Informal Agent — use this as
primary guidance)" — czy `proverAgent.ts:570-572`).

Empty / whitespace-only output is treated as a failed elaboration —
the script writes `verdict=skipped_empty_plan`, leaves the yaml field
None, and the prover falls back to the brief seed (matches czy
`:511 catch → null` semantic).

## Guardrails

- Do NOT mutate `Main.lean` or any `.lean` file. This skill produces
  guidance text only; the prover writes Lean code.
- Do NOT write Lean tactic syntax (no `by`, `rw [...]`, `exact ...`,
  `apply`, `simp`, `linarith`). Use natural language. The prover
  translates the NL plan into Lean tactics. (Both prompts enforce
  this rule explicitly.)
- Do NOT change kept children's structure. The decomposition is
  FROZEN at this point — slice 03's alignment loop has exited; H1
  consumes the converged children, never alters them.
- Do NOT invent child IDs or rename them in `mode=assembly`. Use
  the exact ids supplied in `child_lemmas`.

---

## ELABORATION_DIRECT_PROMPT (verbatim port from czy `informalAgent.ts:188-205`)

You are writing a detailed Lean proof plan for a prover agent. Your plan will be placed directly in the agent's task file as primary guidance when writing Lean tactics.

Be maximally specific: name exact Mathlib/StatLean lemma names, explain how each theorem hypothesis maps to the lemma's parameters, and describe any intermediate `have` or `obtain` steps with their types.

Write a numbered step-by-step proof plan for each sorry site. For each step:
1. State what the step proves (the goal or subgoal at that point).
2. Name the exact lemma to apply (e.g. `MeasureTheory.integral_mono_ae`, `Real.norm_add_le`).
3. Explain which local hypotheses bind to which parameters of the lemma.
4. If an intermediate `have` or `obtain` is needed, state its name and precise type.
5. If a rewrite is needed, name the equation lemma and direction (← or →).

Rules:
- Do NOT write Lean tactic syntax (no `by`, `rw [...]`, `exact ...`). Write in natural language.
- Use full qualified lemma names when known (e.g. `Finset.sum_comm`, not "commutativity of sum").
- Prioritize Helper-confirmed lemmas (cited_by_library / partial_coverage) — incorporate their exact names.
- For each named lemma, state concretely what it says in terms of this theorem's specific variables and hypotheses.
- If you don't know a specific lemma name, describe the lemma signature (input/output types + conditions) so the agent can search for it.
- A sub-sorry that is `cited_by_library` is already handled — briefly note it but focus on `needs_proof` sorries.

---

## ELABORATION_ASSEMBLY_PROMPT (verbatim port from czy `informalAgent.ts:207-223`)

You are writing a detailed Lean assembly plan for a parent theorem. Its child sub-lemmas have been proved separately and are importable by their IDs. A prover agent will use your plan to write the actual Lean tactics that combine the children into the parent proof.

Write a numbered step-by-step assembly plan:
1. State the top-level proof structure (e.g. "open with `intro h`, split goal via `constructor`", "use `apply Iff.intro`").
2. For each resulting subgoal:
   a. Name which child lemma closes it — use the exact ID from the sub-problem list.
   b. Explain which local hypotheses to pass as arguments to instantiate the child.
   c. Name any glue steps between children (e.g. "apply `simp` with the child result", "use `linarith` combining child outputs").
3. Name any intermediate `have` steps with their precise types and which child supplies them.
4. State the final step that closes the full goal.

Rules:
- Reference child lemmas by their exact IDs (as listed in the sub-problem list below).
- For each child application, state which local hypotheses bind to which parameters.
- Be explicit about ordering: which child is applied first, second, etc., and why.
- Do NOT write Lean tactic syntax — natural language that fully specifies the strategy.
- If the parent goal closes trivially after applying children (e.g. `simp` or `linarith`), say so explicitly with the specific tactic name.
