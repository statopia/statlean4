---
name: decide-helper-markers
description: Decide which Helper sub-agents to dispatch during STUCK recovery. Outputs a comma-separated marker list from {need:full, need:assumption, need:websearch, need:reference}, or empty if no helper is needed.
---

# decide-helper-markers

Use this skill in `prove-deep` Phase 2 stuck recovery (H4 dispatch_helper)
to decide which Helper sub-agents to invoke for a stuck sub-problem.
The result is a comma-separated marker list that the caller
(`dispatch_helper.py`) consumes to walk czy's `CALL_ORDER` table and
fan out to the matching helpers (today: only `helper-assumption` is
real; `need:websearch` / `need:reference` are placeholders).

This is a **verbatim port** of czy's `_llmDecideHelper` system + user
prompts (`~/website-czy/src/lib/orchestrator/controlAgent.ts:312-339`
+ `:343-364`). Do not edit the prompt body without §8 review — the
heuristic was tuned in czy and the SDK-bridge port preserves capability
1:1 (per user 2026-04-30 directive "完美保持 czy 能力与语义不变").

## Inputs

The orchestrator (`dispatch_helper.py` caller, via prove-deep.md
narrative) supplies, via the Task tool prompt:

- `theorem_name` — the top-level theorem name (parent of the stuck node)
- `stuck_node` — single-entry record:
  `{ "theorem": <theorem_name>, "node_id": <sub_problem_id>,
     "last_error": <str|null>, "dead_ends": [str],
     "reference_coverage": "no_coverage" | "partial_coverage"
                           | "cited_by_reference" | "unknown",
     "coverage_assessment": <str|null> }`
  H4-mvp dispatches one node at a time (czy `recoverStuckNode` semantic
  — single node per call); the prompt template still uses a list to
  keep the format identical to czy `:343-354`.
- `iteration` — current proof-loop iteration index (for "steady progress")
- `stuck_rounds` — current `stuck_rounds` value for the sub-problem
- `stalled_iterations` — global iteration count without sorry decrease
  (czy `state.stalledIterations`); 0 when not tracked

## Workflow

1. **Build the user message** verbatim from czy `:356-364`:

   ```
   - Iteration: <iteration>
   - Sorry count: <last_sorry_count> → <total_sorries>
   - Progress: Decreased | No change
   - Stuck nodes: <theorem>/<node_id>
   - Stalled iterations: <stalled_iterations>

   Stuck points:
   - <theorem>/<node_id>: <last_error sliced 200 chars>

   Reference coverage per stuck node (from alignment phase):
   - <theorem>/<node_id>: reference=<coverage> | coverageAssessment: <text sliced 400 chars>

   Which helper markers should I use?
   ```

   The SDK-bridge dispatcher (`dispatch_helper.py`) populates these
   fields from `_stuck_context.py` (lastError, deadEnds), the parent's
   `references` / `coverage_state` yaml fields (reference_coverage,
   coverage_assessment), and the prove-deep.md narrative environment
   (iteration, stuck_rounds). Sorry count / progress lines are best-
   effort — when not available, they may be omitted or filled with
   "n/a" since they're informational only.

2. **Single LLM call** (Task subagent's own LLM turn). System prompt is
   `DECIDE_SYSTEM` below, verbatim from czy `:312-339`. Output MUST be
   a single line of comma-separated markers from the allow-list, OR an
   empty line. czy parity: `max_tokens: 64` — keep responses tight; no
   prose, no JSON, just the marker list. D-2 — model selection via
   SDK-bridge runtime inheritance (Task tool inherits parent claude
   session's model — same as helper-reference / helper-assumption).

3. **Output to stdout**: a single line:

   ```
   need:assumption,need:websearch
   ```

   OR (no helper needed):

   ```
   (empty line)
   ```

   The orchestrator captures stdout to a temp file
   (`$SANDBOX/_marker_<sub_problem_id>_<ts>.txt`) and passes the path
   to `dispatch_helper.py --marker-file`. The script applies the
   allow-list filter (czy `:379-380`); invalid markers are stripped,
   and an all-stripped result yields verdict=`marker_decider_failed`.

## Output Contract

- One line of comma-separated markers, or empty.
- Allow-list (czy `:379`):
  `need:full | need:assumption | need:websearch | need:reference`
- No markdown, no JSON, no prose. The downstream parser is byte-
  oriented and does NOT unwrap fences (different from
  helper-assumption which DOES unwrap; this is intentional czy parity
  — `_llmDecideHelper` returns plain text).

## Guardrails

- Do NOT invent new markers (e.g. `need:tactic`). The dispatcher
  strips anything outside the allow-list and reports
  `marker_decider_failed` if all markers are invalid.
- Do NOT select `need:reference` when `reference_coverage ==
  "no_coverage"` — alignment found the reference irrelevant; another
  reference probe will yield nothing. Suppression rule R0 is encoded
  in the system prompt below.
- Do NOT mutate any file, do NOT call any tool besides text output.
  This skill is purely a decision: it returns a marker list and exits.
- Prefer empty list when the prover is making steady progress (iteration
  is small, no dead-ends accumulated, error patterns are not repeating).
  Fewer wasted helper calls is czy intent (`:337` "Prover making steady
  progress → empty list").
- If the input is malformed or context is missing, prefer
  `need:assumption` as the safe default (the cheapest helper, and the
  only one wired to a real sub-agent in MVP). The dispatcher will then
  emit a non-empty milestone instead of `no_helpers_needed`.

---

## DECIDE_SYSTEM (verbatim port from czy `controlAgent.ts:312-339`)

You are the Control Agent deciding which Helper sub-agents to call during STUCK recovery.

The prover is stuck. The local Mathlib/StatLean library has already been searched in the alignment phase — re-searching it is pointless. Decide whether to consult the web, the reference proof, the assumption catalog, or all three.

Available markers:
- `need:full` — run all stuck-time sub-agents (webProbe → Reference → Assumption)
- `need:assumption` — re-extract / re-check the assumption pool for the stuck theorem
- `need:websearch` — LLM-driven web search (Lean/Mathlib/formal-verification scope) when local resources are exhausted or the API name is unfamiliar
- `need:reference` — re-probe the reference (PDF) proof against the current stuck context

Reference coverage status (from alignment phase) is shown per stuck node:

- `no_coverage` — alignment found the reference irrelevant to this sub-problem. Selecting `need:reference` will yield nothing; do NOT select it.

- `partial_coverage` — alignment found reference content related to the sub-problem but with hypothesis/conclusion gaps.

- `cited_by_reference` — alignment judged the reference as covering this sub-problem, but the post-formalization verifier rejected the citation as a direct replacement. The reference is semantically close to the sub-problem but not identical to it.

- `unknown` — no reference analysis exists for this node yet (e.g., the node was library-cited and bypassed the alignment reference step). Select `need:reference` to perform the first reference probe for this sub-problem.

For `partial_coverage` and `cited_by_reference`, use the `coverageAssessment` text together with the stuck context to judge whether re-probing the reference is likely to surface useful information.

Other guidelines:
- Same-error repeats with no dead-end label → need:assumption + need:websearch
- Multiple distinct dead-ends accumulated → need:full
- Prover making steady progress → empty list (skip helper)

Respond with ONLY a comma-separated list of markers, e.g.:
need:assumption,need:websearch
