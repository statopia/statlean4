---
name: helper-library-coverage
description: Check whether any Mathlib/StatLean library lemma directly covers each decomposed sub-problem. Runs token-extract → search_lemmas tool calls → judge-LLM for each sub-problem; emits a JSON array per sub-problem with coverage verdict and matched lemma details.
---

# helper-library-coverage

Use this skill in `prove-deep` Phase 0 R5.5 (alignment batch, BEFORE R6
helper-reference dispatch) to check each child sorry_item of a decomposed
parent against the Mathlib/StatLean lemma index. The result feeds the
`coverage_state: cited_by_library` + `library_hit` fields on child items,
enabling E11's R7 library path.

This is a **port** of czy's `SearchSubAgent.checkLibraryCoverage`
(`~/website-czy/src/lib/orchestrator/helperSearchSubAgent.ts:115-189`).
TOKEN_EXTRACT_SYSTEM and JUDGE_SYSTEM prompts are verbatim ports per
`docs/H3_LIBRARY_COVERAGE_SPEC.md` §3.2 verbatim-port commitment. Do not
edit the prompt bodies without §8 review.

Constants (czy `:248-250`, byte-faithful):
- `MAX_TOKENS = 6`
- `PER_TOKEN_LIMIT = 10`
- `MAX_CANDIDATES = 30`

## Inputs

The orchestrator (prove-deep.md R5.5) supplies, via the Task tool prompt:

```
Theorem: <theorem_name>
Sub-problems to check:
1. [<id>] <description>
2. [<id>] <description>
...
```

## Workflow

For each sub-problem in the input list, run the 3-step pipeline below.
Process sub-problems **sequentially** (or in parallel if the Task runtime
supports it — either is correct). On ANY failure in steps 1/2/3, emit
`coverage: "needs_proof"` for that sub-problem and continue to the next —
do NOT abort the whole batch.

### Step 1 — Token extraction

Call LLM with the TOKEN_EXTRACT_SYSTEM system prompt (below) and user
message:

```
Sub-problem description:
<description sliced to first 800 characters>
```

Parse the JSON response: `{"tokens": ["token1", "token2", ...]}`. Extract
up to **6** tokens. If the response is malformed or empty, treat as 0
tokens and fall through to `needs_proof` for this sub-problem.

### Step 2 — search_lemmas tool calls

For each token from step 1, call the `search_lemmas` MCP tool with:
- `query`: the token string (one per call)
- `mode`: `"name"` (substring match on lemma name)
- `limit`: `10`

Collect all result lines. Deduplicate by the composite key
`(name|kind|location)` — if two lines have the same name, kind, and
location, keep only one. Stop collecting once you have **30** unique
candidates total (MAX_CANDIDATES cap).

Parse each result line using the format `NAME\tKIND  [source]` or
`NAME\tKIND  LOC  [source]`:
- Extract `name` (before the tab)
- Extract `kind` (after tab, before double-space or end)
- Extract optional `location` (between double-space separators)
- Extract `source`: `mathlib` | `statlean` | `extern`

Lines that don't match the expected format are silently dropped.

If no candidates are found for any token (all `[no lemmas found...]`
responses), emit `coverage: "needs_proof"` for this sub-problem.

### Step 3 — Judge

Call LLM with the JUDGE_SYSTEM system prompt (below) and user message:

```
Sub-problem:
<description>

Candidates (name, kind, optional location, source):
<numbered list, one candidate per line: "N. name [kind] [location] [source]">
```

Parse the JSON response:
```json
{"verdict": "cited"|"no_match", "matchedName": "<name>"|null, "reasoning": "<sentence>"}
```

**Anti-hallucination guard (czy `:416-418`):** After parsing, check that
`matchedName` is verbatim from the candidate list (exact string match on
the `name` field). If `matchedName` is not in the candidate list, override
the verdict to `"no_match"` and set `reasoning: "judge picked unknown name"`.

If verdict is `"cited"` AND `matchedName` is in the candidate list:
- Find that candidate entry (to get source, location, kind)
- Emit `coverage: "cited_by_library"` with the matched lemma fields

If verdict is `"no_match"` (or hallucination guard fired):
- Emit `coverage: "needs_proof"`

## Output Contract

Emit a single JSON array to stdout (no markdown fences, no prose):

```json
[
  {
    "sub_problem_id": "<id>",
    "coverage": "cited_by_library",
    "matched_name": "MeasureTheory.integral_nonneg",
    "matched_source": "mathlib",
    "matched_location": "Mathlib/MeasureTheory/Integral/Bochner.lean:42",
    "matched_kind": "lemma",
    "candidates_queried": ["integral_nonneg", "nonneg_integral"],
    "reasoning": "Conclusion coverage check passes: integral_nonneg states exactly the nonnegativity of the Bochner integral for nonneg integrands."
  },
  {
    "sub_problem_id": "<id>",
    "coverage": "needs_proof",
    "matched_name": null,
    "matched_source": null,
    "matched_location": null,
    "matched_kind": null,
    "candidates_queried": ["condExp_add", "condExp_const"],
    "reasoning": "No candidate's conclusion entails the full conditional expectation linearity claim."
  }
]
```

Fields for `needs_proof` entries: `matched_name`, `matched_source`,
`matched_location`, `matched_kind` are all `null`.

## Persistence

After emitting the JSON array to stdout, the orchestrator will capture it
to `$SANDBOX/_library_coverage_$PARENT_ID.json` and call:

```bash
python3 theme/scripts/extract_library_coverage.py \
    --parent-id "$PARENT_ID" \
    --subagent-json-file "$SANDBOX/_library_coverage_$PARENT_ID.json" \
    --sandbox "$SANDBOX"
```

The script writes `coverage_state: cited_by_library` + `library_hit:
{name, source, location, kind}` on child items (Rule 3 Layer 1: only these
two fields). One `library-coverage-extracted` milestone fires per parent_id.

## Guardrails

- Do NOT mutate `Main.lean` or any `.lean` file. This skill is purely
  a classification-and-annotate operation.
- Do NOT mark any sorry as `state=DONE`. Library coverage annotation is
  H3's job; compilation verification is E11's (verify_citation.py).
- Do NOT invent lemma names. The judge may only select names verbatim from
  the candidate list produced by `search_lemmas`.
- Do NOT use the strong model. H3 is a pipeline classification step
  (alignment phase), not a prove agent. Default model only
  (CLAUDE.md Rule 2 exemption per spec §2.6, D-8).
- If the JSON output is malformed or empty, the wrapping script exits 2 and
  no yaml mutation occurs. Do not try to rescue the JSON — child sorries
  stay `needs_proof` and continue through R6/R7/Phase 1 unchanged.

---

## TOKEN_EXTRACT_SYSTEM (verbatim port from czy `:252-261`)

> Byte-equal port of czy's `TOKEN_EXTRACT_SYSTEM` template literal.
> Wrapped in a fenced code block to preserve czy's single-line-per-
> paragraph layout (no Markdown soft-wrap drift). H3 §8 code review
> S3.2 fixup.

```
You are extracting Mathlib/StatLean lemma name keywords from a sub-problem description for a search query.

Output ONLY valid JSON, no fences or prose. Format:
{"tokens": ["token1", "token2", ...]}

Rules:
- Each token is a short identifier-style keyword likely to appear in a Lean lemma name (e.g. "integral_nonneg", "Finset.sum_comm", "norm_add_le", "iIndepFun", "condExp").
- Prefer Mathlib naming conventions: snake_case for theorems, CamelCase for namespaces.
- Output 3 to 6 tokens. Fewer is fine if the description is narrow.
- Do NOT include verbs ("prove", "show"), generic words ("theorem", "lemma"), or punctuation.
```

---

## JUDGE_SYSTEM (verbatim port from czy `:358-379`)

You judge whether any candidate Mathlib/StatLean lemma already covers a given sub-problem.

Strict checks — ALL three must pass for "cited":
1. Hypotheses match — every assumption of the sub-problem is present in (or implied by) the candidate's typical statement; the candidate does not assume incompatible extra conditions.
2. Conclusion coverage — the candidate's conclusion must logically entail the sub-problem's claim. This check passes when the candidate proves the same claim, or when the sub-problem is a special case of the candidate's more general result. This check fails when the candidate's conclusion is weaker than the sub-problem's claim, addresses a different quantity, or points in a different direction.
3. Direct usability — the candidate is callable as written, without major adapter lemmas to bridge type mismatches.

You see only the candidates' names + kinds (and optional location). Do NOT invent statements; reason from the name + standard Mathlib naming conventions.

Output ONLY valid JSON, no fences. Format:
{
  "verdict": "cited" | "no_match",
  "matchedName": "<exact candidate name from the list>" | null,
  "reasoning": "<one short sentence stating which checks pass or fail>"
}

You MUST select matchedName from the candidate list verbatim — never invent a new name. If unsure, return "no_match".
