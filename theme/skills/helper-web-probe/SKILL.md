---
name: helper-web-probe
description: Run a web-search probe to help unstick a Lean 4 / Mathlib proof. Outputs a JSON object with generated query, web hits, fetched content, analysis, and assembled context block for injection into the next prover attack.
---

# helper-web-probe

Use this skill in `prove-deep` Phase 2 stuck-recovery (H4 `dispatch_helper.py`
`need:websearch` arm) to run a three-step web probe: query generation →
web search + deep fetch → analysis. The assembled context block is persisted
by `extract_web_probe.py` to the `webprobe_context` field on the targeted
sorry row so the next prover attack can inject it.

This is a **port** of czy's `SearchSubAgent.webProbe`
(`~/website-czy/src/lib/orchestrator/helperSearchSubAgent.ts:196-242, :444-667`).
The system prompts below are verbatim per `docs/H5_WEB_PROBE_SPEC.md` §3.2
byte-equal commitment — `QUERY_GEN_SYSTEM` from `:451-462` and
`ANALYSIS_SYSTEM` from `:463-470`. Do not edit the prompt bodies without
§8 review.

## Constants (verbatim from czy `:447-449`)

- `DEEP_FETCH_TOP_K = 2` — deep-fetch at most 2 URLs per probe
- `DEEP_FETCH_BYTES = 4000` — truncate each fetched page body to 4000 bytes
- `DOMAIN_WHITELIST = /github\.com|proofwiki\.org|leanprover|mathoverflow|arxiv\.org/i`

## Inputs

The orchestrator (H4 `dispatch_helper.py` narrative, or test harness) supplies
via the Task tool prompt:

- `theorem_name` — the top-level theorem name
- `sub_problem_id` — the sorry_item id that is stuck
- `stuck_context` — JSON object with optional fields:
  - `currentGoal` — the current Lean goal state (sliced to ≤600 chars)
  - `lastError` — the last error message from the prover (sliced to ≤600 chars)
  - `codeAttempted` — the code that was attempted (sliced to ≤600 chars)
  - `deadEnds` — list of failed approaches (last 3, each ≤200 chars)
- `sandbox` — sandbox directory path (passed through to `extract_web_probe.py`)

## Workflow

### Step 1 — Query generation

Using the `QUERY_GEN_SYSTEM` below as your system context, generate one
focused web-search query.

Build the user message from the stuck_context fields (czy `:480-487`):
```
Theorem: <theorem_name>

Current goal:
<stuck_context.currentGoal, sliced to 600 chars>  [if present]

Last error:
<stuck_context.lastError, sliced to 600 chars>  [if present]

Code attempted:
<stuck_context.codeAttempted, sliced to 600 chars>  [if present]

Failed approaches:
- <stuck_context.deadEnds[-3], each sliced to 200 chars>  [if present and non-empty]
```

Output: `{"query": "..."}` — trim and clamp to max 100 chars. If you
cannot produce a valid query, use `<theorem_name> Lean 4 Mathlib` as
the fallback (czy `:513-515`).

### Step 2 — Web search + deep fetch

1. Call the **WebSearch** tool with the generated query and count=5
   (D-2 architectural translation: SDK built-in WebSearch tool replaces
   czy's `/api/web-search` CORS proxy which is not accessible in CLI sandbox).

2. Filter hits by domain whitelist (matches any of: `github.com`,
   `proofwiki.org`, `leanprover`, `mathoverflow`, `arxiv.org`).
   Take the top 2 whitelisted hits (`DEEP_FETCH_TOP_K=2`).

3. For each whitelisted hit: call the `web_fetch` tool on the URL to
   retrieve the page body. Truncate the body to `DEEP_FETCH_BYTES=4000`
   bytes. Prepend a URL header `\n\n--- <url> ---\n` before the body.
   Concatenate all fetched pages into a single `web_fetch_content` string.

   - If `web_fetch` is unavailable: skip deep fetch, set
     `web_fetch_content = ""`. Non-fatal per D-2b.
   - If a specific URL fetch fails: skip that URL (non-fatal, czy `:549-551`).

4. If WebSearch tool is unavailable or returns 0 hits after filtering:
   set `web_hits = []`, `web_fetch_content = ""`. Proceed to Step 3
   (empty-hits fast-path will fire).

### Step 3 — Analysis

**Empty-hits fast-path** (czy `:583-588`): if `web_hits` is empty and
`web_fetch_content` is empty, skip the LLM analysis call and use:
```json
{"findings": "No relevant web results found.", "suggestion": "Try a different approach in the prover; web search returned nothing useful."}
```

Otherwise, using the `ANALYSIS_SYSTEM` below as your system context,
analyse the search results.

Build the user message (czy `:595-602`):
```
Theorem: <theorem_name>

Last error:
<stuck_context.lastError, sliced to 400 chars>  [if present]

Search query: <generated_query>

Hits:
1. <title>
   <url>
   <snippet, sliced to 200 chars>
[up to 5 hits; if none, "(none)"]

Deep-fetched page content (truncated):<web_fetch_content, sliced to 8000 chars>
[if web_fetch_content is non-empty]
```

Output: `{"findings": "...", "suggestion": "..."}`. If the LLM returns
malformed JSON or fails, fall back to:
```json
{"findings": "(no findings)", "suggestion": ""}
```

### Step 4 — Assemble context + emit JSON

Render the assembled context block (czy `renderWebProbeContext` `:633-667`):

```
## Web Probe (stuck recovery for <theorem_name>)
Query: <generated_query>

### Findings
<findings>

### Suggestion
<suggestion>

### Top hits
- <title>
  <url>
[up to 5 hits, only if hits non-empty]

### Deep-fetched content (truncated)
<web_fetch_content.trim().slice(0, 2000)>
[only if web_fetch_content non-empty]
```

**Two truncation points apply (spec §3.2):**
- **(a) Fetch-level cap**: `web_fetch_content` in the output JSON contains
  each page body truncated to `DEEP_FETCH_BYTES=4000` bytes (applied in Step 2).
- **(b) Renderer-level cap**: the deep-fetch block inside `assembled_context`
  further truncates to 2000 chars (`.trim().slice(0, 2000)`) — the final
  context budget for the prover.

Write the assembled output to
`$SANDBOX/_webprobe_${SUB_PROBLEM_ID}_${TIMESTAMP}.json`, then call
`extract_web_probe.py` to persist to yaml and emit the milestone:

```bash
python3 theme/scripts/extract_web_probe.py \
    --sub-problem-id "$SUB_PROBLEM_ID" \
    --subagent-json-file "$SANDBOX/_webprobe_${SUB_PROBLEM_ID}_${TIMESTAMP}.json" \
    --sandbox "$SANDBOX"
```

## Output Contract

Emit ONE JSON object on stdout (also written to the file above):

```json
{
  "sub_problem_id": "<id>",
  "generated_query": "<trimmed query string, ≤100 chars>",
  "web_hits": [
    {"title": "...", "url": "https://...", "snippet": "..."}
  ],
  "web_fetch_content": "\n\n--- https://... ---\n<body truncated to 4000 bytes>",
  "findings": "<findings text>",
  "suggestion": "<suggestion text>",
  "assembled_context": "## Web Probe (stuck recovery for <theorem_name>)\n..."
}
```

The orchestrator reads `extract_web_probe.py`'s exit code (0/2/3/4) as
the success signal. One `web-probe-completed` milestone per `sub_problem_id`
is the consumer-side signal.

## Guardrails

- Do NOT mutate `Main.lean` or any `.lean` file. This skill is purely
  a search + annotation operation.
- Do NOT mark any sorry as `state=DONE`. This skill annotates; it does
  not verify or close.
- Do NOT hallucinate web search results. Only report what the WebSearch
  and web_fetch tools actually return.
- If the WebSearch tool is not available in this environment, emit
  `web_hits=[]`, `web_fetch_content=""` and proceed to the fast-path.
- The `assembled_context` field in stdout JSON MUST always be present
  (even if empty string); its absence causes `extract_web_probe.py`
  to emit `verdict=parse_error`.

---

## QUERY_GEN_SYSTEM (verbatim port from czy `:451-462`)

You are generating ONE web-search query to help unstick a Lean 4 / Mathlib proof.

The query must target Lean 4, Mathlib, formal-verification, or mathematical-statistics literature. Prefer including:
- specific Mathlib API names mentioned in the error (if any),
- the mathematical concept involved,
- the Lean keyword "Mathlib" or "Lean 4" to narrow scope.

Avoid: vague queries, multiple alternatives separated by OR, queries about non-Lean languages.

Output ONLY valid JSON, no fences. Format:
{"query": "<single search query string, max 100 chars>"}

---

## ANALYSIS_SYSTEM (verbatim port from czy `:463-470`)

You analyse web-search results to help a Lean 4 prover get unstuck.

Given the stuck context, the search query, hits, and (truncated) page content, output:
- findings: 2-4 sentences summarising what the search content tells us about the stuck issue (specific lemma names, common patterns, missing imports, etc.). If nothing useful was found, say so.
- suggestion: 1-3 concrete next-step actions for the prover (e.g. "try rewriting via X.Y", "import Mathlib.Z", "the lemma name is W in Lean 4").

Output ONLY valid JSON, no fences. Format:
{"findings": "...", "suggestion": "..."}
