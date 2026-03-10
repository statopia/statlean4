---
description: Attack a sorry with structured demo output (presentation mode)
allowed-tools: Read, Edit, Grep, Glob, Bash(lake:*), Bash(grep:*), Task, WebSearch, WebFetch
model: opus
argument-hint: [file:line or theorem-name]
---

# Prove Sorry — Presentation Output Mode

Target: $ARGUMENTS

**This is `/prove` with structured stage output for live demo / presentation.**
Follow the exact same prove protocol as `/prove`, but with **real-time streaming logs**
and stage summary blocks. The audience is watching on a projector.

---

## Output Protocol — Streaming + Stage Summary

Each stage has TWO parts, in this order:

1. **Real-time log lines** — bracket-tagged status updates printed **as work happens**
2. **Stage summary block** — the final recap, printed when the stage completes

### CRITICAL: Real-time Logging Rule

**Every time you output log lines as text, IMMEDIATELY follow with a Bash call
to append those EXACT SAME lines to `/tmp/prove_stages.log`.**

**VERBATIM RULE: The content written to the log file MUST be character-for-character
identical to what you printed on screen.** Do NOT translate, rephrase, or change
language. If you printed Chinese on screen, the log file must have the same Chinese.
Copy-paste, do not rewrite.

**Do NOT wait until the stage summary to write all log lines at once.**
Each group of 1-3 log lines gets its own immediate write.

Pattern (repeat for every batch of log lines):
```
<assistant text>
[search] Tier 1: mathlib_api_index -> "Fisher" -> miss
</assistant text>

<bash tool call>
cat >> /tmp/prove_stages.log << 'EOF'
[search] Tier 1: mathlib_api_index -> "Fisher" -> miss
EOF
</bash tool call>
```

### Tag Convention (ASCII only — no emoji)

| Tag | Meaning | Example |
|-----|---------|---------|
| `[target]` | Target identification | `[target] Shao Prop 3.2 — Fisher Information` |
| `[file]` | File location | `[file]   Information/Basic.lean — has scoreFunction` |
| `[grade]` | Grade assessment | `[grade]  A — 需组合 3 个 HasDerivAt API` |
| `[search]` | Search action | `[search] Tier 1: mathlib_api_index → "Fisher" → miss` |
| `[hit]` | Search hit | `[hit]    HasDerivAt.mul_const — sig matches` |
| `[miss]` | Search miss | `[miss]   tactic_patterns.yaml → no match` |
| `[idea]` | Strategy decision | `[idea]   HasDerivAt chain → .deriv extract` |
| `[write]` | Writing proof step | `[write]  score_eq: (id.mul_const).sub(hζ) \|>.deriv` |
| `[build]` | Build action | `[build]  lake build Statlean.Information.Basic ...` |
| `[pass]` | Build pass | `[pass]   PASS (8.3s)` |
| `[fail]` | Build failure | `[fail]   error: one_mul type mismatch` |
| `[fix]` | Fix action | `[fix]    simpa [one_mul] → rebuild` |

### Stage Summary Block

At the end of each stage, output a summary block:

```
━━━ STAGE N/5: <STAGE_NAME> ━━━
  <content — compact summary>
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

Then immediately write it to the log file too.

---

## Full Flow Example

```
[target] Shao Prop 3.2 (p.187) — 指数族 Fisher 信息量
[file]   Information/Basic.lean — 已有 scoreFunction, fisherInformation
[grade]  A — 组合 HasDerivAt chain + integral rewrite
                                                        ← (write to log)
━━━ STAGE 1/5: TARGET ━━━
  Theorem:  expFamily_score_eq + expFamily_fisher_eq_variance
  File:     Statlean/Information/Basic.lean
  Grade:    A (组合式)
  Goal:     score(η,x) = T(x) - ζ'(η)
━━━━━━━━━━━━━━━━━━━━━━━━━
                                                        ← (write to log)
[search] Tier 1: mathlib_api_index → "HasDerivAt" → miss
                                                        ← (write to log)
[search] Tier 2: #check hasDerivAt_id → hit
[hit]    HasDerivAt.mul_const — (c·d)' = c'·d
[hit]    HasDerivAt.sub — (f-g)' = f'-g'
[miss]   tactic_patterns.yaml → no match
                                                        ← (write to log)
━━━ STAGE 2/5: API SEARCH ━━━
  Search tier: 2 (#check)
  Matched: hasDerivAt_id, .mul_const, .sub, .deriv
  Tactic pattern: (none)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                        ← (write to log)
[idea]   HasDerivAt chain → .deriv → integral rewrite
[write]  score_eq: (hasDerivAt_id.mul_const).sub(hζ) |>.deriv
[write]  fisher_eq: unfold + congr + score_eq
[write]  fisher_eq_variance: one rewrite with h_mean
                                                        ← (write to log)
[build]  lean --stdin test ...
[pass]   PASS — zero errors
                                                        ← (write to log)
━━━ STAGE 3/5: PROOF ━━━
  Strategy: HasDerivAt chain → score → Fisher
  Key tactics:
    have := (hasDerivAt_id η).mul_const (T x)
      |>.sub hζ.hasDerivAt |>.deriv
    simpa [one_mul] using this
  Lines: 9 total
━━━━━━━━━━━━━━━━━━━━━━━━━
                                                        ← (write to log)
[build]  lake build Statlean.Information.Basic ...
[pass]   PASS (8.3s)
                                                        ← (write to log)
━━━ STAGE 4/5: VERIFY ━━━
  Command:  lake build Statlean.Information.Basic
  Result:   PASS
  Time:     8.3s
━━━━━━━━━━━━━━━━━━━━━━━━━
                                                        ← (write to log)
━━━ STAGE 5/5: RESULT ━━━
  Sorry count:  n/a (new theorems, zero sorry)
  New theorems: expFamily_score_eq, expFamily_fisher_eq, expFamily_fisher_eq_variance
  APIs used:    hasDerivAt_id, HasDerivAt.{mul_const,sub,deriv}
  FORMALIZED: Shao Prop 3.2 — Fisher Information
━━━━━━━━━━━━━━━━━━━━━━━━━
                                                        ← (write to log)
```

---

## Stage Content Specifications

### Stage 1/5: TARGET

Log lines: [target], [file], [grade]
Summary: Theorem name, file, grade, goal

### Stage 2/5: API SEARCH

Log lines: [search] per query, [hit]/[miss] per result
Summary: Tier used, matched APIs, tactic pattern

### Stage 3/5: PROOF

Log lines: [idea], [write] per proof step, [build]/[pass]/[fail]/[fix]
Summary: Strategy, key tactic lines (NOT full proof), line count

### Stage 4/5: VERIFY

Log lines: [build], [pass]/[fail]
Summary: Command, result, time

### Stage 5/5: RESULT

Summary only: sorry count, APIs, new patterns, final status

---

## Prove Protocol

Follow the exact same protocol as `/prove`:

### Phase 0: Toolchain Setup (MANDATORY)
0. `python3 scripts/extract_signatures.py <file>` — read declaration index
1. Read `theme/tactic_patterns.yaml` — match goal shape
2. Use `bash scripts/check_snippet.sh` for tactic debugging

### Phase 1: Understand (do NOT edit yet)
1. Read the file containing the sorry (targeted line range).
2. Read surrounding context (imports, helper lemmas).
3. Three-tier API search:
   - Tier 1: `theme/mathlib_api_index.md` (80% hit rate)
   - Supplement: `grep -i '<keyword>' theme/mathlib_full_type_index.tsv`
   - Tier 2: `#check` / `exact?`
   - Tier 3: grep Mathlib source (last resort)

### Phase 2: Strategy
4. List 2-3 proof strategies with tradeoffs.
5. Pick the simplest one that uses existing Mathlib API.

### Phase 3: Implement
6. Write the proof replacement.
7. Build with `lake build <module>`.
8. Max 5 build-fix cycles.

### Phase 4: Verify
9. Run `lake build <module>` (or full build if needed).

### Phase 5: Report
10. Count sorries before/after. Summarize APIs used.

---

## Key Rules
- **Log lines come FIRST, stage summary LAST** for each stage
- **Write to log file IMMEDIATELY after each batch of text output** — do not wait
- **ASCII only** — no emoji, use [tag] brackets
- Show only KEY tactic lines in Stage 3, not the full proof
- If build fails: [fail] + 1-line error + [fix] + [pass] on retry
- All prove rules (depth budget, divergence protocol, guardrails) from `/prove` still apply
