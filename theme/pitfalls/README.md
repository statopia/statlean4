# Lean 4 Pitfalls — Prover Knowledge Base

A focused, statistics-flavored knowledge base for the autoformalize / prove
loop. Each file covers **one or two related error categories** with
diagnoses, fixes, and ready-to-paste templates.

The audience is the LLM agent loop (autoformalize, prover, helper). Files
here are written so they can be loaded on demand from the agent prompt
when an error matches a routing key — see `LEAN_QUICK_ERROR_TABLE` in
[`src/lib/orchestrator/honestyRules.ts`](../../src/lib/orchestrator/honestyRules.ts).

---

## Files in this folder

| File | When to read | Lines |
|---|---|---|
| [`lean_syntax_errors.md`](./lean_syntax_errors.md) | Parser / lexer / elaboration errors. `unexpected token`, `unknown identifier`, combining marks, English-word operators, unclosed declarations, `exact failed`. | ~280 |
| [`typeclass_errors.md`](./typeclass_errors.md) | `failed to synthesize`, `OrderBot ℝ`, 500k-heartbeat timeouts, WHNF / termination errors. | ~220 |
| [`instance_pollution.md`](./instance_pollution.md) | **Multiple `MeasurableSpace Ω` instances** — the dominant failure mode for sub-σ-algebra / conditional-expectation proofs. | ~330 |
| [`measure_theory_patterns.md`](./measure_theory_patterns.md) | Positive templates: integrability, conditional expectation (`condExpWith`, 3-condition uniqueness, set-integral), almost-everywhere reasoning, σ-algebra plumbing, indicator rewriting, NNReal bounds. Includes probability-measure encoding and RV measurability. | ~400 |
| [`statistics_domain.md`](./statistics_domain.md) | Stats-specific APIs: `gaussianReal`, `expMeasure`, `variance`, `IndepFun`, `Matrix.mulVec`, OLS skeleton, convergence (`Tendsto`, `atTop`), zero-measure escape pitfall. | ~200 |
| [`mathlib_style.md`](./mathlib_style.md) | Promotion-grade style: file header, naming (snake_case / UpperCamelCase / lowerCamelCase), 100-char line limit, calc alignment, implicit-vs-explicit binders, pre-submit checklist. | ~300 |

---

## How error categories map to files

```text
ERROR HEARD                                                     → READ
─────────────────────────────────────────────────────────────── ────────────────────────────
unexpected token 'λ'/'Π'/'Σ'/'∀'/'∃'                            lean_syntax_errors §A.1
expected token (combining mark β̂ θ̂ X̄ X̃)                       lean_syntax_errors §A.6
unknown identifier 'in'/'notin'/'and'/'or' (English operator)   lean_syntax_errors §A.2
unexpected token 'theorem'/'def' (after another decl)           lean_syntax_errors §A.3
unknown identifier (binder ordering / auto-bound implicit)      lean_syntax_errors §A.4
section doc comment in tactic mode                              lean_syntax_errors §A.5
exact / apply failed                                            lean_syntax_errors §C.3
type mismatch (ℕ vs ℝ, coercion)                                lean_syntax_errors §C.2
no goals after tactic                                           lean_syntax_errors §C.6
"error on wrong line" (misleading location)                     lean_syntax_errors §C.1
alpha/beta-equiv binder mismatch                                lean_syntax_errors §C.4
numerals in propositional contexts                              lean_syntax_errors §C.5
lambda variable shadowing                                       lean_syntax_errors §C.7
dot notation namespace confusion                                lean_syntax_errors §C.8

failed to synthesize OrderBot ℝ (Finset.sup on ℝ)               typeclass_errors §A.1
failed to synthesize IsProbabilityMeasure / Integrable          typeclass_errors §A.2
failed to synthesize MeasurableSpace                            typeclass_errors §A.3
failed to synthesize Fintype                                    typeclass_errors §A.4
500k heartbeats / "deterministic timeout"                       typeclass_errors §B.1
maximum recursion depth exceeded                                typeclass_errors §B.2
WHNF / unification timeout                                      typeclass_errors §B.3
equation compiler / termination failed                          typeclass_errors §B.4

synthesized X, inferred Y (sub-σ-algebra context)               instance_pollution.md (whole)
"hm : m ≤ m"  /  hypothesis became circular                     instance_pollution §B.1
inferInstance drift (set comap … inferInstance)                 instance_pollution §C
mysterious mismatches with multiple MeasurableSpace             instance_pollution §A

condExp / conditional expectation API confusion                 measure_theory §B (condExpWith)
proving μ[f|m] =ᵐ[μ] g                                          measure_theory §C (3-condition)
∫ x in s, μ[f|m] x ∂μ                                            measure_theory §D (set integral)
proving Integrable from a bound                                 measure_theory §A
∀ᵐ x ∂μ, P x                                                    measure_theory §E
σ(W) ≤ σ(Z, W)  /  comap measurability                           measure_theory §F
Set.indicator / product f * 1_{S}                                measure_theory §G
‖μ[f|m] ω‖ ≤ R (NNReal)                                          measure_theory §H

picking the right Mathlib distribution name                     statistics_domain §B
variance / IndepFun / iIndepFun                                 statistics_domain §C
Matrix.mulVec, OLS skeleton, IsUnit (Xᵀ * X)                     statistics_domain §D
Tendsto / atTop / `open Filter Topology`                        statistics_domain §E
"prover picks μ = 0 to trivialize the goal"                     statistics_domain §F (cross-ref)

writing for promote-to-statlib (style/header/naming)            mathlib_style.md (whole)
```

---

## How the agent loop should use these files

1. **Tier 1 — inline routing table.** The agent prompt carries a short
   "error → file:§section" table (the routing block above, plus
   `LEAN_QUICK_ERROR_TABLE` in `honestyRules.ts`). Most of the time the
   agent recognizes the row and applies the inline 1-line fix without
   reading anything.

2. **Tier 2 — on-demand `read_file`.** When the inline row says
   `→ lean_syntax_errors §A.1`, the agent calls
   `read_file path="docs/pitfalls/lean_syntax_errors.md"` (or the
   KB-served path) and skims to that section.

3. **Tier 3 — full file.** Used after `sameErrorCount >= 2` (the same
   error survived two fixes). The agent reads the whole relevant file,
   not just one section.

The dispatch is intentionally **read-on-demand**, not "shove every
markdown into the system prompt" — these files together are >1500 lines.

---

## Authoring rules

- **One error category per file**, or two tightly related categories.
- **Lead with a Quick Reference / TL;DR** so the agent can decide in 5
  lines whether this file is the right one.
- **Statistics emphasis.** Every file should have at least one
  worked example drawn from a probability / statistics setting (OLS,
  Gaussian noise, conditional expectation, empirical measure, etc.).
- **No Mathlib name without a status marker.** ✓ = verified spelling,
  ⚠ = unverified — agent should `check_type` before using.
- **No development history.** Don't write "we used to do X but
  switched to Y" — these files describe the **current** state. History
  belongs in git.
- **Stay under ~400 lines per file.** Split before that.

---

## Provenance

Content was merged from:
- `statlean/theme/statistics_pitfalls.md` (existing — §1, §2, §3, §4, §5, §6, §7, §8, §9, §10, §11)
- Drafts originally placed in `/tmp/lean_kb_drafts/` (compilation_errors, instance_pollution, measure_theory_patterns, mathlib_style)
- Cross-references from `Archon/.archon-src/skills/lean4/skills/lean4/references/` (compilation-errors, instance-pollution, measure-theory, mathlib-style, domain-patterns) — patterns adapted, not copied verbatim.

When in doubt, the orchestration design lives in
[`docs/LoopProverPipeLine.md`](../LoopProverPipeLine.md) — these
pitfall files are about *what the LLM writes inside one ProverAgent
turn*, not about *how the orchestrator schedules turns*.
