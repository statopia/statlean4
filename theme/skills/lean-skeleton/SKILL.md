---
name: lean-skeleton
description: Generate Lean file skeletons from `theorems.yaml`, placing reusable items into `Statlib` and project-specific items into `Formalization`.
---

# lean-skeleton

Use this skill when theorem tasks are structured and you need compilable Lean scaffolding.

## Inputs

- `theorems.yaml`
- `scope.yaml`
- existing repository tree

## Workflow

1. Partition theorem items by `layer`.
2. Map `statlib` items to `Statlib/...` and `formalization` items to `Formalization/...`.
3. Generate imports with `Statlib`-first preference.
4. Create theorem declarations in dependency order.
5. Create/update module entry files for deterministic build order.

## Output Contract

- Generated files compile as far as available proofs allow.
- File/module naming follows theorem namespace.
- No duplicate theorem names.

## Guardrails

- Do not place domain-general lemmas in `Formalization`.
- Avoid direct `Mathlib` imports in `Formalization` when `Statlib` already exports required facts.

## ⚠ MIGRATION NOTE (2026-05-01) — runtime location moved

The `Type encoding + anti-vacuity` and `Identifier naming` sections
below are **inlined verbatim** into `.claude/commands/pipeline.md` Step 3
("Honesty rules MANDATORY pre-write checklist"). The pipeline.md inline
is the **runtime dispatch path** — that's what reaches the agent's
context during a real `/pipeline` run.

This SKILL file is retained as the **documentation source-of-truth**:
the original czy `honestyRules.ts:25-46` + `:162-200` content lives here
unmodified for cross-reference and historical lookup. **Do not edit
the body below in isolation** — any change must be mirrored into
pipeline.md Step 3 to take effect at runtime.

Why the migration: empirical falsification on jobmolovhy6getc (2026-05-01)
showed that `Skill {skill: "lean-skeleton"}` is never invoked by the
SDK-bridge runtime — the agent reaches Step 3 by reading pipeline.md
directly, never opens this SKILL file, so the rules below were dead
text. Same disease pattern as proof-closure SKILL fold (fixed 2026-04-30
by inlining into prove-deep.md).

---

## Type encoding + anti-vacuity

<!-- Source: website-czy/src/lib/orchestrator/honestyRules.ts:25-46 (SKELETON_HONESTY_RULES) — body byte-equal; heading adapted per spec §3.3/§3.4 -->

When the source math gives a SPECIFIC object, BIND it as a parameter — never hide it under `∃`:

| Math | Lean (✓) | REJECTED (✗) |
|---|---|---|
| Probability measure / specific noise (e.g. N(0, σ²I)) | `(μ : Measure Ω) [IsProbabilityMeasure μ]` or a Mathlib distribution | `∃ μ : Measure Ω, ...` |
| Almost-sure claim under a given measure | `∀ᵐ ω ∂μ, P ω` (μ is a bound parameter) | `∃ μ, ∀ᵐ ω ∂μ, P ω` ← prover picks μ = 0, claim collapses |
| Random variable | `(X : Ω → ℝ) (hX : Measurable X)` | `∃ X, Measurable X ∧ ...` |
| L² / E[X] / E[X|G] / σ-algebra | `MemLp X 2 μ` / `∫ x, X x ∂μ` / `μ[X|G]` / `[MeasurableSpace Ω]` | — |

## Anti-vacuity rules (every entry is a known agent failure)

- **Escapable existential** (highest risk): `∃ m, ∀ᵐ _ ∂m, _` — prover picks m = 0; bind m instead.
- **Stub binder**: `(_ : True | False | Unit | PUnit | Empty | 0 = 1)` — vacuously satisfied.
- **Vacuous wrapper**: `True ∧ _`, `_ ∧ True`, `∃ _, True`, `∃ C > 0, True`.
- **Disconnected binder**: type doesn't reference any ambient variable (μ, X, σ, Ω, …) — it's a stub; omit it.
- **Collapsed quantifier**: `∀ θ₁ θ₂, θ₁ = θ₂`, `∃ C > 0, ∀ x, C > 0` (body ignores x).
- **Weakening**: ℝ → ℕ, ∀ → ∃, removed quantifier bounds.

Pre-write self-check: pick trivial witnesses for each ∃ in your conclusion (μ := 0, set := ∅, n := 0, X := fun _ => 0). If the claim becomes vacuously true, the skeleton is wrong — rewrite before `write_file`.

## Identifier naming (LaTeX-style ASCII for math symbols)

<!-- Source: website-czy/src/lib/orchestrator/honestyRules.ts:162-200 (LEAN_NAMING_CONVENTION) — body byte-equal; heading adapted per spec §3.3/§3.4 -->

When the source math uses one of these symbols, **always** write the
ASCII transliteration as the Lean identifier. Raw Unicode causes lexer
failures that are hard to debug.

### HARD BAN: `λ` `Π` `Σ` `∀` `∃` (Lean reserved keywords)

These five characters are **reserved keywords** (lambda binder, dependent
function/sigma type, universal/existential quantifier). They MUST NOT
appear ANYWHERE inside an identifier — not as the whole name, not as a
prefix/suffix, **not embedded in a compound name**. The Lean lexer cuts
the identifier at the keyword and reports `unexpected token` at that
column.

Common embedded mistake — these all FAIL to parse:

| Mistake | Why it fails | Fix |
|---|---|---|
| `hλ_pos` (hypothesis name) | `λ` mid-identifier ends `h` early; parser expects `)` | `hlambda_pos` |
| `Σ_inv` (covariance inverse) | `Σ` starts a sigma-type token | `Sigma_inv`, `covInv` |
| `Πₖ` (product symbol) | `Π` starts a Pi-type token | `Pi_k`, `prod_k` |
| `∀_intro` / `∃_witness` | quantifier symbols are keywords | `forall_intro` / `exists_witness` |

Rule of thumb: before you `write_file`, **grep your own draft for the
five characters `λ Π Σ ∀ ∃`** — if any appears inside a name (i.e.
adjacent to a letter, digit, or `_`), rename to ASCII.

### LaTeX-style transliteration table (other symbols)

| LaTeX in source | DON'T write | DO write |
|---|---|---|
| `\lambda` (eigenvalue, Lagrange mult.) | `λ` (keyword) | `lambda`, `lam`, `eigval` |
| `\Pi` / `\Sigma` (covariance, etc.) | `Π` / `Σ` (keywords) | `Pi`, `Sigma`, `Sigma_mat`, `covMat` |
| `\hat{\beta}`, `\hat{\theta}` | `β̂`, `θ̂` (combining mark) | `hat_beta`, `hat_theta` |
| `\tilde{x}`, `\bar{X}` | `x̃`, `X̄` (combining mark) | `tilde_x`, `bar_X` |

**Always safe** (precomposed, not keywords): `α β γ δ ε ζ η θ ι κ μ ν ξ π ρ τ φ χ ψ ω` (note: `λ Π Σ` are excluded), subscripts `β₀ x₁ ε_n`, superscripts `x² ε⁺ X⁻¹`.
