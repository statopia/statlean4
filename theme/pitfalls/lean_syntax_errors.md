# Lean 4 Syntax & Elaboration Errors

Parser, lexer, and elaboration failures. These errors come from the
**front end** of Lean's pipeline (before typeclass synthesis), so they
report on raw text or on a single elaboration step — not on global
proof structure.

When you see `unexpected token`, `expected ':'`, `Unknown identifier`,
`type mismatch`, `tactic 'exact' failed`, `no goals`, or
`expected token` — start here.

For typeclass errors (`failed to synthesize ...`) see
[`typeclass_errors.md`](./typeclass_errors.md).

---

## Quick reference

| Symptom | Section | One-line fix |
|---|---|---|
| `unexpected token 'λ' / 'Π' / 'Σ' / '∀' / '∃'` | §A.1 | Reserved keyword embedded in identifier — rename to ASCII (`λ` → `lambda`, `Σ` → `Sigma`). |
| `unexpected token 'in' / 'and' / 'or'` (English-word operator) | §A.2 | Use Lean operators: `∈`, `∧`, `∨`, `¬`. |
| `unexpected token 'theorem' / 'def' / 'lemma'` mid-file | §A.3 | Previous declaration is unclosed — count parens above. |
| `Unknown identifier 'X'` (and X is a later binder) | §A.4 | Move declaration before the use site. |
| `unexpected identifier; expected command` after `/-! ... -/` in tactic | §A.5 | Use `--` line comments inside `by` blocks. |
| `unexpected/expected token` on `β̂` `θ̂` `X̄` `X̃` | §A.6 | Combining marks rejected — rename to `hat_beta`, `bar_X`. |
| `type mismatch ℕ vs ℝ` | §B.2 | `(x : ℝ)` or `↑x`. |
| `tactic 'exact' failed, type mismatch` | §B.3 | Try `apply`, or break into `have` steps. |
| `binder x doesn't match goal's binder ω` | §B.4 | `set F := ... with hF` then `simpa [hF] using ...`. |
| `numerals are data but expected Prop` | §B.5 | Replace literal with corresponding lemma term. |
| `no goals to be solved` | §B.6 | Delete the redundant tactic; previous one closed the goal. |
| `Unknown identifier 'foo'` (forgot `open`) | §B.9 | `open Filter Topology MeasureTheory ProbabilityTheory`. |
| Error reported on a line that *looks* fine | §B.1 | Real bug is 5–20 lines earlier; read backwards. |
| Variable shadowing in lambda | §B.7 | Rename the inner variable. |
| Dot-notation type mismatch (`h.EventuallyEq.foo`) | §B.8 | Use standalone form: `EventuallyEq.foo h ...`. |

---

## §A. Parser / lexer errors

The parser is the very first stage of Lean's pipeline. When you see
`unexpected token X` or `expected Y`, the lexer/parser is reporting
that **at that position**, the grammar permitted some token but you
wrote a different one. Parser errors do not consult typeclass /
definition information — they are purely syntactic.

### §A.1 Reserved keywords inside identifiers (`λ Π Σ ∀ ∃`)

**Full message** (one of):
```
unexpected token 'λ'; expected ')'
unexpected token 'Σ'; expected term
```

**Cause**: `λ Π Σ ∀ ∃` are Lean 4 reserved keywords (lambda binder,
dependent function/sigma types, universal/existential quantifiers).
The lexer cuts identifiers at any of these characters — **even when
they appear embedded inside a compound name**.

**Common offenders** (all FAIL):

| Bad | Why it fails | Good |
|---|---|---|
| `hλ_pos` (hypothesis "λ is positive") | `λ` ends `h`, parser then expects `)` | `hlambda_pos` |
| `Σ_inv` (covariance inverse) | `Σ` starts a sigma-type token | `Sigma_inv`, `covInv` |
| `Πₖ` (product symbol) | `Π` starts a Pi-type token | `Pi_k`, `prod_k` |
| `∀_intro` | quantifier symbol is a keyword | `forall_intro` |
| `(λ : ℝ)` (single-letter binder) | even alone, `λ` is parsed as the lambda binder, not a name | `(lam : ℝ)` |

**Fix**: rename **every** occurrence of the keyword character anywhere
in the file (not just the one the error reports). The error message
points at the token — the failing identifier is whatever
letters/digits/underscores sit immediately before/after.

**Pre-write check**: before `write_file`, scan your draft for the five
characters `λ Π Σ ∀ ∃`. If any appears adjacent to a letter, digit, or
`_`, rename it to ASCII first. The transliteration table:

| LaTeX-ish | ASCII |
|---|---|
| `\lambda` | `lambda`, `lam`, `eigval` |
| `\Pi` (capital) | `Pi`, `pi_param`, `prod_op` |
| `\Sigma` (capital) | `Sigma`, `sigma_mat`, `cov` |
| `\forall` | `forall_*`, `_all` |
| `\exists` | `exists_*`, `_ex` |

### §A.2 English-word operators (`in`, `notin`, `and`, `or`)

**Full message** (one of):
```
unexpected token 'in'; expected ':' or 'then'
Unknown identifier 'notin'
```

**Cause**: `in` is a Lean keyword **only** in `let x := e in body` and
`for x in xs do` constructs. It is **not** a membership predicate.
Similarly, `and`/`or`/`notin`/`not` are not Lean operators.

**Common offenders**:
```lean
if j in S then ... else ...        -- ❌ 'in' not allowed here
if j notin S then ... else ...     -- ❌ 'notin' not a token
∑ i in S, f i                      -- ❌ 'in' is NOT valid in ∑/∏ binders (deprecated)
∑ i in Sᶜ, f i                     -- ❌ same — use ∈ not in
P and Q                            -- ❌ use ∧ or And
P or Q                             -- ❌ use ∨ or Or
not P                              -- ❌ use ¬ or Not
```

**Fix table**:

| English-word draft | Lean 4 |
|---|---|
| `j in S` | `j ∈ S` |
| `j notin S` | `j ∉ S` (or `¬ (j ∈ S)`) |
| `∑ i in S, f i` | `∑ i ∈ S, f i` |
| `∑ i in Sᶜ, f i` | `∑ i ∈ Sᶜ, f i` |
| `∏ i in S, f i` | `∏ i ∈ S, f i` |
| `P and Q` | `P ∧ Q` |
| `P or Q` | `P ∨ Q` |
| `not P` | `¬ P` |
| `P iff Q` | `P ↔ Q` |
| `forall x, P` | `∀ x, P` |
| `exists x, P` | `∃ x, P` |
| `s -> t` | `s → t` (both work; Mathlib idiom is Unicode) |

**`∑ i in S` is the most common trap**: it looks like natural math notation but
`in` was removed from `∑`/`∏` binders in recent Mathlib. Always use `∈`:

```lean
∑ i ∈ S, f i          -- ✓
∑ i ∉ S, f i          -- ✓  (complement — same as ∑ i ∈ Sᶜ, f i)
∑ i ∈ Sᶜ, f i         -- ✓
```

If you cannot type `∈` directly, use `Set.Mem j S` or `S j`
(membership-as-predicate) — but never `in`.

### §A.3 `unexpected token 'theorem'/'def'/'lemma'` mid-file (unclosed prior declaration)

**Full message**:
```
unexpected token 'theorem'; expected ':'
```

**Cause**: the **previous** declaration is not syntactically complete.
The parser is mid-term, expecting a `:` (return type), `:=` (definition
body), or matching `)` / `}` / `]`, and reads the next top-level
keyword — at which point it bails.

The error's reported line is **the next declaration**, not the bug.
The real mistake is somewhere above.

**How to find the real bug**:
1. Read 5–20 lines BEFORE the reported error line.
2. Look at the most recent `def` / `noncomputable def` / `lemma` /
   `theorem`. Count opening `(` `{` `[` versus closing — they must
   balance.
3. If you see something like
   ```lean
   noncomputable def foo (x : ℝ
   theorem bar : ...   -- ← reported error here
   ```
   the missing `)` after `ℝ` is the actual bug.

**Fix**: close the unbalanced bracket / add the missing `:` or `:=` to
the offending earlier declaration.

### §A.4 `Unknown identifier 'X'` when X is a later binder

**Full message**:
```
Unknown identifier `lambda`
Note: It is not possible to treat `lambda` as an implicitly bound variable
here because it has multiple ...
```

**Cause**: you used a name in a binder before declaring it. Lean's
binder list is processed strictly left-to-right; a name on the right
cannot reference a binder that comes after.

**Example**:
```lean
theorem foo
    (h_lasso_obj : ∀ β, lasso_obj β = ... + lambda * ...)   -- ❌ uses lambda
    (lambda : ℝ)                                            --   declared here
    : ... := by sorry
```

**The Note about auto-bound implicit**: Lean has an
`autoBound implicit` feature that *silently* prepends `{X : ?}` if a
name is used but not declared. The note is telling you: "I tried to do
that, but `lambda` is used inconsistently (different types in different
places), so I gave up."

**Fix**: move the declaration before the use site:
```lean
theorem foo
    (lambda : ℝ)
    (h_lasso_obj : ∀ β, lasso_obj β = ... + lambda * ...)   -- ✓
    : ... := by sorry
```

**Also: binder-order pitfall** (section variables vs. plain params).
Plain `(name : T)` parameters must appear **after** all `[Instance]`
parameters, otherwise instance lookup `‹...›` later in the signature
can resolve to the plain parameter:
```lean
-- ❌ m precedes [MeasurableSpace Ω], so ‹MeasurableSpace Ω› = m
lemma bad (m : MeasurableSpace Ω) [MeasurableSpace Ω]
    (hm : m ≤ ‹MeasurableSpace Ω›) ...

-- ✓ all instances before plain parameters
lemma good [inst : MeasurableSpace Ω] (m : MeasurableSpace Ω)
    (hm : m ≤ inst) ...
```
Full discussion in [`instance_pollution.md`](./instance_pollution.md) §B.1.

### §A.5 `unexpected identifier; expected command` after `/-! ... -/` block

**Cause**: `/-! ... -/` is a **section docstring**, valid only at
top-level. Inside a `by` block it terminates parsing — every line
after is read as a new top-level command and fails.

**Fix**: inside tactic blocks, use line comments `-- ...`.
```lean
-- ❌ inside `by ...`:
by
  /-! ### Step 0: comment -/
  intro x
  ...

-- ✓
by
  -- Step 0: comment
  intro x
  ...
```

### §A.6 Combining marks (`β̂`, `θ̂`, `x̃`, `X̄`)

**Cause**: hat / tilde / bar / dot symbols are encoded as a base
letter + **combining-mark codepoint** (e.g. `β̂` = `β` U+03B2 + `̂`
U+0302). The Lean 4 lexer does not accept combining marks inside
identifiers — it treats the mark as a separator, breaking the name.

**Symptom**: `expected token` at the column of the combining-marked
identifier.

**Translation table**:

| Math | DON'T write | DO write |
|---|---|---|
| β̂, θ̂, x̂, p̂ (hat) | `β̂`, `θ̂`, `x̂`, `p̂` | `hat_beta`, `hat_theta`, `hat_x`, `hat_p`, or `betaHat` |
| Σ̂ (hat over capital) | `Σ̂` | `hat_Sigma`, `SigmaHat` |
| β̃, X̃ (tilde) | `β̃`, `X̃` | `tilde_beta`, `tilde_X` |
| X̄, x̄ (bar / mean) | `X̄`, `x̄` | `bar_X`, `Xbar`, `mean_X` |
| β̇, β̈ (dots) | `β̇` | `dot_beta`, `ddot_beta` |
| ŷ (regression prediction) | `ŷ` | `hat_y`, `yHat` |

### §A.7 What IS safe (don't over-correct)

Plenty of Unicode is fine. Don't ASCII-fy what doesn't need it:

- **Greek precomposed letters** (single Unicode codepoint, not keywords):
  `α β γ δ ε ζ η θ ι κ μ ν ξ ο π ρ τ υ φ χ ψ ω` — use freely.
  - The exclusions are `λ Π Σ` (keywords, see §A.1).
  - `Φ` (capital phi) is also safe — not a keyword.
- **Subscripts**: `β₀`, `x₁`, `y₂`, `ε_n`, `A₁₁` — these are individual
  Unicode digits (U+2080–U+2089), **not** combining marks.
- **Superscripts**: `x²`, `ε⁺`, `X⁻¹` — same as subscripts.
- **Math operators**: `≤`, `≥`, `≠`, `≈`, `∈`, `∉`, `⊆`, `∪`, `∩`,
  `→`, `↦`, `∘` — all safe.
- **Underscores in identifiers**: `mean_X`, `cov_mat`, `n_samples` —
  always safe.
- **Pure ASCII**: `betaHat`, `tilde_x`, `lambda_param`, `sigma_sq` —
  always safe; preferred when reading from LaTeX-style sources.

**Rule of thumb when porting LaTeX**: translate `\hat{\beta}` →
`hat_beta`, `\bar{X}` → `bar_X`, `\tilde{x}` → `tilde_x`, `\lambda` →
`lambda`, `\Sigma` → `Sigma_mat`, `\Pi` → `Pi_n`. This bypasses the
lexer issues entirely.

---

## §B. Elaboration errors

The elaborator runs **after** parsing succeeds. It reports type
mismatches, unknown identifiers (post-resolution), `exact` failures,
etc.

### §B.1 The reported line is often NOT the bug location

**Why**: the elaborator processes the file linearly and reports failure
at the point it can't continue, which is typically **5–20 lines after
the actual mistake**.

**Strategy**:
1. Read backwards from the reported line.
2. Look at the most recent `let` / `have` / tactic — wrong RHS or
   wrong variable name there often explains a downstream "type
   mismatch".
3. If you `set X := ...` and later `X` doesn't unify, the `set` is
   the suspect.

**Example**:
```lean
let μX := pathLaw μ X      -- line 4231: BUG (should be Y)
-- ... 5–7 lines using μX ...
exact ...                  -- line 4238: error reported here
```
The fix is line 4231, not line 4238.

### §B.2 `type mismatch` with `ℕ` vs `ℝ` (coercion)

**Full message**:
```
type mismatch
  x has type ℕ
  but is expected to have type ℝ
```

**Fix**:
```lean
(x : ℝ)        -- preferred: explicit coercion
↑x             -- alternative
```

For function calls: `f ↑n` or `f (n : ℝ)`.

For `Fin n → ℝ` index sums:
```lean
∑ i : Fin n, (i : ℝ)    -- ✓ — coerce each i before arithmetic
```

For natural-number cardinality vs real-number `n` in statistical
formulas, the canonical move is `(n : ℝ)` once at the top, then use
that variable throughout:
```lean
let nR : ℝ := (n : ℝ)
... use nR everywhere ...
```

### §B.3 `tactic 'exact' failed, type mismatch` (close but not equal)

**Cause**: the term you provided has nearly the right type but doesn't
unify exactly (wrong argument order, missing `intro`, extra binder).

**Fixes — in order of preference**:
1. Use `apply` instead of `exact` — `apply` allows unification with
   remaining holes.
2. Restructure constructors: `exact ⟨h.1, h.2⟩` vs `exact ⟨h.2, h.1⟩`.
3. Break into intermediate `have` steps so each gets checked
   individually (see §B.1 — wrong-line trap).
4. Use `refine` to leave one piece as `?_` and inspect what type Lean
   wants there.

```lean
-- Diagnosis trick: insert a refine with a hole
refine ?_
-- Lean now shows the exact expected type → fix the term
```

### §B.4 `binder x doesn't match goal's binder ω` (alpha-equivalence friction)

**Cause**: Lean's `simp`/`simpa` sometimes can't see that
`fun x => F x` and `fun ω => F ω` are the same term up to bound-variable
renaming. The two functions are alpha-equivalent but the unifier
gets stuck.

**Fix**: name the integrand once with `set ... with`:
```lean
set F : Ω → ℝ := fun ω => μ[g | m] ω * ξ ω with hF
have h := integral_condExp (μ := μ) (m := m) (hm := hm) (f := F)
simpa [hF] using h.symm
```

This forces both sides to use `F` literally (no fresh binders), so
unification reduces to definitional equality.

### §B.5 `numerals are data but expected type is Prop`

**Cause**: passed a `1 : ℕ`-style literal where a proof term is
expected.

**Fix**: replace the literal with the corresponding lemma:
```lean
-- ❌
h.atTop_add 1

-- ✓
h.atTop_add (tendsto_const_nhds : Tendsto (fun _ => (1 : ℝ)) atTop (nhds 1))
```

The general pattern: numerals appear *inside* terms; whenever Lean
expects a proof, you must construct one (`Eq.refl`, `le_refl`,
`tendsto_const_nhds`, etc.).

### §B.6 `no goals to be solved`

**Cause**: a previous tactic (`simp`, `linarith`, `aesop`, `decide`,
`omega`, `tauto`) already closed the goal, and the next tactic has
nothing to do.

**Fix**: delete the redundant tactic. If you want a tactic to run only
when goals remain, use `<;>`:
```lean
all_goals try simp
-- or
constructor <;> linarith
```

### §B.7 Variable shadowing in lambda / anonymous function

**Cause**: same name used in inner and outer binders; Lean picks the
inner (lexical) binding, type errors propagate.

**Fix**: rename the inner variable:
```lean
-- ❌
intro a
exact f (fun a => g a) a   -- two `a`s — inner shadows outer

-- ✓
intro a
exact f (fun x => g x) a
```

This commonly bites in `Finset.sum` / `∫` integrands when you reuse
the outer index name as the bound variable.

### §B.8 Dot-notation namespace confusion

**Full message**:
```
type mismatch: expected Filter, got Measure
```

**Cause**: `h.EventuallyEq.foo` is parsed as `EventuallyEq.foo` applied
to `h` — but `EventuallyEq` is also a constructor / type, so the first
argument is interpreted as a `Filter`.

**Fix**: use the standalone form `EventuallyEq.foo h ...` instead of
`h.EventuallyEq.foo`. Or pick a different access path:
```lean
-- Often the desired form is:
Filter.EventuallyEq.foo h₁ h₂
-- not
h₁.foo h₂
```

### §B.9 `Unknown identifier 'Tendsto' / 'atTop' / 'IndepFun'` (forgot `open`)

**Cause**: namespace not opened. Statistics/probability identifiers
live in several namespaces:

| Identifier | Namespace |
|---|---|
| `Tendsto`, `atTop`, `Filter.Eventually` | `Filter` |
| `𝓝`, `nhds`, `Continuous` | `Topology` |
| `IndepFun`, `iIndepFun`, `condExp`, `gaussianReal` | `ProbabilityTheory` |
| `Integrable`, `MeasureTheory.Measure`, `ae` | `MeasureTheory` |
| `ℝ≥0∞`, `ENNReal` | `ENNReal` (top-level after `open`) |

**Fix**: at the top of the proof file (after `import Mathlib`):
```lean
open Filter Topology MeasureTheory ProbabilityTheory ENNReal
```

This is the canonical "stats file" open list. Add `Function` and `Set`
if you use `Function.Injective`, `Set.indicator`, etc. without
qualifying.

---

## Quick debug commands

```lean
-- See the type Lean inferred
#check x

-- Check a term is well-typed against an expected type
#check (term : ExpectedType)

-- See what instance the elaborator picks
#check (inferInstance : SomeClass α)

-- Trace typeclass search (verbose)
set_option trace.Meta.synthInstance true in
example : Goal := by apply_instance

-- Trace unification (very verbose — last resort)
set_option trace.Meta.isDefEq true in
example : ... := ...
```

---

## Workflow when an unfamiliar error fires

1. **Match against the table at the top of this file.** ~70% of errors
   we hit are already there.
2. **Read backwards** from the reported line if no obvious match
   (§B.1).
3. **Run `#check`** on the failing expression to see what type Lean
   *thinks* it has.
4. **Try `refine ?_`** to inspect the expected type in the goal.
5. If still stuck after 2 attempts, escalate per
   [`typeclass_errors.md`](./typeclass_errors.md) §C or
   [`instance_pollution.md`](./instance_pollution.md) §F.
