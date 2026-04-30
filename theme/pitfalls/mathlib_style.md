# Mathlib Style for statlean Files

Style conventions for Lean files that will live in or alongside
Mathlib — anything in `Statlean/` that may eventually promote to
`statlib/` or upstream to Mathlib.

This file is **promotion-grade**: agents writing prove-loop scratch in
`Statlean/Web/jobid/Main.lean` don't have to follow every rule, but
anything that goes through `promote-to-statlib` should pass.

For error reference (parser, typeclass, instance pollution, measure
theory patterns) see the sibling files in
[`README.md`](./README.md).

---

## §A. File header

Every `.lean` file in a permanent location starts with:

```lean
/-
Copyright (c) YYYY Author Name. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Author Name
-/
import Mathlib.Foo
import Mathlib.Bar

/-!
# Module Title

Brief description of what this file proves.

## Main results

- `theorem_name`: one-line description
- `another_theorem`: one-line description

## References

- [Author2000] full citation if applicable
-/
```

Rules:
- Copyright on **line 1**, no preceding blank line.
- `Authors:` line — no period at the end.
- Imports immediately after copyright (no blank line between).
- Blank line before the `/-! ... -/` module docstring.
- Module docstring uses `/-! ... -/` (note the `!`), not `/-- ... -/`.

---

## §B. Naming conventions

### Case rules

| Returns | Style | Example |
|---|---|---|
| `Prop` (theorems, lemmas) | `snake_case` | `integral_add`, `condExp_unique` |
| Types, structures, classes, inductive types | `UpperCamelCase` | `Measure`, `IsProbabilityMeasure` |
| Functions returning non-Prop, definitions | `lowerCamelCase` | `condExpKernel`, `pathLaw` |

### When `UpperCamelCase` appears inside a `snake_case` name

Convert to `lowerCamelCase`:
```lean
def iidProjectiveFamily ...                          -- ✓ IID → iid
theorem conditionallyIID_of_exchangeable ...         -- ✓ "iid" inside snake_case
def IIDProjectiveFamily ...                          -- ❌ uppercase in def name
```

### Prop-valued classes

| Form | Pattern | Example |
|---|---|---|
| Noun | `Is` + Noun | `IsProbabilityMeasure`, `IsMartingale` |
| Adjective | bare word | `Normal`, `Continuous`, `Integrable` |

### Inequality lemma names

| Symbol | Suffix |
|---|---|
| `≤` | `le` |
| `<` | `lt` |
| `≥` | `ge` (only for swapped-argument variants) |
| `>` | `gt` (only for swapped-argument variants) |

Default to `le`/`lt`. Use `ge`/`gt` only to flag a variant whose
arguments are in the opposite order.

### Avoid ad-hoc names

Do not use `helper1`, `foo_aux`, `lemma2`, `my_thing`. Names should
reflect the math: `mean_of_indicator`, `sum_pow_le`, `condExp_const`.

---

## §C. Line length

**Limit: 100 characters.** Break long signatures and tactic calls.

### Break strategies

```lean
-- Break before the colon of a long signature
theorem foo {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    [StandardBorelSpace (Ω[α])] :
    Statement := by
  ...

-- Break after `:=` for long bodies
def longDefinition :=
    complex_expression_here

-- Break in calc chains after the relation symbol
calc a = b := by proof1
  _ = c := by proof2

-- Continuation lines: 4 spaces (or 2 for some contexts)
```

### Quick check
```bash
awk 'length > 100 {print FILENAME ":" NR ": " length($0) " chars"}' **/*.lean
```

---

## §D. Tactic mode formatting

### Where `by` lives

```lean
-- ✓
theorem foo : Statement := by
  intro x
  exact h

-- ❌
theorem foo : Statement :=
  by
  intro x
```

### Subgoal focus

Use `·` (focusing dot, U+00B7 — `\.` in Lean) to focus each subgoal:

```lean
constructor
· -- first goal
  exact h1
· -- second goal
  exact h2
```

### Term mode for trivial proofs

```lean
-- ✓
theorem foo : P := proof_term

-- ⚠️ usually unnecessary
theorem foo : P := by exact proof_term
```

### Avoid semicolons

Prefer newlines. `by simp; ring` is allowed but not encouraged. The one
common idiom that uses `;` is `intro a b c <;> simp` — `<;>` (apply to
all goals) is fine.

---

## §E. Calc proofs

Align relation symbols vertically:

```lean
calc expression
    = step1 := by justification1
  _ = step2 := by justification2
  _ ≤ step3 := by justification3
```

- Each step has its own justification.
- The first relation has 4-space indent; subsequent `_` lines have
  2-space indent.

---

## §F. Implicit vs explicit parameters

### `{x : T}` (implicit) when

- `x` is inferable from later parameters' types.
- `x` doesn't appear at the call site explicitly.

### `(x : T)` (explicit) when

- `x` is a primary mathematical object the lemma is about.
- `x` is used in the body but not in any other parameter's type.
- Named hypothesis or proof object.

### Examples

```lean
-- ✓ n is inferable from c : Fin n → ℝ
lemma foo {n : ℕ} {c : Fin n → ℝ} : Statement

-- ✓ μ and X are primary subjects
theorem bar {μ : Measure Ω} (X : ℕ → Ω → α) : Statement

-- ✓ n explicit because it's used in the body, not in another param's type
def shift_iter (n : ℕ) (F : Ω[α] → ℝ) : Ω[α] → ℝ := fun ω => F ((shift^[n]) ω)
```

---

## §G. File names

`UpperCamelCase.lean` for all files:
```
✓ Core.lean, DeFinetti.lean, ConditionallyIID.lean
❌ core.lean, de_finetti.lean
```

Exceptions are extremely rare (e.g. `lp.lean` for ℓᵖ spaces) and
require explicit justification.

---

## §H. Documentation content rules

### No development history references

```lean
-- ❌ stale once merged
/-- In earlier drafts, this used axioms; we removed them. -/
/-- This replaces the old broken implementation. -/

-- ✓
/-- Constructs the conditional expectation kernel for a finite measure. -/
```

Comments are for the **current** state of the code. History belongs in
git.

### Don't post-mortem axioms

After a theorem has been proved (`axiom` keyword removed), don't add a
banner:

```lean
-- ❌ noise
/-- This construction is completely **axiom-free**! -/

-- ✓
/-- Constructs ... using mathlib's standard measure theory. -/
```

Mathematical axioms (Choice, propext, etc.) are fine to discuss when
relevant.

---

## §I. Pre-submit checklist

Before `promote-to-statlib`, verify:

- [ ] Copyright header on line 1.
- [ ] Imports immediately after copyright (no blank line).
- [ ] Module docstring `/-! ... -/` with `# Title` and `## Main results`.
- [ ] Naming: theorems `snake_case`, types `UpperCamelCase`, defs `lowerCamelCase`.
- [ ] All lines ≤ 100 characters.
- [ ] `by` at end of line (not on its own line).
- [ ] Each main declaration has a `/-- ... -/` docstring.
- [ ] No development-history language in comments.
- [ ] No `sorry` (or only documented `WIP` sorries).
- [ ] `#print axioms` shows only `Classical.choice`, `propext`, `Quot.sound`.

### One-liners
```bash
# Line length violations
awk 'length > 100 {print FILENAME ":" NR ": " length($0)}' **/*.lean

# theorems that should be lowercase
grep -nE "^theorem [A-Z]" **/*.lean

# defs returning Prop should be theorems
grep -nE "^def [a-z_].*: Prop" **/*.lean

# count remaining sorries
grep -c "sorry" **/*.lean
```

---

## §J. References

- [Mathlib library style](https://leanprover-community.github.io/contribute/style.html)
- [Mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html)
