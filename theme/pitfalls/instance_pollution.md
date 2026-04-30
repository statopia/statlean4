# Instance Pollution — Multiple `MeasurableSpace` Instances in Scope

When you work with sub-σ-algebras (conditional expectation, Markov
chains, filtrations, etc.) you have **multiple** `MeasurableSpace Ω`
instances live in the same proof. Lean's typeclass resolution
**prefers recently-defined local constants** over the ambient instance
— and "local" includes outer scopes you didn't touch. This shows up
as cryptic type mismatches (`synthesized: m, inferred: inst✝⁴`) and
500k-heartbeat timeouts.

This is the single biggest source of wasted prover-loop turns on
conditional-expectation work. Read top-to-bottom **before** writing
your first sub-σ-algebra theorem; the patterns are non-obvious and the
failure modes waste hours.

For the surface-level error message see
[`typeclass_errors.md`](./typeclass_errors.md) §A.6. For the positive
patterns that build on top of the techniques here see
[`measure_theory_patterns.md`](./measure_theory_patterns.md).

---

## TL;DR

```lean
theorem your_lemma ... := by
  -- ① PIN the ambient instance with a *named* let
  let m0 : MeasurableSpace Ω := ‹MeasurableSpace Ω›

  -- ② Do ALL ambient measurability work, FORCING m0 with @
  have hZ_m0    : @Measurable Ω β m0 _ Z := by simpa [m0] using hZ
  have hBpre_m0 : @MeasurableSet Ω m0 (Z ⁻¹' B) := hB.preimage hZ_m0

  -- ③ ONLY THEN define sub-σ-algebras
  let mW : MeasurableSpace Ω := MeasurableSpace.comap W m0

  -- ④ When calling Mathlib lemmas, also keep ambient (unannotated) copies
  have hBpre : MeasurableSet (Z ⁻¹' B) := by simpa [m0] using hBpre_m0
```

If you skip ① / ② and just do `let mW := ...`, every subsequent
`MeasurableSet ...` will silently bind to `mW` and the proof will diverge
with mysterious mismatches.

---

## §A. The problem

Lean's elaborator, when faced with `MeasurableSet s` (no explicit
typeclass argument), picks the **most recently introduced** local
`MeasurableSpace Ω` it can find. That includes:
- A `let` you wrote 3 lines ago
- A `set` from any `have` block
- An `abbrev` defined in an outer section
- A `MeasurableSpace.comap ...` bound by `set ... := ...`

**It does NOT** prefer the ambient `[MeasurableSpace Ω]` from the binder
list.

### A typical bug

```lean
theorem foo (Ω β : Type*) [inst : MeasurableSpace Ω] [MeasurableSpace β]
    (Z : Ω → β) (hZ : Measurable Z)
    (B : Set β) (hB : MeasurableSet B) : SomeProp := by

  let mSub : MeasurableSpace Ω := MeasurableSpace.comap Z inferInstance
  --   ↑ creates a NEW MeasurableSpace Ω in scope

  have hBpre : MeasurableSet (Z ⁻¹' B) := hB.preimage hZ
  --                          ↑ ELABORATES TO @MeasurableSet Ω mSub (Z ⁻¹' B)
  -- but hZ has type            @Measurable Ω β inst _ Z
  --                                      ↑↑↑↑ different instance!
  -- → "type mismatch synthesized: mSub, inferred: inst"
```

The bug surfaces several lines later, often in the form
`synthesized: mSub, inferred: inst✝⁴`. Lean's diagnostic naming
(`inst✝N`) makes it nearly impossible to know what's what without
intentionally pinning instances.

---

## §B. The 4 patterns that work

### §B.1 Pattern 1 — Don't bind locally (best when the sub-σ-algebra is used 1–2 times)

```lean
theorem foo ... := by
  -- Reference the sub-σ-algebra inline; never `let mSub := ...`
  have hBpre : MeasurableSet (Z ⁻¹' B) := hB.preimage hZ
  have hsub_le :
      (MeasurableSpace.comap Z inferInstance) ≤ (inferInstance : MeasurableSpace Ω) :=
    hZ.comap_le
  ...
```

**Pros**: zero pollution, simple. **Cons**: verbose if you reference the
sub-σ-algebra many times.

### §B.2 Pattern 2 — Pin ambient + use `@` for ambient facts (RECOMMENDED default)

```lean
theorem foo (Ω β : Type*) [MeasurableSpace Ω] [MeasurableSpace β]
    (Z : Ω → β) (hZ : Measurable Z) (B : Set β) (hB : MeasurableSet B) : ... := by

  -- ① pin
  let m0 : MeasurableSpace Ω := ‹MeasurableSpace Ω›

  -- ② ambient work using @ to force m0
  have hZ_m0    : @Measurable Ω β m0 _ Z := by simpa [m0] using hZ
  have hBpre_m0 : @MeasurableSet Ω m0 (Z ⁻¹' B) := hB.preimage hZ_m0

  -- ③ now define sub-σ-algebras
  let mW : MeasurableSpace Ω := MeasurableSpace.comap W m0

  -- ④ work with mW (annotate explicitly when using mW facts)
  have hmW_le : mW ≤ m0 := hW.comap_le
  have : @MeasurableSet Ω mW someSet := ...
```

**Why `@` is mandatory**: even doing ambient work "first" is not enough
if any **outer** scope binds another `MeasurableSpace Ω`. The `@`
notation defeats outer-scope pollution by naming the instance
explicitly.

### §B.3 Three-tier optimization (for `500k+ heartbeats` timeouts)

When you call Mathlib lemmas (e.g. `integral_indicator`,
`set_integral_condexp`) that need to **infer** the ambient
`MeasurableSpace`, the unification of `m0` against the inferred
instance becomes expensive. Keep **both** versions of every
measurability fact:

```lean
-- Tier 1: pin ambient
let m0 : MeasurableSpace Ω := ‹MeasurableSpace Ω›

-- Tier 2: m0-annotated versions (for explicit @ work)
have hBpre_m0 : @MeasurableSet Ω m0 (Z ⁻¹' B) := hB.preimage hZ_m0

-- Tier 3: ambient versions (cheap conversion via simpa)
have hBpre : MeasurableSet (Z ⁻¹' B) := by simpa [m0] using hBpre_m0

-- Now Mathlib calls don't pay unification cost
have := integral_indicator hBpre ...      -- uses Tier 3, instant
have := MeasurableSet.inter hBpre_m0 ...  -- uses Tier 2, explicit
```

**Why this works**: `m0 := ‹MeasurableSpace Ω›` is **definitionally
equal** to the ambient instance, so `simpa [m0]` is one rewrite — not
expensive. Mathlib lemmas get the instance they expect with no search.

### §B.4 Pattern 3 — Force `@` everywhere (fallback when you can't pin early)

If the proof structure prevents you from pinning at the top (e.g. some
sub-σ-algebra is already `let`-bound by the proof skeleton you got),
name the ambient instance in the signature and `@`-annotate **every**
ambient measurability fact.

```lean
theorem foo (Ω β : Type*) [inst : MeasurableSpace Ω] [MeasurableSpace β]
    (Z : Ω → β) (hZ : Measurable Z) ... := by

  let mSub : MeasurableSpace Ω := MeasurableSpace.comap Z inferInstance

  -- Force ambient with @ (note `inst` is the binder name above)
  have hBpre : @MeasurableSet Ω inst (Z ⁻¹' B) := hB.preimage hZ
  have h1    : @MeasurableSet Ω inst s1        := ...
  have h2    : @MeasurableSet Ω mSub s2        := ...   -- different instance, also annotated
```

**Pros**: precise. **Cons**: easy to miss one, error-prone, ugly.

### §B.5 Pattern 4 — Section-level `abbrev` (multi-theorem reuse)

Only useful when several theorems in the same section all need the same
sub-σ-algebra. `abbrev` is definitionally transparent at top level but
**still pollutes** as soon as you `let`-bind it inside the proof — so
inside each theorem you must still apply Pattern 2 (pin + `@`).

```lean
section MyMeasures
  variable (Ω β : Type*) [MeasurableSpace Ω] [MeasurableSpace β]
  variable (Z : Ω → β) (hZ : Measurable Z)

  abbrev mSubZ : MeasurableSpace Ω := MeasurableSpace.comap Z inferInstance

  theorem first  : ... := by
    let m0 : MeasurableSpace Ω := ‹MeasurableSpace Ω›   -- still pin!
    ...

  theorem second : ... := by
    let m0 : MeasurableSpace Ω := ‹MeasurableSpace Ω›
    ...
end MyMeasures
```

---

## §C. The `inferInstance` drift trap

Even with pinning, this fails:
```lean
let m0 : MeasurableSpace Ω := ‹MeasurableSpace Ω›
set mη : MeasurableSpace Ω := MeasurableSpace.comap η inferInstance with hmη
--                                                    ↑ creates a *snapshot* instance
```

The `inferInstance` inside `set` captures **a fresh instance** at the
moment `set` runs, distinct from the pinned `m0` and from the original
ambient. Subsequent operations get `synthesized: inferInstance,
inferred: inst✝⁶` errors with no obvious fix.

**Fix — Pattern B (inline comaps everywhere)**:
```lean
let m0 : MeasurableSpace Ω := ‹MeasurableSpace Ω›
let mγ : MeasurableSpace β := ‹MeasurableSpace β›

-- never `set` a comap; inline at every use site
have hmη_le : MeasurableSpace.comap η mγ ≤ m0 := by
  intro s hs
  rcases hs with ⟨t, ht, rfl⟩
  exact (hη ht : @MeasurableSet Ω m0 (η ⁻¹' t))

-- pass inline to lemmas
have h_ce : μ[f | MeasurableSpace.comap η mγ] =ᵐ[μ]
            (fun ω => ∫ y, f y ∂(condExpKernel μ (MeasurableSpace.comap η mγ) ω)) :=
  condExp_ae_eq_integral_condExpKernel hmη_le hint
```

**Rule**: `set`/`let` for comaps with `inferInstance` is forbidden. Use
`let m0 := ‹...›` to freeze ambient, and inline every `comap` expression
at every use.

---

## §D. Common mistakes (each cost real time in production)

### §D.1 Thinking `abbrev` at top level prevents pollution

```lean
abbrev mSub := MeasurableSpace.comap Z inferInstance  -- top level

theorem foo : ... := by
  let m := mSub          -- ❌ STILL POLLUTES — the `let` is the problem
  have h : MeasurableSet s := ...   -- now resolves to m
```

`abbrev` only avoids pollution **as long as you don't bind it locally**.
Reference it inline, or apply Pattern 2 inside the theorem.

### §D.2 Mixing ambient and alternative-instance work without `@`

```lean
let mSub : MeasurableSpace Ω := ...
have h1 : MeasurableSet s1 := ...        -- ❌ silently picks mSub
have h2 : MeasurableSet s2 := ...        -- ❌ silently picks mSub
```

Once mSub is in scope, **every** unannotated `MeasurableSet` goes to
mSub. Either pin and use `@`, or don't bind locally.

### §D.3 Using `letI` for non-instance data

```lean
letI mSub : MeasurableSpace Ω := ...   -- ❌ INSTALLS as the instance
-- now EVERY MeasurableSpace Ω query picks mSub
```

`letI` is for **replacing** the active instance globally in the local
scope. Use plain `let` for sub-σ-algebra data, not `letI`.

### §D.4 Adding an explicit instance binder when the section already provides one

```lean
section
variable [MeasurableSpace γ]

lemma foo {mγ : MeasurableSpace γ}    -- ❌ now there are TWO MeasurableSpace γ instances
    (hm : m ≤ mγ) := by sorry
```

Drop the explicit `{mγ : ...}` — rely on the section variable. To
reference it explicitly: `(by infer_instance : MeasurableSpace γ)`.

### §D.5 `(by infer_instance)` in a lemma signature (causes elaboration mismatches)

```lean
-- ❌
lemma foo (W : Ω → γ) :
    μ[ ... | MeasurableSpace.comap W (by infer_instance) ] = ...

-- caller:
set mW := MeasurableSpace.comap W (by infer_instance : MeasurableSpace γ)
apply foo  -- "synthesized mW, inferred inst✝⁴" — distinct elaboration
```

**Fix**: take an explicit `MeasurableSpace`-valued parameter:
```lean
-- ✓
lemma foo {m₀ : MeasurableSpace Ω} {γ : Type*} [MeasurableSpace γ]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (W : Ω → γ) (hCI : SomeProperty W)
    {m : MeasurableSpace Ω} (hm : m ≤ m₀) :
    μ[ ... | m ] = ...
```

Caller passes `(m := mW) (hm := hmW)` — no `infer_instance` mismatch.

---

## §E. Which pattern when

| Situation | Pattern | Complexity |
|---|---|---|
| Sub-σ-algebra used 1–2 times | §B.1 (no local binding) | ⭐ |
| Default for any non-trivial CE proof | §B.2 (pin + `@`) | ⭐⭐ — RECOMMENDED |
| Mathlib lemma calls causing 500k heartbeats | §B.3 (three-tier) | ⭐⭐ |
| Many theorems in one section share a sub-σ-algebra | §B.5 (section abbrev) | ⭐⭐ |
| Existing proof you can't restructure at the top | §B.4 (`@` everywhere) | ⭐⭐⭐ |

---

## §F. Summary — three things to remember

1. **Pollution is about scope, not order.** ANY conflicting
   `MeasurableSpace Ω` in any enclosing scope leaks into your proof
   unless you `@`-annotate.
2. **Pin + `@` is the default.** `let m0 := ‹MeasurableSpace Ω›` and
   `@MeasurableSet Ω m0 ...` is the only reliable way to keep ambient
   work ambient.
3. **No magic syntax exists.** Mathlib doesn't ship a "preserve ambient"
   incantation. The `@` notation IS the solution.
