# Lean 4 Typeclass & Performance Errors

`failed to synthesize instance of type class T` and the family of
`deterministic timeout / max heartbeats` errors. These come from the
**typeclass database search**, not from parsing or elaboration of a
single term.

For pure parser errors see
[`lean_syntax_errors.md`](./lean_syntax_errors.md). For the special
case of multiple `MeasurableSpace Ω` instances (sub-σ-algebras), see
[`instance_pollution.md`](./instance_pollution.md) — that file is
its own deep dive because it dominates conditional-expectation proofs.

---

## Quick reference

| Symptom | Section |
|---|---|
| `failed to synthesize OrderBot ℝ` (e.g. `Finset.univ.sup` on ℝ) | §A.1 |
| `failed to synthesize IsProbabilityMeasure μ` / `IsFiniteMeasure μ` | §A.2 |
| `failed to synthesize MeasurableSpace α` | §A.3 |
| `failed to synthesize Integrable f μ` | §A.4 |
| `failed to synthesize Fintype (Fin n)` | §A.5 |
| `synthesized X, inferred inst✝N` (sub-σ-algebra) | §A.6 → `instance_pollution.md` |
| `(deterministic) timeout at 'typeclass'` / 20000+ heartbeats | §B.1 |
| `(deterministic) timeout` / 500k+ heartbeats during elaboration | §B.2 |
| `maximum recursion depth has been reached` | §B.3 |
| `fail to show termination` | §B.4 |

**Three tricks before reading further**:
1. `haveI : T := ...` — install the instance manually.
2. `letI : T := ...` — same, but for non-`Prop` instance data.
3. `@FullyQualified.lemma _ _ _ ...` — bypass instance search by
   passing every argument explicitly.

---

## §A. Instance synthesis failures

`failed to synthesize instance of type class T` means the elaborator
asked the typeclass database for an instance of `T` and the search
failed. The fix is **almost always** one of:

1. Add a `haveI` / `letI` providing the instance manually.
2. Change the API call to one with weaker requirements.
3. Lift the instance from a hypothesis or a proof.
4. Use `@`-form to pass the instance explicitly.

### §A.1 `failed to synthesize OrderBot α` / `SupSet α` (Finset.sup on ℝ etc.)

**Full message**:
```
failed to synthesize instance of type class
  OrderBot ℝ
```

**Cause**: `Finset.sup s f` requires `[OrderBot α]` because it returns
`⊥` on the empty `s`. **ℝ has no `OrderBot` instance** (no smallest
real number). The same applies to `Finset.inf` (needs `OrderTop`).

This commonly appears when defining ℓ∞ norm, max-of-residuals,
empirical sup, etc.

**Three fixes — pick by use case**:

| Want | Use | Notes |
|---|---|---|
| Max of `f` on a known-nonempty Finset | `Finset.sup' s hs_nonempty f` ✓ | Needs `Finset.Nonempty s` proof — but no `OrderBot`. |
| sup over a finite **type** indexed family | `⨆ j : Fin p, f j` ✓ (i.e. `iSup`) | Works on ℝ via `ConditionallyCompleteLinearOrder`; returns 0 on empty. |
| sup over `Finset` with a Mathlib-blessed default | `Finset.sup s (fun x => (f x : ℝ≥0∞))` ✓ | Move to ℝ≥0∞ which has `OrderBot = 0`. |

**Example fix — ℓ∞ norm of `Fin p → ℝ`**:
```lean
-- ❌ fails: OrderBot ℝ not found
noncomputable def linf_norm {p : ℕ} (v : Fin p → ℝ) : ℝ :=
  Finset.univ.sup (fun j => |v j|)

-- ✓ recommended (no nonempty hypothesis required)
noncomputable def linf_norm {p : ℕ} (v : Fin p → ℝ) : ℝ :=
  ⨆ j : Fin p, |v j|

-- ✓ alternative when you have p > 0
noncomputable def linf_norm {p : ℕ} (hp : 0 < p) (v : Fin p → ℝ) : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hp⟩⟩) (fun j => |v j|)
```

`⨆` is the Mathlib idiom; `Finset.sup'` is fine when nonemptiness is
already in scope.

### §A.2 `failed to synthesize IsProbabilityMeasure μ` / `IsFiniteMeasure μ`

**Full message**:
```
failed to synthesize instance of type class
  IsProbabilityMeasure μ
```

**Cause**: a Mathlib lemma you called requires the instance, but it is
not in scope.

**Fix patterns**:
```lean
-- Pattern 1: provide explicitly from the universe-mass proof
haveI : IsProbabilityMeasure μ := ⟨measure_univ⟩
-- where `measure_univ : μ Set.univ = 1`

-- Pattern 2: probability ⇒ finite (don't construct twice)
haveI : IsFiniteMeasure μ := inferInstance
-- (only works if `IsProbabilityMeasure μ` is already in scope)

-- Pattern 3: trim of a finite measure stays finite
haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim μ hm
haveI : SigmaFinite     (μ.trim hm) := sigmaFinite_trim     μ hm

-- Pattern 4: lift via Fact
haveI : Fact (m ≤ m₀) := ⟨h_le⟩
```

**For deeper sub-σ-algebra cases** (when the instance keeps getting
re-synthesized to the wrong measurable space), see
[`instance_pollution.md`](./instance_pollution.md) §B.2.

### §A.3 `failed to synthesize MeasurableSpace α`

**Full message**:
```
failed to synthesize instance of type class
  MeasurableSpace α
```

**Cause**: the space `α` has no measurable structure.

**Three sub-cases**:
- **Concrete types** (ℝ, ℝⁿ, ℕ, ℤ, ℚ): the `borel` instance is
  auto-derived in Mathlib. If this fails, you've likely shadowed the
  type or are missing an `import`. Add `import Mathlib.MeasureTheory.MeasurableSpace.Basic`.
- **Abstract types**: add `[MeasurableSpace α]` as a typeclass
  parameter to your theorem.
- **`Fin n → ℝ`**: derived from the product of `borel ℝ` instances.
  Should be automatic; if not, ensure `import Mathlib.MeasureTheory.Constructions.Pi`.

### §A.4 `failed to synthesize Integrable f μ`

**Cause**: the function isn't (yet) known to be integrable.

**Fix patterns**:
```lean
-- Add as hypothesis (safest)
(hf : Integrable f μ)

-- Derive from boundedness + measurability + finite measure
have hf : Integrable f μ :=
  Integrable.of_bound h_meas.aestronglyMeasurable C (ae_of_all _ h_bound)

-- Restriction of integrable function stays integrable
have hf_S : Integrable (Set.indicator S f) μ := hf.indicator hS

-- Iff with norm
have : Integrable f μ ↔ Integrable (fun x => ‖f x‖) μ :=
  integrable_norm_iff h_meas.aestronglyMeasurable
```

For the full integrability cookbook see
[`measure_theory_patterns.md`](./measure_theory_patterns.md) §A.

### §A.5 `failed to synthesize Fintype (Fin n)`

**Cause**: `Fintype (Fin n)` is auto-derived. If this fails, you have
likely:
- Shadowed `Fin` with a local definition.
- Worked with `Fin n` where `n : ℕ` is opaque and there's no
  `[Fintype]` constraint anywhere upstream.

**Fix**: ensure `n : ℕ` is concrete in scope. If `n` is a variable
parameter, the `Fintype (Fin n)` instance should kick in
automatically — if it doesn't, add it explicitly:
```lean
haveI : Fintype (Fin n) := Fin.fintype n
```

### §A.6 `synthesized X, inferred inst✝N` — instance pollution

**Full message** (cryptic):
```
type mismatch
  synthesized type:  @MeasurableSet Ω m s
  inferred type:     @MeasurableSet Ω inst✝⁴ s
```

**Cause**: multiple `MeasurableSpace Ω` instances in scope (typical
with sub-σ-algebras for conditional expectation). Lean picked the
wrong one.

**This is its own topic** — see
[`instance_pollution.md`](./instance_pollution.md) for the full
playbook (5 patterns: pin ambient with `let m0 := ‹_›`, use `@` for
ambient facts, three-tier strategy, inline comaps, section abbrev).

---

## §B. Performance and recursion

### §B.1 Typeclass timeout — `maximum number of heartbeats (20000)`

**Full message**:
```
(deterministic) timeout at 'typeclass', maximum number of heartbeats
(20000) has been reached
```

**Cause**: typeclass search is in a loop or exploring too deep. Usually
caused by:
- circular instance definitions (`A → B`, `B → A`)
- ambient ambiguity (multiple `MeasurableSpace Ω` candidates — see
  [`instance_pollution.md`](./instance_pollution.md))
- a custom instance with a costly side condition

**Fix**:
```lean
-- Provide manually to skip search
letI : MeasurableSpace Ω := m₀

-- Or raise the budget for one declaration
set_option synthInstance.maxHeartbeats 40000 in
theorem my_theorem : Goal := ...
```

If the cause is sub-σ-algebra ambiguity, the right fix is structural
(not raising heartbeats). Read
[`instance_pollution.md`](./instance_pollution.md).

### §B.2 Elaboration timeout — `500k+ heartbeats`

**Full message**:
```
(deterministic) timeout, maximum number of heartbeats (500000)
has been reached
```

**Cause**: Lean is doing expensive type unification, often because:
- A polymorphic function with a complex argument.
- Multiple `MeasurableSpace` instances forcing repeated unification of
  `m0` ↔ `inferInstance`.
- `simp` rewriting through large definitions during typeclass search.

**Fixes** (in order of preference):
1. **For sub-σ-algebra cases**: use the three-tier strategy from
   [`instance_pollution.md`](./instance_pollution.md) §B.3 — keep
   both `m0`-annotated and ambient versions of measurability facts,
   convert with `simpa [m0]`. This is by far the most common cause in
   our prove-loop.
2. **Mark expensive defs `@[irreducible]`** so unification doesn't
   unfold them.
3. **Increase the heartbeat budget** for one declaration:
   ```lean
   set_option maxHeartbeats 800000 in
   theorem expensive : Goal := ...
   ```
4. **Break the proof up** into smaller `have`/`obtain` steps so each
   step's elaboration is independently cheap.

### §B.3 `maximum recursion depth has been reached`

**Full message**:
```
maximum recursion depth has been reached (use `set_option maxRecDepth N`)
```

**Cause**: a recursive `def`, `simp` chain, or term-mode proof goes
deeper than the default `maxRecDepth` (currently 512). Common in:
- Term-mode proofs that build deeply nested constructors.
- `simp` lemmas that fire indefinitely on the same goal shape.
- `decide` on a non-decidable target.

**Fixes**:
```lean
-- Raise the budget (not great — usually masks a real bug)
set_option maxRecDepth 1024 in
theorem deep_thing : ... := ...

-- Better: replace term-mode with tactic-mode and use intermediate `have`s
theorem deep_thing : ... := by
  have h1 := ...
  have h2 := ...
  exact h1.trans h2
```

If `simp` is the culprit, identify the looping rule with
`set_option trace.Meta.Tactic.simp.rewrite true in` and exclude it
(`simp only [...] -looping_rule`).

### §B.4 `fail to show termination`

**Full message**:
```
fail to show termination for
  f
```

**Cause**: Lean can't see that your recursive function makes progress.

**Fix**: add a `termination_by` clause:
```lean
def f (n : ℕ) : ℕ :=
  if n = 0 then 0 else f (n - 1)
termination_by n

-- For lists / well-founded order:
def reduceList : List α → List α
  | [] => []
  | _ :: xs => reduceList xs
termination_by l => l.length

-- For a custom decreasing measure:
def gcd : ℕ → ℕ → ℕ
  | 0, b => b
  | a + 1, b => gcd (b % (a + 1)) (a + 1)
termination_by a b => a
```

If your function is essentially partial, prefer `partial def` (no
termination obligation, but you can't reduce it).

---

## §C. Escalation order when `failed to synthesize` keeps firing

After two failed `haveI` attempts on the same instance:

1. **Inspect what Lean wants** with `set_option pp.all true`:
   ```lean
   example : Goal := by
     set_option pp.all true in
     show ?_     -- prints the goal with all type annotations
     ...
   ```
   Often the printed goal reveals an unexpected coercion or a wrong
   measurable-space binder.

2. **Trace synthesis**:
   ```lean
   set_option trace.Meta.synthInstance true in
   example : Goal := by exact?
   ```
   Look for "tried instance X, failed because Y" lines.

3. **Try `@`-form** to pin every implicit argument:
   ```lean
   exact @condExp Ω ℝ m₀ m inst μ hm f
   ```

4. **For sub-σ-algebra cases**: stop fighting the elaborator —
   the structural fix is in
   [`instance_pollution.md`](./instance_pollution.md) §B.

5. **Last resort**: leave the obligation as `sorry` with a comment
   `-- blocker: failed to synthesize <T>` and move on. Don't burn
   30+ minutes on one synthesis failure.

---

## See also

- [`instance_pollution.md`](./instance_pollution.md) — multi-MeasurableSpace cases (the source of most §B.1/§B.2 timeouts in CE proofs).
- [`measure_theory_patterns.md`](./measure_theory_patterns.md) §A — full integrability cookbook (covers §A.4 in depth).
- [`lean_syntax_errors.md`](./lean_syntax_errors.md) §A.4 — binder-order pitfall related to `‹...›` resolution.
