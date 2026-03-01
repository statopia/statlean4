# StatLean Agent Instructions

This file is read by AI coding agents (e.g. OpenAI Codex CLI) working on this repository.
For Claude Code, see `CLAUDE.md`.

## Authorization

All operations are pre-authorized: git, file I/O, script execution, `lake build`.
Proceed without confirmation.

## Language

- Answer questions in Chinese (unless the user writes in English)
- Comments and docstrings in Lean code: English
- Commit messages: Chinese or English

---

## Module Organization

### Organize by mathematical object, not by proof project
- File paths reflect mathematical objects: `Gaussian/Poincare.lean`, not `Concentration/GaussianPoincare.lean`
- All content for one object (definitions, proved theorems, sorry gaps) goes in the same file, separated by `section`
- Theorem names must be semantic: `frechet_mean_existence_transfer`, not `proposition_008_proposition_9`

### Sorry and proved lemmas coexist in the same file
- Use `section` to isolate proved lemmas from sorry gaps
- Do **not** split into `FooBase.lean` + `Foo.lean`
- `Statlean/Verified.lean` is an additional acceptance tool (imports only zero-sorry modules); it does **not** drive file splitting

### Mathlib file organization rules (mandatory)
- Intermediate lemmas and main theorems go in the **same file**, separated by section/namespace
- Only **independently reusable** infrastructure gets its own file (e.g. ANOVA variance decomposition used by Poincare, LSI, etc.)
- No `*Base.lean` pattern: do not split files by proof status (proved vs unproved)
- 500-900 line single files are normal; do not split just because of line count
- Organize by mathematical object / abstraction level, not by proof project or status

### Thin wrappers must be deleted
- If `f x` is just an alias for Mathlib's `g x`, inline the call site; do not keep the wrapper

### Empty shells must be cleaned up
- Empty directories, files with only `namespace ... end`, orphan files not imported anywhere: delete them
- `Statlean.lean` import list must match actual files

---

## Import Migration Rules

- Before deleting/moving a module, **grep the entire repo**: `grep -r "OldModuleName" --include="*.lean"`
- When replacing imports, analyze actual dependencies — only import what is truly used
- Also update non-Lean path references (`scripts/`, `theme/`, etc.)
- Lean 4 hard rule: `import` must be at the very top; module docstring `/-! ... -/` after all imports

---

## Formalization Strategy

**Interactive formalization playbook: `theme/formalize_playbook.md`** (input parsing → content retrieval → signature design → proof → honesty check).
When the user says "formalize XX from YY", **follow Steps 0-7 of that playbook**.

## Proof Strategy

**Full playbook: `theme/prove_playbook.md`** (decision tree + error fix table + strategy selection table).

### Attack Order
- Sorry gaps form a dependency DAG; attack from leaf nodes
- Classify: (A) Mathlib missing prerequisite API -> wait or build infra; (B) clear route -> attack directly; (C) depends on unsolved sorry -> defer
- Priority: B > A > C

### Key Patterns
- **Strong induction** over plain induction: use `Nat.strongRecOn` when `forall m < n` is needed
- **Case split**: for continuous parameters (e.g. `|t|`), split into large/small cases
- **Telescope**: product/sum telescope expansions may not exist in Mathlib; be prepared to build them
- **IBP route**: `integral_mul_deriv_eq_deriv_mul_of_integrable` + density chain rule
- **Lp downgrade**: `MemLp.mono_exponent` + `integrable_withDensity_iff` for Gaussian integrability

### Acceptance Criteria
- `lake build` zero errors
- Sorry count only decreases, never increases
- `lake build Statlean.Verified` zero sorry warnings

---

## Mathlib / StatLib Search Strategy (3-tier, mandatory)

### Tier 1: Static index (0 token cost) — always do this first
- Read `theme/mathlib_api_index.md` (~650+ entries, organized by namespace)
- Also read `Statlean/Verified.lean` for the list of already-verified modules
- Coverage: variance, MGF/CGF, charFun, Independence, IdentDistrib, condExp, condVar, Gaussian, MemLp, integral, Measure.map, exp bounds, convexity/Jensen, polynomial derivatives, IBP, Gronwall, tilted measures, Lp density, Topology/Metric, Compactness, StrongLaw/SLLN, Filter/ae
- **80% of searches are resolved at this tier**

### Tier 2: `#check` / `exact?` (precise but slow)
- Known name: `echo '#check @ProbabilityTheory.foo' | lake env lean --stdin`
- Unknown name but known target type: use `exact?` or `apply?` (~30-60s)

### Tier 3: grep Mathlib source (last resort)
- Only when tiers 1 and 2 both fail
- Limit directories: `Mathlib/Probability/`, `Mathlib/MeasureTheory/`, `Mathlib/Analysis/`

---

## Efficiency Rules

- **Incremental compilation**: `lake build Statlean.Gaussian.Poincare` — only build the target, not the whole project
- **grep before read**: locate line numbers with grep, then read specific ranges; do not blindly read large files
- **Do not repeat searches**: if you searched for something, do not search again
- **Infrastructure: commit immediately**: when a sub-lemma is proved with zero sorry, write it to the `.lean` file and run `lake build` to verify — do not wait until the end
