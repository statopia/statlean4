# /prove-deep all-leaves — 2026-03-07

## Final Report

**Duration**: ~90 min
**Sorries before**: 6 (in backlog) / 4 sorry lines in LogSobolev
**Sorries after**: 6 (in backlog) / 4 sorry lines in LogSobolev
**Proved**: 0 new
**Stuck**: 3 (all targets analyzed, blockers documented)
**Infrastructure**: Improved proof sketches and sub-lemma decompositions

## DAG Status
| # | ID | Priority | Type | Status | Agent |
|---|---|---|---|---|---|
| 1 | `lsi.entropy_subadditivity_of_nonneg` | P10 | honest | STUCK (decomposed) | A1-retry |
| 2 | `berry_esseen.esseen_concentration` | P1 | stuck | **STUCK** (false statement found) | A2 |
| 3 | `lsi.normalized_of_integrable` | P2 | stuck | **STUCK** (needs ~250 lines infra) | A3 |

## Agent Results

### A2: esseen_concentration_universal — STUCK
- **Finding**: Statement is mathematically FALSE for heavy-tailed measures
  - Bochner integral returns 0 for non-integrable integrands → RHS = C₂/T → can't bound |CDF diff| ≤ 1
- **Fix**: Add integrability hypothesis (downstream `esseen_charfun_integral_bound` can provide it)
- **Blocker**: Stieltjes inversion formula (~100-150 lines, not in Mathlib)
- **Routes exhausted**: Fourier convention mismatch, smoothing kernel, sinc integral, all need Stieltjes

### A1-retry: entropy_subadditivity_of_nonneg (n≥2) — STUCK (improved)
- **Achievement**: Better proof sketch with telescoping approach documented in code
- **Key sub-steps**: (A) chain rule ~40 lines, (B) data processing ~30 lines, (C) dimension reduction ~50 lines
- **No Mathlib blockers** — purely measure-theoretic, estimated ~120 lines
- **Structural decomposition** verified (Finset.add_sum_erase + linarith) but reverted to single sorry

### A3: gaussian_lsi_normalized_of_integrable — STUCK (researched)
- **Research**: 5 proof routes analyzed with detailed feasibility/effort estimates
- **Best route**: Two-point LSI + CLT transfer (~200-250 lines, 95% feasible)
  - All dependencies exist (Lévy continuity, CLT proved in Statlean)
  - Elementary proof (no PDE/functional analysis)
- **Alternative**: Bakry-Emery OU semigroup (~280-350 lines, 80% feasible)
  - Hermite infrastructure exists in Poincare.lean
  - Docstring updated with precise sub-lemma DAG
- **Mathlib gap**: No LSI, OU semigroup, hypercontractivity, or Bakry-Emery

## Next Targets (for next session)
1. **entropy_subadditivity_of_nonneg** (P10, ~120 lines) — no Mathlib blockers, most tractable
2. **gaussian_lsi_normalized_of_integrable** (P2, ~250 lines) — via two-point LSI + CLT
3. **esseen_concentration_universal** (P1, ~150 lines) — needs Stieltjes inversion infra

## Blocked (awaiting upstream)
- `lsi.integrable_sq_log` ← #3
- `herbst.subgaussian_mgf` ← #3 + #1
- `lsi.integrable_condEntropy` ← #1
