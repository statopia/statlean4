---
description: Scan all sorry gaps, report structured status
allowed-tools: Bash(grep:*), Bash(wc:*), Bash(lake:*), Read, Grep, Glob
model: haiku
---

# Sorry Status Dashboard

Scan every `.lean` file under `Statlean/` for `sorry` occurrences. For each sorry found:

1. Report: file path, line number, the theorem/lemma name containing it
2. Classify difficulty:
   - **Mathlib-ready**: likely provable with existing Mathlib API (e.g., `simp`, `linarith`, known lemmas)
   - **Needs-infrastructure**: requires Mathlib lemmas that don't exist yet
   - **Core-gap**: one of the 6 honest core gaps (efron_stein_anova_key, gaussian_poincare_1d_core, gaussian_poincare_coord_bound_core, gaussian_lsi_1d_core, tensorization_lsi_core, herbst_argument_core)

3. Output a summary table:

```
| File | Theorem | Line | Difficulty | Notes |
|------|---------|------|-----------|-------|
```

4. End with counts: total sorry, by difficulty class, and suggested next target (lowest-hanging fruit first).

Search command: `grep -rn "sorry" Statlean/ --include="*.lean" | grep -v "^.*:.*--.*sorry" | grep -v AutoPromoted`

$ARGUMENTS
