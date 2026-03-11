---
description: Audit Mathlib API coverage for a proof goal
allowed-tools: Grep, Glob, Read, Bash(grep:*), Task, WebSearch, WebFetch
model: sonnet
argument-hint: [theorem-name or proof-goal description]
---

# Mathlib API Audit

Goal: $ARGUMENTS

## Purpose
Before spending hours on a proof, determine what Mathlib already has and what's genuinely missing. This prevents the #1 time sink: attempting proofs that need infrastructure that doesn't exist.

## Audit Steps (parallelize where possible)

### 0. Check proof knowledge base (MANDATORY FIRST)
- Read `theme/proof_knowledge.yaml` — check if L3/L2 already covers the proof goal
- If matched: the key_api list is the starting point, skip to step 2 for those specific APIs
- `grep -i '<keyword>' theme/statlean_api_index.tsv` — check StatLean self-built API (614 declarations)

### 1. Decompose the proof goal
Break the target theorem into the key lemmas it needs. For each sub-lemma:

### 2. Check coverage (StatLean + Mathlib)
For each sub-lemma, search in order:
- **StatLean first**: `grep -i '<keyword>' theme/statlean_api_index.tsv`
- **Mathlib index**: `grep -i '<keyword>' theme/mathlib_full_type_index.tsv` (51K entries)
- **Mathlib curated**: `theme/mathlib_api_index.md` (650+ entries with annotations)
- **Mathlib source** (only if indexes miss): search `.lake/packages/mathlib/Mathlib/`

For each match, classify:
- Direct match (exact theorem exists)
- Partial match (theorem exists but for different types, e.g., real vs. ennreal)
- Analogous result (e.g., Mathlib has the L² version but you need L^p)
- Nothing found

### 3. Check known gaps
Cross-reference with project memory's "Mathlib Gaps" section and `theme/input/sorry_backlog.yaml` blockers.

### 4. Produce coverage report

```
## API Coverage Report: [theorem-name]

### Available in Mathlib ✅
- `lemma_name_1` — does X (file: path)
- `lemma_name_2` — does Y (file: path)

### Partially available ⚠️
- Need X but Mathlib only has Y for different type
- Need X but only in ENNReal, not Real

### Missing from Mathlib ❌
- Description of what's needed
- Estimated difficulty to build locally
- Whether it's a one-off helper or reusable infrastructure

### Verdict
- [ ] Fully provable with existing API
- [ ] Provable with N small helper lemmas
- [ ] Blocked on missing infrastructure (describe)
```

### 5. Recommendation
If provable: suggest proof strategy and key API calls.
If blocked: identify the minimum missing piece and whether it's worth building.
