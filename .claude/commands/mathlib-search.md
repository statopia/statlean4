---
description: Deep search Mathlib for a specific API/lemma
allowed-tools: Grep, Glob, Read, Bash(grep:*), Bash(lake:*), Task, WebSearch, WebFetch
model: sonnet
argument-hint: [search-term or type signature]
---

# Mathlib API Search

Search target: $ARGUMENTS

## Search Strategy (MUST follow level order — do not skip to grep source)

### 0. Check proof knowledge base
- `grep -i '<term>' theme/proof_knowledge.yaml` — check if L2 chain or L3 strategy already covers this
- If found: report the known chain/strategy and verify it's still valid

### 1. Check StatLean self-built API
- `grep -i '<term>' theme/statlean_api_index.tsv` (614 declarations)
- Many APIs that seem like they should be in Mathlib are actually self-built in StatLean

### 2. Check Mathlib indexes (fast, no full read needed)
- `grep -i '<term>' theme/mathlib_full_type_index.tsv` (51K entries, name + type)
- `grep -i '<term>' theme/mathlib_api_index.md` (650+ curated entries with annotations)
- Try synonyms and alternative Mathlib naming conventions:
  - `foo_bar` (snake_case), `Foo.bar` (namespace.method)
  - `MeasureTheory.`, `ProbabilityTheory.` prefixes

### 3. Local Mathlib source search (only if indexes miss)
Search `.lake/packages/mathlib/Mathlib/` in relevant subdirectories:
  - `MeasureTheory/` for integrals, measures, L^p
  - `Probability/` for variance, conditional expectation, independence
  - `Analysis/` for norms, inner products, Sobolev
  - `Topology/` for continuity, compactness
  - `Order/` for lattice operations on sigma-algebras

### 4. Type-based search
- If a type signature is given, search for lemmas with matching types
- `echo '#check @<name>' | lake env lean --stdin` to verify signatures

### 5. Online fallback
- Search leanprover-community.github.io for documentation
- Search Mathlib4 docs if local search is insufficient

## Output format
For each match found, report:
- Full qualified name
- File path (relative to mathlib root)
- Complete type signature
- Brief description of what it does
- Usage example if non-obvious

Sort results by relevance. Mark which are most likely useful for the current project.
