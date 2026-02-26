---
description: Deep search Mathlib for a specific API/lemma
allowed-tools: Grep, Glob, Read, Bash(grep:*), Bash(lake:*), Task, WebSearch, WebFetch
model: sonnet
argument-hint: [search-term or type signature]
---

# Mathlib API Search

Search target: $ARGUMENTS

## Search Strategy (run in parallel where possible)

### 1. Local Mathlib source search
Search the `.lake/packages/mathlib/Mathlib/` directory:
- Grep for the exact term
- Grep for partial matches and synonyms
- Search in relevant subdirectories:
  - `MeasureTheory/` for integrals, measures, L^p
  - `Probability/` for variance, conditional expectation, independence
  - `Analysis/` for norms, inner products, Sobolev
  - `Topology/` for continuity, compactness
  - `Order/` for lattice operations on sigma-algebras

### 2. Name pattern search
- Search for `theorem.*<term>`, `lemma.*<term>`, `def.*<term>`
- Try common Mathlib naming conventions:
  - `foo_bar` (snake_case)
  - `Foo.bar` (namespace.method)
  - `MeasureTheory.` prefix for measure theory
  - `ProbabilityTheory.` prefix for probability

### 3. Type-based search
- If a type signature is given, search for lemmas with matching types
- Look for `→` patterns in theorem statements

### 4. Online fallback
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
