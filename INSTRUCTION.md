# StatLean Contributor Guide

## Overview

StatLean uses a **concept-driven pipeline**: you pick the theorems you want to formalize, the system generates Lean skeletons with `sorry`, and you (or Claude Code) fill in the proofs.

You contribute with **your own Claude token budget** — Claude API key or Claude Pro/Max subscription.

## Quick Start

```bash
# 1. Fork & clone
git clone https://github.com/<your-username>/statlean4.git
cd statlean4

# 2. Install elan + Lean (skip if already installed)
curl https://elan-init.tracing.rs/elan-init.sh -sSf | sh

# 3. Download Mathlib cache (~5 min, avoids 2h compile)
lake exe cache get

# 4. Verify build
lake build Statlean
```

## Step 1: Choose What to Formalize

### Option A: Pick by ontology ID

```bash
# See all available concepts
grep "^  - id:" theme/input/stat_ontology.yaml

# Formalize one theorem (auto-expands dependency chain)
make -C theme formalize CONCEPTS="cramer_rao"
# → Generates: parametric_family → fisher_information → ... → cramer_rao
# → Creates Lean skeletons in Statlean/Information/CramerRao.lean etc.
```

### Option B: Pick by natural language

```bash
make -C theme formalize CONCEPTS="Cramér-Rao, Basu"
# Fuzzy matching: "Cramér-Rao" → cramer_rao, "Basu" → basu_theorem
```

### Option C: No dependency expansion

```bash
make -C theme formalize CONCEPTS="cramer_rao" NO_DEPS=1
# Only generates cramer_rao itself, no prerequisite concepts
```

### Option D: With a PDF (extract LaTeX into skeletons)

```bash
make -C theme formalize CONCEPTS="cramer_rao" PDF=lecture.pdf
# Extracts theorem statements from PDF, matches to concepts, fills LaTeX fields
```

### Option E: Skip the pipeline, directly edit existing sorry

```bash
# Check what sorry gaps exist
cat theme/input/sorry_backlog.yaml
# Or grep directly
grep -rn "sorry" Statlean/ --include="*.lean" | grep -v "\-\-.*sorry"
```

## Step 2: Prove

### With Claude Code (recommended)

```bash
# Install Claude Code CLI
npm install -g @anthropic-ai/claude-code

cd statlean4

# Interactive: pick one sorry to attack
claude
# Then type:  /prove Statlean/Information/CramerRao.lean cramer_rao

# Automatic: attack all leaf-node sorry gaps
claude
# Then type:  /prove-deep all-leaves

# Non-interactive (CI-friendly)
claude --print "Read theme/input/sorry_backlog.yaml, attack the highest priority sorry"
```

### Without Claude Code

Write Lean proofs directly — no tooling required. The pipeline is optional infrastructure.

```bash
# Edit the file
vim Statlean/Information/CramerRao.lean

# Build to check
lake build Statlean.Information.CramerRao
```

## Step 3: Validate & Submit

```bash
# Create a branch
git checkout -b feat/cramer-rao

# Verify
lake build Statlean.Information.CramerRao   # zero errors
grep -c "sorry" Statlean/Information/CramerRao.lean   # should be 0

# Commit & push
git add Statlean/
git commit -m "feat: prove cramer_rao (zero sorry)"
git push origin feat/cramer-rao

# Open PR
gh pr create --title "Prove Cramér-Rao lower bound"
```

## One-liner Example

```bash
git clone https://github.com/me/statlean4.git && cd statlean4
lake exe cache get
make -C theme formalize CONCEPTS="lehmann_scheffe"
claude --print "/prove-deep Statlean/Sufficiency/LehmannScheffe.lean"
git checkout -b feat/lehmann-scheffe
git add Statlean/ && git commit -m "feat: prove lehmann_scheffe"
git push origin feat/lehmann-scheffe && gh pr create
```

## FAQ

| Question | Answer |
|----------|--------|
| Who pays for tokens? | You — your own Claude API key or Claude Max subscription |
| Minimum contribution? | One sorry gap (even a single sub-lemma counts) |
| How to avoid conflicts? | Check `sorry_backlog.yaml` for unclaimed gaps before starting |
| Partial progress OK? | Yes — as long as sorry count doesn't increase, partial PRs welcome |
| Must I use Claude? | No — hand-written Lean proofs are equally welcome |
| What Lean version? | 4.28.0-rc1 via [elan](https://github.com/leanprover/elan) |

## Project Conventions

- **File organization**: by mathematical object, not by proof status. See `CLAUDE.md` for details.
- **Theorem names**: semantic (`cramer_rao`), not positional (`theorem_007`).
- **sorry comments**: include `-- blocker:` annotation explaining what's needed.
- **Acceptance**: `lake build` zero errors, sorry count non-increasing.
- **Verified.lean**: imports only zero-sorry modules. If your file reaches zero sorry, add it there.

## Sorry Backlog

The file `theme/input/sorry_backlog.yaml` tracks all open sorry gaps with:
- Priority (lower = more impactful)
- Blockers (what Mathlib API or prerequisite is missing)
- Dependencies (which sorry blocks which)

Check it before starting to pick the most impactful target.
