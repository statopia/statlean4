---
description: Full pipeline — PDF theorem → Lean 4 formalization (extract → ingest → skeleton → prove → gate)
allowed-tools: Read, Edit, Write, Grep, Glob, Bash, Task, WebSearch, WebFetch
model: opus
argument-hint: <pdf-file> [--theorem <name>] [--pages <range>] [--prove-depth deep|shallow]
---

# Full Formalization Pipeline

Input: $ARGUMENTS

## Overview

Run the complete pipeline: PDF → LaTeX → YAML → Lean 4 → Prove → Gate

## Step 1: PDF Extract

```bash
python3 theme/scripts/pdf_extract.py <pdf> --backend claude [--theorem <name>] [--pages <range>]
```

Report: number of blocks extracted, key theorems found.

## Step 2: LaTeX Ingest

```bash
python3 theme/scripts/from_tex.py theme/input/paper.tex -o theme/input/theorems.yaml
```

Report: number of theorem entries in YAML.

## Step 3: Lean Skeleton (use /tex2lean skill)

For each theorem in YAML:
1. Map LaTeX to Mathlib types
2. Generate Lean 4 declaration with `sorry`
3. Place in appropriate `Statlean/` module
4. Build to verify skeleton compiles

## Step 4: Build & Fix (use /build-fix skill)

Iterate until clean compilation (max 5 cycles).

## Step 5: Prove (use /prove or /prove-deep skill)

- `--prove-depth shallow`: Only prove leaf lemmas, leave hard theorems as honest sorry.
- `--prove-depth deep`: Full deep prove mode (sub-lemma extraction, parallel agents).

## Step 6: Gate & Commit

1. Count remaining sorry
2. Full project build
3. Commit with structured message
4. Update `sorry_backlog.yaml`
5. Report metrics (time, tokens, sorry count)

## Progress Reporting

After EACH step, report:
- Step name and status (PASS/FAIL)
- Key outputs
- Time estimate
- Any issues encountered
