---
description: Full pipeline — PDF theorem → Lean 4 formalization (extract → ingest → skeleton → prove → gate)
allowed-tools: Read, Edit, Write, Grep, Glob, Bash, Agent, Skill, Task, WebSearch, WebFetch
model: opus
argument-hint: <pdf-file> [--theorem <name>] [--pages <range>] [--prove-depth deep|shallow] [--time-budget 2h]
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

## Step 5: Prove (DAG-driven)

Parse `--time-budget` from arguments (default: 2h).
Parse `--prove-depth` from arguments (default: deep).

If `--prove-depth shallow`:
  - Skip prove, proceed to Step 6 (sorry 留在 backlog 等后续攻击)

If `--prove-depth deep`:
  - **Execute**: Use the Skill tool to invoke `/prove-deep all-leaves --time-budget <budget>`
  - prove-deep 内部执行 DAG 调度（3 agents 饱和、work-stealing、增量 commit）
  - prove-deep 完成后自动返回本 pipeline，继续 Step 6
  - 如果 prove-deep 报告有 stuck sorry → 不阻塞 pipeline，记入 backlog

## Step 5.5: Infrastructure Extraction (inline, per CLAUDE.md rules)

Infrastructure extraction happens **during** Step 5, not as a separate pass:

1. **Zero-sorry infrastructure** (self + deps have no sorry) → placed in same file,
   isolated by `section`. Only extracted to a separate file if independently reusable
   across multiple modules (e.g., ANOVA variance decomposition).
2. **No `*Proved.lean` splitting** — CLAUDE.md forbids splitting by proof status.
3. **Whole-file zero sorry** → update `Verified.lean`.
4. **Remaining sorry** → structured comment + `sorry_backlog.yaml` registration.
5. **Sync**: Run `sync_sorry_backlog.py` to reconcile code ↔ backlog.

## Step 6: Sync Backlog & Gate

1. Run `python3 theme/scripts/sync_sorry_backlog.py` to reconcile code ↔ backlog
2. Run `bash theme/scripts/gate.sh` for full project build + sorry count + PIPELINE_ID check
3. Commit with structured message
4. Report metrics (time, tokens, sorry count before/after)

## Progress Reporting

After EACH step, report:
- Step name and status (PASS/FAIL)
- Key outputs
- Time estimate
- Any issues encountered
