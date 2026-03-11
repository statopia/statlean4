---
description: Full pipeline — PDF theorem → Lean 4 formalization (extract → ingest → skeleton → prove → gate)
allowed-tools: Read, Edit, Write, Grep, Glob, Bash, Agent, Skill, Task, WebSearch, WebFetch
model: opus
argument-hint: <pdf-file> [--theorem <name>] [--pages <range>] [--prove-depth deep|shallow] [--time-budget 1h]
---

# Full Formalization Pipeline

Input: $ARGUMENTS

## Overview

Run the complete pipeline: PDF → LaTeX → YAML → Lean 4 → Prove → Gate

## Step 1: PDF Extract

```bash
# Default: pymupdf (local, zero API cost)
python3 theme/scripts/pdf_extract.py <pdf> [--theorem <name>] [--pages <range>]
```

pymupdf extracts raw text locally. If math formulas need LaTeX restoration,
do it in-session (read the .md file and fix LaTeX inline) — no API cost.

Report: number of blocks extracted, key theorems found.

## Step 2: LaTeX Ingest

```bash
python3 theme/scripts/from_tex.py theme/input/paper.tex -o theme/input/theorems.yaml
```

Report: number of theorem entries in YAML.

## Step 3: Lean Skeleton (use /tex2lean skill)

**Follow `theme/formalize_playbook.md` Steps 2-4** for each theorem:
1. Check existing code (grep + read Verified.lean)
2. Read `theme/mathlib_api_index.md` for Mathlib type mappings
   - 补充：`grep -i '<keyword>' theme/mathlib_full_type_index.tsv`（51K 条全量 Mathlib 索引）
3. Design Lean signature (must reflect precise math content)
4. Place in appropriate `Statlean/` module
5. Build to verify skeleton compiles
6. Run honesty check (Step 6 of playbook): no trivial wrappers, no hidden sorry

## Step 4: Build & Fix (use /build-fix skill)

Iterate until clean compilation (max 5 cycles).

## Step 5: Prove (subagent dispatch — uses Max plan quota, zero API credit)

Parse `--prove-depth` from arguments (default: deep).

`make formalize` already ran `prove` target which wrote `theme/out/prove_targets.json`.

If `--prove-depth shallow`:
  - Skip prove, proceed to Step 6 (sorry 留在 backlog 等后续攻击)

If `--prove-depth deep`:
  1. Read `theme/out/prove_targets.json`
  2. For each target (up to 3), launch a parallel Agent subagent with:
     - `subagent_type: "general-purpose"`
     - The `prompt` field from prove_targets.json
     - `model: "sonnet"` (good balance of speed and capability)
     - **prompt 必须包含 Phase 0 工具链指令**：
       "先用 python3 scripts/extract_signatures.py 读声明索引，
        先读 theme/proof_knowledge.yaml 匹配 goal，
        L3/L2 匹配到 → 按 key_api grep statlean_api_index.tsv 和 mathlib_full_type_index.tsv 查签名，跳过 mathlib_api_index 全文,
        未匹配 → 读 theme/mathlib_api_index.md + grep 两个索引，
        tactic 试错阶段用 bash scripts/check_snippet.sh 增量编译，
        每证完一个子引理立即写入 .lean 文件并 lake build 验证"
  3. Wait for all agents to complete
  4. For each target, verify sorry eliminated: `grep -c '\bsorry\b' <file>`
  5. If any target made progress but still has sorry, optionally re-dispatch
  6. Run `lake build` to verify everything compiles

**Important**: This uses Claude Code subagents (Max plan quota), NOT the `claude` CLI
(which would consume API credits). The prove_loop.sh fallback is only for CI environments.

## Step 5.5: Infrastructure Extraction (inline, per CLAUDE.md rules)

1. **Zero-sorry infrastructure** → placed in same file, isolated by `section`.
2. **Whole-file zero sorry** → update `Verified.lean`.
3. **Remaining sorry** → structured comment + `sorry_backlog.yaml` registration.

## Step 5.7: Knowledge Ingestion（自动）

对 Step 5 中成功证明的定理，收集 agent 返回的 `new_knowledge` YAML 块并入库：
```bash
python3 scripts/ingest_knowledge.py --input <agent_new_knowledge>
```
汇总多 agent 结果时做全局去重。

## Step 6: Sync Backlog & Gate

1. Run `python3 theme/scripts/sync_sorry_backlog.py` to reconcile code ↔ backlog
2. Run `bash theme/scripts/gate.sh` for full project build + sorry count + PIPELINE_ID check
3. Report metrics (time, tokens, sorry count before/after, knowledge entries added)
4. Commit with structured message

## Progress Reporting

After EACH step, report:
- Step name and status (PASS/FAIL)
- Key outputs
- Time estimate
- Any issues encountered
