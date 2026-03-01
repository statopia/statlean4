---
description: Deep prove mode — DAG-driven work-stealing scheduler with 3 saturated agents
allowed-tools: Read, Edit, Write, Grep, Glob, Bash(lake:*), Bash(grep:*), Bash(echo:*), Bash(python3:*), Bash(git:*), Task, Agent, WebSearch, WebFetch
model: opus
argument-hint: [sorry-id from backlog, or "next" for highest priority, or "all-leaves"] [--time-budget Xh]
---

# Deep Prove Mode — DAG Event-Driven Scheduler

Target: $ARGUMENTS

**Time budget: configurable via `--time-budget` (default: 1h).**
This mode keeps 3 agents saturated, dispatching new work as soon as any agent completes.
When one sorry is proved → incremental commit → unlock downstream → dispatch next ready task.

**Timeout policy (hard enforcement):**
- **Soft deadline** = `--time-budget` (default 1h): stop dispatching new tasks.
- **Hard deadline** = soft deadline + 1h: force-stop all remaining agents via `TaskStop`,
  even if they haven't finished. Before stopping, dump their partial progress to
  `sorry_backlog.yaml` (mark as `stuck`, record last error / partial proof sketch)
  and update `MEMORY.md` with any patterns learned.
- This ensures every `/prove-deep` session terminates within 2× budget at most.

---

## Phase 0: Initialize DAG

1. **Sync backlog**: Run `python3 theme/scripts/sync_sorry_backlog.py` to ensure
   `sorry_backlog.yaml` matches actual code.
2. **Load DAG**: Read `theme/input/sorry_backlog.yaml`. Build dependency graph:
   - Each sorry item has `dependencies[]` (what must be proved first) and `unlocks[]` (what becomes ready when this is proved).
   - **ready** = `dependencies` all proved or empty, AND `type != blocked` (or all blockers resolved).
   - **blocked** = has unresolved dependencies.
3. **Select targets** based on argument:
   - **Specific ID** (e.g., `efron_stein.condvar`): Attack that sorry directly (must be ready).
   - **`next`**: Pick the ready sorry with lowest priority number.
   - **`all-leaves`**: Attack ALL ready sorries via the DAG scheduler below.
4. **Priority queue**: Sort ready items by `priority` (lower = first).
5. **Parse time budget**: If `--time-budget 3h` specified, set deadline.

---

## Phase 1: Sub-Task Decomposition (MANDATORY for complex sorry)

Decompose BEFORE launching prove agents when ANY of these apply:
- `estimated_lines > 150`
- The proof involves **3+ chained Mathlib APIs** (e.g., condExp + rnDeriv + setIntegral + pullout)
- The proof requires **MeasurableSpace instance juggling** (sub-σ-algebra, comap, trim)
- A previous agent attempt on this sorry was `stuck`

Decomposition steps:
1. Launch ONE research agent (haiku) to analyze the sorry goal + surrounding context.
2. Identify independent sub-lemmas (e.g., integrability, measurability, core equality).
3. Write sub-lemma declarations with sorry + compile-check them.
4. Update `sorry_backlog.yaml` with new sub-items and DAG edges.
5. Recompute ready queue — sub-lemmas become the new leaves.

**Rationale**: Agents that discover decomposition ad-hoc waste cycles on instance
resolution and type-juggling. Pre-decomposition isolates each API interaction into
a focused sub-goal, dramatically improving agent success rate.

Skip this phase only for genuinely simple sorry (single tactic, obvious API).

---

## Phase 2: Saturated DAG Scheduling Loop (CORE)

```
MAX_SLOTS = 3
active_agents = {}   # {task_id → sorry_id}
ready_queue = [sorted by priority]
start_time = now()

LOOP:
  # ── Fill slots to MAX_SLOTS ──
  while len(active_agents) < MAX_SLOTS and ready_queue is not empty:
    sorry = ready_queue.pop(0)
    agent = launch_background_agent(sorry)
    active_agents[agent.task_id] = sorry.id
    mark sorry as in_progress in backlog

  # ── If no active agents and no ready tasks → done ──
  if active_agents is empty:
    break

  # ── Poll for completion (non-blocking round-robin) ──
  for each task_id in active_agents:
    result = TaskOutput(task_id, block=false)
    if result is complete:
      sorry_id = active_agents.pop(task_id)
      process_result(sorry_id, result)
      # After processing, loop back to fill slots immediately
      goto LOOP

  # ── Check time budget ──
  if soft_deadline exceeded:
    stop dispatching new tasks (but keep polling active agents)
  if hard_deadline exceeded (soft + 1h):
    for each active agent:
      TaskStop(task_id)
      record partial progress in sorry_backlog.yaml (status: stuck)
    break

  # ── Brief pause then re-poll ──
  (poll again immediately — TaskOutput block=false is ~zero cost)
```

### `launch_background_agent(sorry)` — Agent Prompt Template

For each sorry, launch a background Agent with `subagent_type: "general-purpose"`,
`run_in_background: true`:

```
目标: 证明 {sorry.theorem} (文件 {sorry.file}:{sorry.line})
Goal type: [read from file]

Phase 0 工具链 (强制):
  0. 用 python3 scripts/extract_signatures.py {sorry.file} 读声明索引，定位目标行号后再 Read 指定范围（不盲读全文件）
  1. 先读 theme/tactic_patterns.yaml 查找与当前 goal 匹配的 pattern — 有匹配则优先使用
  2. 先读 theme/mathlib_api_index.md 查找相关 API
     补充: grep -i '<关键词>' theme/mathlib_full_type_index.tsv 查全量 51K 条 Mathlib 声明
  3. 只有索引不够时才用 #check / exact?
  4. 最后手段: grep Mathlib 源码 (必须注明升级理由)

增量编译:
  - tactic 试错阶段: bash scripts/check_snippet.sh {sorry.file} <start> <end>
  - 全模块验证: lake build Statlean.{Module}

约束:
  - 只修改 {sorry.file}
  - 最多 5 轮 build 循环
  - 每轮: 尝试证明 → build → 分析错误 → 修复
  - 每证完一个子引理立即写入 .lean 文件并 lake build 验证，不要攒到最后一起写
完成后报告:
  - status: proved | stuck | need_sub_lemma
  - 如果 stuck: 说明卡在哪里 (缺 API / 类型不匹配 / 策略不对)
  - 如果 need_sub_lemma: 列出需要的 sub-lemma 签名
  - 如果有新 tactic pattern: 列出 (goal_shape → tactic_sequence) 供主会话更新 tactic_patterns.yaml
```

### `process_result(sorry_id, result)` — Result Handler

```
if result.status == "proved":
  1. lake build Statlean.<Module>  — incremental verify
  2. if build OK:
     - Update backlog: sorry_id.status = proved
     - Check unlocks: for each downstream in sorry.unlocks:
         if all(dep.status == proved for dep in downstream.dependencies):
           add downstream to ready_queue (sorted by priority)
     - Check whole-file zero sorry → update Verified.lean
     - git add + commit "prove: {theorem_name}"
  3. if build FAIL:
     - Log error, mark sorry as pending, priority += 3

elif result.status == "stuck":
  - Mark sorry as pending
  - Increase priority by 5 (deprioritize)
  - Log blocker info for future reference

elif result.status == "need_sub_lemma":
  - Create sub-items in backlog with dependency edges
  - Add new leaf sub-items to ready_queue
  - Original sorry becomes blocked by sub-items
```

---

## Phase 3: Checkpoint

After the scheduling loop exits (all done, or time budget reached):

1. **Sync backlog**: `python3 theme/scripts/sync_sorry_backlog.py`
2. **Commit**: Any uncommitted proved work.
3. **Update MEMORY.md**: New Mathlib patterns learned during this session.
4. **Report**:
```
DAG PROVE REPORT
  Duration: X min
  Sorries before: N
  Sorries after:  M (proved K, stuck J, remaining R)
  Proved:         [list with theorem names]
  Unlocked:       [downstream items now ready]
  Infrastructure: [new defs/lemmas added]
  Stuck:          [list with blockers]
  Next targets:   [highest priority ready items for next session]
```

---

## Single-Target Mode (specific ID or `next`)

When not `all-leaves`, skip the DAG scheduler:

1. Select the single target sorry.
2. Run Phases 1-style research (parallel haiku agents for API search).
3. Decompose into sub-lemmas if large.
4. Prove sub-lemmas depth-first (leaf → intermediate → hard).
5. Each proved sub-lemma: incremental build + commit.
6. Report.

This follows the original `/prove-deep` flow but with:
- **No batch waiting** — process results as they come.
- **Incremental commits** — don't wait for full theorem.
- **sync_sorry_backlog.py** integration.

---

## Acceleration Rules

1. **Phase 0 工具链强制执行**:
   - 大文件先用 `python3 scripts/extract_signatures.py <file>` 读声明索引
   - 攻击 sorry 前先查 `theme/tactic_patterns.yaml` 匹配 goal pattern
   - tactic 试错阶段用 `bash scripts/check_snippet.sh` 增量编译
2. **三级搜索强制执行**:
   - 第一级：`theme/mathlib_api_index.md`（必须首先查）
   - 补充：`grep -i '<keyword>' theme/mathlib_full_type_index.tsv`（51K 条全量索引）
   - 第二级：`#check` / `exact?`
   - 第三级：grep Mathlib 源码（必须注明升级理由）
   - **给 subagent 的 prompt 必须包含**："先读 `theme/tactic_patterns.yaml` 和 `theme/mathlib_api_index.md`"
3. **Incremental build**: `lake build Statlean.<Module>` not `lake build`.
4. **No redundant search**: Trust subagent results.
5. **Parallel research**: Use haiku agents for API search.
6. **入库不等待**: 证完子引理立即 commit，不等主定理。
7. **Pattern 更新**: 成功证明后，在报告环节记录新 tactic pattern → tactic_patterns.yaml
8. **上下文满处理**:
   - 等待 active agents 返回
   - sync backlog + commit
   - 更新 MEMORY.md
   - 输出: "上下文已满，用 /prove-deep all-leaves 继续"

## Key Context

- Project: `/home/gavin/statlean`
- Build: `lake build Statlean.<Module>` (incremental) or `lake build` (full)
- Backlog: `theme/input/sorry_backlog.yaml`
- Sync tool: `python3 theme/scripts/sync_sorry_backlog.py`
- Memory: `.claude/projects/-home-gavin-statlean/memory/MEMORY.md`
- Mathlib index: `theme/mathlib_api_index.md`
- Mathlib full index: `theme/mathlib_full_type_index.tsv` (51K entries, grep)
- Tactic patterns: `theme/tactic_patterns.yaml` (58 patterns, match before search)
- Signature extractor: `python3 scripts/extract_signatures.py` (replaces blind file reads)
- Snippet checker: `bash scripts/check_snippet.sh` (incremental single-decl compile)
- Classifier: `theme/scripts/classify.py`
