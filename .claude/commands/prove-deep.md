---
description: Deep prove mode — DAG-driven work-stealing scheduler with 3 saturated agents
allowed-tools: Read, Edit, Write, Grep, Glob, Bash(lake:*), Bash(grep:*), Bash(echo:*), Bash(python3:*), Bash(git:*), Task, Agent, WebSearch, WebFetch, mcp__statlean_web_ui__request_user_decision
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

# Emit a milestone so observability (UI, evolve harness) can see the
# DAG cycle starting. Real bash, not pseudo-code:
#   python3 theme/scripts/emit_event.py --sandbox "$SANDBOX" milestone \
#       --name dispatch-batch-start
# (See "Output Conventions" at end of file. The CLI is forbidden from
# emitting `step` events for these phases; milestones are the correct
# granularity here.)

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
{如有路线: "路线已获取（来自 R1/R2/R3/R4），按路线执行：\n" + roadmap_yaml}

Phase 0.5 路线搜索 (在 API 搜索之前执行):
  0. 如果主会话已提供路线（见上方 roadmap）→ 直接按路线 key_api 查签名，跳过后续搜索
  1. 否则：先读 theme/proof_knowledge.yaml 查找与当前 goal 匹配的 L3 strategy / L2 chain / L1 tip
     - 注意 anti: true 条目 = 不要走这条路（如 Stein identity 不给 LSI）
  2. 如果 R3 仍无路线，且 sorry 等级 ≥ C，且定理是已知数学结果：
     - WebSearch "<theorem_name> proof Lean 4 Mathlib"（快速探测，~3-5K token）
     - 有 Lean 形式化 → WebFetch 提取 API 名称
     - 有 ProofWiki/教材证明 → WebFetch 获取骨架
     - 无结果 → 停止 Web 搜索，进入自主探索

Phase 0 工具链 (强制):
  0. 用 python3 scripts/extract_signatures.py {sorry.file} 读声明索引，定位目标行号后再 Read 指定范围（不盲读全文件）
  1. 如果 Phase 0.5 已获得路线 → 按 key_api 定向 grep 查签名（省 8.5K token）:
     - StatLean API: grep -i '<name>' theme/statlean_api_index.tsv
     - Mathlib API: grep -i '<name>' theme/mathlib_full_type_index.tsv
  2. 如果未匹配 → 读 theme/mathlib_api_index.md + grep 两个索引
  3. 仍未找到 → #check / exact?
  4. 最后手段: grep Mathlib 源码 (必须注明升级理由)

增量编译:
  - tactic 试错阶段: bash scripts/check_snippet.sh {sorry.file} <start> <end>
  - 全模块验证: lake build Statlean.{Module}

约束:
  - 只修改 {sorry.file}
  - 最多 5 轮 build 循环
  - 每轮: 尝试证明 → build → 分析错误 → 修复
  - 每证完一个子引理立即写入 .lean 文件并 lake build 验证，不要攒到最后一起写
  - **API 名称错误快速修复**: 如果 build 报 `unknown identifier` 或 `unknown constant`:
    1. 先查 `grep -i '<name>' theme/api_gotchas.tsv`（秒级，~12 条高频坑）
    2. 命中 → 按 correct_api 替换
    3. 未命中 → `grep -i '<name>' theme/mathlib_full_type_index.tsv`（51K 条）
    4. 仍未命中 → API 可能真不存在，考虑替代路线
    不要猜第二个名字直接写代码。
完成后报告:
  - status: proved | stuck | need_sub_lemma
  - 如果 stuck: 说明卡在哪里 (缺 API / 类型不匹配 / 策略不对)
  - 如果 need_sub_lemma: 列出需要的 sub-lemma 签名
  - 如果有新 pattern（正面或负面）: 输出 new_knowledge YAML 块供主会话入库
    （主会话收到后用 `python3 scripts/ingest_knowledge.py --input <file>` 标准流程入库）
    new_knowledge:
      - level: L3/L2/L1
        trigger: "<goal 形状>"
        strategy/chain/tip: "<内容>"
        workflow: "<证明组织方式（可选，见下）>"
        anti: true/false    # true = 不要走这条路
        confidence: <3-5>
  - **效率反思（build 循环 ≥ 5 轮时强制）**:
    回顾哪些轮次是重复劳动（同类错误反复出现），提取 workflow pattern：
    不是"用了什么 API"，而是"证明应该怎么组织以避免试错"。
    将 workflow pattern 写入 new_knowledge 的 workflow 字段。
    例: workflow: "先用 have 块建立所有子项的 Integrable/MemLp，再组装 integral_add/sub rewrite 链"
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
     - Emit milestone (real bash):
         python3 theme/scripts/emit_event.py --sandbox "$SANDBOX" milestone \
             --name sorry-proved \
             --details "{\"sorry_id\":\"<sorry_id>\",\"theorem\":\"<theorem_name>\"}"
  3. if build FAIL:
     - Log error, mark sorry as pending, priority += 3
     - Emit milestone:
         python3 theme/scripts/emit_event.py --sandbox "$SANDBOX" milestone \
             --name lake-build-fail \
             --details "{\"sorry_id\":\"<sorry_id>\"}"

if result.new_knowledge:
  - 将 new_knowledge YAML 块写入临时文件（如 /tmp/new_knowledge_{sorry_id}.yaml）
  - run("python3 scripts/ingest_knowledge.py --input /tmp/new_knowledge_{sorry_id}.yaml")
  - 脚本自动：验证 level/trigger/confidence → 去重 → 追加到 proof_knowledge.yaml → 输出摘要

elif result.status == "stuck":
  - Mark sorry as pending
  - Increase priority by 5 (deprioritize)
  - Log blocker info for future reference
  - Emit milestone:
      python3 theme/scripts/emit_event.py --sandbox "$SANDBOX" milestone \
          --name subagent-stuck \
          --details "{\"sorry_id\":\"<sorry_id>\",\"blocker\":\"<one-line>\"}"
  - **User-trust gate** (web-UI only — silently skipped in CLI-standalone
    mode when the tool is unavailable):
    If the blocker description mentions missing Mathlib infrastructure
    (patterns: "unknown identifier", "unknown constant", "no such lemma",
    "API doesn't exist", "需要 X 但 Mathlib 没有") OR the sorry has been
    stuck twice in a row, call
    `mcp__statlean_web_ui__request_user_decision` with:
      question: "Sorry <theorem_name> is stuck (blocker: <one-line>). Trust as axiom, investigate deeper, or abort?"
      options: ["trust_as_axiom", "investigate_deeper", "abort"]
    Act on the reply:
      - USER_CHOICE: trust_as_axiom   → leave the sorry with comment
        `-- TRUSTED (user-approved infra gap: <reason>)`, skip further
        dispatches for this id, continue DAG loop.
      - USER_CHOICE: investigate_deeper → keep in ready_queue with
        original priority, re-dispatch with time budget ×1.5.
      - USER_CHOICE: <free-text hint>  → treat as R1 proof-route hint
        for the next dispatch of this sorry (inject via
        `parse_proof_roadmap.py --inline "<hint>" --theorem <name>`).
      - USER_ABORTED: <reason>         → mark sorry as stuck in backlog,
        never re-dispatch this session.
      - Tool not found / tool error    → fall back to CLI-default
        (keep as pending with deprioritized priority, continue).

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
4. **proof_knowledge 入库（强制）**：把本轮发现的 L1/L2/L3 pattern（正面和 anti）
   通过标准入库流程写入，不等用户确认：
   - 收集所有 agent 返回的 `new_knowledge` YAML 块，合并写入 `/tmp/new_knowledge.yaml`
   - 运行 `python3 scripts/ingest_knowledge.py --input /tmp/new_knowledge.yaml`
   - 脚本自动验证、去重、追加到 `theme/proof_knowledge.yaml`
5. **Report — 输出分流（强制）**:

6. **Emit cycle-done milestone**（强制 — 在屏幕摘要打印之后）:
   ```
   python3 theme/scripts/emit_event.py --sandbox "$SANDBOX" milestone \
       --name dag-cycle-done \
       --details "{\"proved\":<K>,\"stuck\":<J>,\"remaining\":<R>}"
   ```
   This is the CLI-side signal the web orchestrator uses to close out
   Round N's Step 9 framing (web-side derived; see
   `website/docs/CLI_WEB_CONFORMANCE.md` §0.3). Do not skip even when
   the cycle ended via hard deadline.

**屏幕输出**（紧凑摘要，≤5 行）：
```
DAG PROVE: Xmin | sorry N→M (proved K, stuck J) | 入库 P 条
  Next: [highest priority item]
详情: reports/prove_deep_<target>.md
```

**文件存档**（完整详情，写入 `reports/prove_deep_<target>.md`）：
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

  已入库 proof_knowledge.yaml:
  - [L1/L2/L3] <trigger> — <正面/anti> — <来源>
```

用 Write 工具写入报告文件，屏幕只输出摘要行。

**`<target>` 命名规则**：单目标 → 定理名（如 `gaussian_lsi`）；`all-leaves` → `all_leaves`。

**Agent launch/result 屏幕输出也精简**：
```
[agent] 启动: <sorry_name> (file:line)
[agent] 完成: <sorry_name> — proved/stuck
```
不在屏幕输出 agent prompt 全文或详细结果分析。

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
   - 攻击 sorry 前先查 `theme/proof_knowledge.yaml` 匹配 goal pattern
   - tactic 试错阶段用 `bash scripts/check_snippet.sh` 增量编译
2. **条件跳过搜索（省 token）**:
   - proof_knowledge.yaml L3/L2 匹配 → **跳过 mathlib_api_index**（省 8.5K token/agent）
   - 未匹配 → 读 `theme/mathlib_api_index.md` + `grep theme/mathlib_full_type_index.tsv`
   - 仍未找到 → `#check` / `exact?` → grep Mathlib 源码（必须注明升级理由）
3. **Incremental build**: `lake build Statlean.<Module>` not `lake build`.
4. **No redundant search**: Trust subagent results.
5. **Parallel research**: Use haiku agents for API search.
6. **入库不等待**: 证完子引理立即 commit，不等主定理。
7. **Knowledge 入库**: 成功证明后，new_knowledge 通过 `python3 scripts/ingest_knowledge.py --input <file>` 自动入库
8. **上下文满处理**:
   - 等待 active agents 返回
   - sync backlog + commit
   - 更新 MEMORY.md
   - 输出: "上下文已满，用 /prove-deep all-leaves 继续"
9. **同文件写互斥（强制，DPI 教训）**:
   - 多个 agent **不得同时修改同一 .lean 文件**
   - 同一文件的不同 sorry → 串行攻击（A 完成 → commit → B 从新状态启动）
   - 不同文件的 sorry → 可并行
   - 违反此规则 → agent 在过时代码上浪费 token（实测 ~220K token 损失）
10. **snippet check 优先于 lake build（强制）**:
    - tactic 试错 → `bash scripts/check_snippet.sh`（~10s）
    - 全模块验证 → `lake build Statlean.<Module>`（~150s）
    - **比例要求**：snippet check ≥ 3× lake build 次数
    - DPI 教训：80 次 lake build ≈ 3.5h 纯编译 = 42% 墙钟时间
11. **跨会话 agent 处理**:
    - 新会话开始后，检查旧 agent 目标代码是否已变更
    - 若已变更 → 不等旧 agent，从当前文件状态启动新 agent
    - 旧 agent 返回后若与当前文件冲突 → 丢弃结果

## Key Context

- Project: `/home/gavin/statlean`
- Build: `lake build Statlean.<Module>` (incremental) or `lake build` (full)
- Backlog: `theme/input/sorry_backlog.yaml`
- Sync tool: `python3 theme/scripts/sync_sorry_backlog.py`
- Memory: `.claude/projects/-home-gavin-statlean/memory/MEMORY.md`
- Mathlib index: `theme/mathlib_api_index.md`
- Mathlib full index: `theme/mathlib_full_type_index.tsv` (51K entries, grep)
- Tactic patterns: `theme/proof_knowledge.yaml` (58 patterns, match before search)
- Signature extractor: `python3 scripts/extract_signatures.py` (replaces blind file reads)
- Snippet checker: `bash scripts/check_snippet.sh` (incremental single-decl compile)
- Classifier: `theme/scripts/classify.py`

## 输出预算规则（强制）

- 屏幕文本输出（非工具调用）总预算 ≤ 5K token（多 sorry DAG 模式）
- 超预算时自动切换为"极简模式"：只输出 sorry 计数变化 + 文件路径
- Agent launch → 1 行 `[agent] 启动: <name> (file:line)`
- Agent result → 1 行 `[agent] 完成: <name> — proved/stuck`
- DAG 报告 → 3-5 行屏幕摘要 + 完整报告写 `reports/prove_deep_<target>.md`
- 知识入库 → "入库 N 条 pattern"（YAML 和脚本输出在 Bash 工具内）
- 经验报告 → "经验报告已写入 reports/session_report.md"
- 工具调用输出（Bash、Read、Grep 等）不计入此预算

## Output Conventions (web UI contract)

See `theme/conventions/ui-signals.md` for the event + Markdown-header
protocol.

`/prove-deep` runs as a subagent of `/pipeline` (Step 5 = "prove").
The Step-number namespace on `events.jsonl` is owned by the outer
pipeline — this skill MUST NOT emit `## Step N:` Markdown headers or
`emit_event.py step` events for its internal DAG Phases. Doing so
collides with pipeline's Step 5 and the UI renders confusing merged
cards.

DAG Phase narrative (Phase 0 route search → Phase 1 decomposition →
Phase 2 parallel dispatch → Phase 3 reassembly) goes in normal prose,
which lands in the Report stream where the user can follow along.

**Artifact events** remain welcome (e.g. `sorry_list.json`,
per-sub-agent result files). Those are namespaced by `kind_tag`,
not by integer step id, and don't collide.
