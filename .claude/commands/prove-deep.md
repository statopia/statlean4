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

0. **Cycle entry (MANDATORY, real bash)**:
   ```bash
   python3 theme/scripts/prove_deep_begin.py \
       --sandbox "$SANDBOX" --target "<TARGET>" --mode "<MODE>" \
       --time-budget-min <N>
   ```
   This emits `dispatch-batch-start` milestone with the ready_queue dump
   so the web orchestrator can derive Round/Step 8 framing and the user
   can see what's being attacked. **Do not skip** — the milestone is
   the only signal of cycle entry; consumers fail-closed when missing.

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
6. **R6 — helper-reference dispatch (E4 slice port).** For each
   parent sorry_item where ALL of these hold:

   - `state == INACTIVE_WAIT` (already decomposed; has children)
   - `coverage_state` is currently `needs_proof` (R1-R5 / library
     search did NOT already mark it `cited_by_library`)
   - `pdfProofBody` is available in the sandbox (extracted by the
     latex-ingest / pdf-extract phase) AND its length ≥ 10 chars

   …dispatch the `helper-reference` Task subagent
   (`theme/skills/helper-reference/SKILL.md`) once per parent. The
   subagent emits a JSON array to its stdout; capture it to
   `$SANDBOX/_helper_reference_$PARENT_ID.json` and pipe through:

   ```bash
   python3 theme/scripts/extract_references.py \
       --parent-id "$PARENT_ID" \
       --subagent-json-file "$SANDBOX/_helper_reference_$PARENT_ID.json" \
       --pdf-proof-body-len $LEN \
       --sandbox "$SANDBOX"
   ```

   The script writes `references[]` / `coverage_state` /
   `coverage_citation` ONLY (Rule 3 Layer 1: signature/state/
   parent_id/children/history_log untouched). One
   `reference-extracted` milestone fires per parent_id.

   **Phase 2 control flow is UNCHANGED**: a parent receiving
   `coverage_state: cited_by_reference` is still attacked by the
   prover loop. R6 is annotation-only; promotion to `done` requires
   E11 `citationVerify` (separate slice). Per
   `docs/E4_REFERENCE_SUBAGENT_SPEC.md` §10 Q4, this is the
   conservative path — short-circuiting on an LLM-assessed citation
   would be a Rule 3 statement-integrity failure mode.

   Multi-parent dispatch IS parallel-safe (extract_references uses
   flock + atomic write); fan out via Task subagent concurrency.
7. **R7 — citation-verify dispatch (E11 slice port).** Run AFTER R6
   completes for the whole batch. Iterate eligible sorries in
   deterministic order — sorted by `id` ascending (lexicographic) —
   so L2 reproducibility holds. For each sorry whose
   `coverage_state ∈ {cited_by_library, cited_by_reference}`:

   **Library path** (`coverage_state == cited_by_library`):
   The cited Mathlib name comes from R1-R5's helper-search output
   (when ported) — until then this branch is dormant on real jobs.
   Invoke:

   ```bash
   python3 theme/scripts/verify_citation.py \
       --mode library --sorry-id "<id>" \
       --cited-lemma "<Mathlib.Name>" \
       --sandbox "$SANDBOX"
   ```

   The script (T2 atomic): runs the 4-tactic ladder (`exact <name>`,
   `apply <name> <;> assumption`, `exact <name>.mp`,
   `exact <name>.mpr`); on FIRST PASS short-circuits and writes
   `state=DONE` + `done_reason=library_verified` + `citation_verified=true`;
   on FULL FAIL leaves the source tree byte-identical to its pre-call
   state and writes `citation_verified=false`. Body-level mutation
   only — Rule 3 Layer 1 invariant preserved (locked theorem
   signature untouched).

   **Reference path** (`coverage_state == cited_by_reference`):
   Dispatch the `citation-verify` Task subagent
   (`theme/skills/citation-verify/SKILL.md`) with the sub-problem's
   `original_description`, the `coverage_citation` (E4 wrote it
   stripped of the `-- cited from reference: ` prefix) as the
   `reference_theorem` input, and the `declarationText` (Lean
   signature). Capture stdout JSON to
   `$SANDBOX/_citation_verify_<id>.json`, then:

   ```bash
   python3 theme/scripts/verify_citation.py \
       --mode reference --sorry-id "<id>" \
       --subagent-json-file "$SANDBOX/_citation_verify_<id>.json" \
       --sandbox "$SANDBOX"
   ```

   On PASS: `state=DONE` + `done_reason=reference_axiom` +
   `citation_verified=true`. On FAIL (LLM verified=false OR malformed
   JSON): `citation_verified=false`; `coverage_state` preserved per
   §E11 D9. Reference path is **non-destructive** — never touches
   `.lean`.

   **Phase 1 + Phase 2 are NOT modified.** PASS-verified nodes enter
   Phase 2 already `state=DONE`; the existing "skip DONE" semantic in
   the LOOP picks them up naturally. FAIL nodes are attacked by the
   prover (per `docs/E11_CITATION_VERIFY_SPEC.md` §10 D8 — verifier-
   unsure does NOT skip; statement-integrity over throughput).

   One `citation-verified` milestone fires per invocation. Layer 4
   (`judge-integrity.ts`) at promotion time is the load-bearing audit
   on `reference_axiom` rows (E11 verifier is a soft signal; Layer 4
   has the trust pivot).

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
4. Call **`decompose_node.py`** to atomically register the children in the backlog
   (czy newloop port slice 3.A; replaces the older "manually edit yaml" recipe):
   ```bash
   python3 theme/scripts/decompose_node.py \
       --parent-id "<parent sorry id>" \
       --sub-problems-json '[{"id":"parent.sub1","theorem":"...","blocker":"..."},
                             {"id":"parent.sub2",...}]' \
       --decision-reason "<why this decomposition; will be stashed on parent
                          and surfaced in retreat history if children fail>" \
       --sandbox "$SANDBOX"
   ```
   The script (T2 atomic): inserts sub-rows with `state=INITIALIZED`, sets
   parent `state=INACTIVE_WAIT` + `children=[...]`, stashes `decision_reason`
   on the parent (consumed by record_retreat if children fail), emits
   `subtasks-split` milestone. **Locked theorem signature on the parent is
   never touched** (Rule 3 Layer 1 invariant — verified in unit tests).
5. **Refinement loop (slice 03 — czy parity)**: after `decompose_node.py`
   commits the initial children (Step A), wrap the decomposition with up to
   2 refinement rounds (Step B). czy `proofLoop.ts:807-920` runs this loop
   per-parent at decomposition time; SDK-bridge mirrors directly.

   Loop body (czy parity — `for alignRound = 0; alignRound < 3` maps to
   1 initial decompose + up to 2 refinements; cap = `informal_round >= 2`
   structurally enforced):

   ```
   WHILE parent.informal_round < 2
         AND parent.coverage_stable == false
         AND at least one child is non-converged
         (coverage_state ∈ {partial_coverage, needs_proof, no_coverage}
          OR (cited_by_* AND citation_verified == false)):

     Round body — for each parent eligible for refinement:

     a. Dispatch helper-reference SKILL (R6 — E4 helper-reference) on
        the current children. Idempotent re-run if children unchanged
        (E4 L2 idempotence test). NO citation-verify dispatch here —
        E11 R7 runs in Step C on converged children only (czy parity:
        czy's citationVerify.ts fires post-loop, never per-round; this
        avoids the lossy interaction where round-N R7 PASSes a child
        the round-N+1 refinement then drops).

     b. Dispatch informal-refine Task subagent
        (theme/skills/informal-refine/SKILL.md) with the helper
        feedback (per-child coverage_state + references[].assessment
        + replacement_statement). **CRITICAL**: when building the
        user message for the subagent, render each current child as
        `id: <yaml_row_id>     theorem: <theorem>     line: <N>     deps: [...]`
        with the yaml row id (e.g. `parent.s2`) — NOT just the
        theorem name. The script's `_diff_subproblems` matches by
        exact-string id; if the LLM uses theorem names instead of
        ids, the diff treats EVERY child as "removed + new" and
        wipes any verified citations. The SKILL prompt now includes
        an explicit "id stability rule" but the agent must still
        supply the ids in the rendering. Capture stdout JSON to
        $SANDBOX/_informal_refine_${PARENT_ID}_round_${N}.json.

     c. Pipe the JSON through refine_decomposition.py:

        python3 theme/scripts/refine_decomposition.py \
            --parent-id "<parent_id>" \
            --subagent-json-file "$SANDBOX/_informal_refine_${PARENT_ID}_round_${N}.json" \
            --sandbox "$SANDBOX"

        Script (T2 atomic): convergence pre-check (czy "all covered"
        exit), parses JSON, on noAdjustment → coverage_stable=true; on
        refined → diff applied (drop + descendants removed; add new
        children with INITIALIZED defaults; KEPT children's `theorem`
        UNTOUCHED — Layer 1 D-6); bumps informal_round. Emits one
        informal-round milestone with verdict ∈ {refined, noAdjustment,
        converged_pre_dispatch, cap_reached, parse_error}.

     d. Re-evaluate the WHILE condition based on the milestone verdict.
        cap_reached / converged_pre_dispatch / noAdjustment → loop exits.
        refined → loop continues to next round; round body re-dispatches
        R6 on the new children list.
   ```

   **Step C — final commit + post-loop verification**: after the loop
   converges, sub-autoformalize fires on the FINAL children (existing
   flow); Layer 1 signature locks apply to FINAL signatures only. Then
   E11 R7 (citation-verify) dispatches per spec §6.1 on the converged
   children. PASS-verified children get state=DONE + done_reason and
   bypass Phase 2 prover.

6. The parent enters INACTIVE_WAIT and exits the ready queue automatically;
   sub-lemmas become the new leaves the next ready_queue computation picks up.

**Rationale**: Agents that discover decomposition ad-hoc waste cycles on instance
resolution and type-juggling. Pre-decomposition isolates each API interaction into
a focused sub-goal, dramatically improving agent success rate. The refinement loop
(steps 5a-5d) gives the InformalAgent up to 2 chances to adjust the decomposition
based on what helper-reference found — closing the alignment-quality gap that
slice 03 ports from czy.

Skip step 5 (refinement loop) only for genuinely simple decompositions where the
agent is confident at round 0. Skip steps 1-5 entirely for genuinely simple sorry
(single tactic, obvious API — no decomposition needed).

---

## Phase 2: Tree-Walker Scheduling Loop (CORE — czy newloop port)

The scheduling model is the **decision tree** ported from czy's
`proofState.ts` + `controlAgent.ts` (replacing the prior flat-DAG queue).
Every sorry_item has a `state` ∈ {INITIALIZED, INACTIVE_WAIT, ACTIVE_PROVING, DONE}
and a `parent_id` (None for top-level). Decomposition turns a parent into
INACTIVE_WAIT with `children` populated; retreat clears the children and
returns the parent to INITIALIZED with a `history_log` entry.

**Ready-queue rule** (recomputed every iteration; replaces the static
priority-sorted queue):

```
A node is ready iff state == "INITIALIZED" AND either:
  (a) parent_id is None AND every dep in dependencies has status="proved"
      (top-level: classic DAG-style cross-sorry dependency)
  OR
  (b) parent_id is not None AND parent_id's state == "INACTIVE_WAIT"
      (sub-problem: parent suspended pending us)

Order ready_queue by priority (higher first), break ties on insertion order.
```

```
MAX_SLOTS = 3
active_agents = {}   # {task_id → sorry_id}
start_time = now()

# NOTE: dispatch-batch-start milestone was emitted at Phase 0 step 0
# via prove_deep_begin.py. Don't re-emit here.

LOOP:
  # ── Compute ready_queue dynamically (czy tree-walker semantics) ──
  ready_queue = compute_ready_queue(sorry_backlog)   # see rule above

  # ── Fill slots to MAX_SLOTS ──
  while len(active_agents) < MAX_SLOTS and ready_queue is not empty:
    sorry = ready_queue.pop(0)
    agent = launch_background_agent(sorry)
    active_agents[agent.task_id] = sorry.id
    set sorry.state = "ACTIVE_PROVING" in backlog

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
`run_in_background: true`. **Before constructing the prompt, check if this sorry
has prior-attempt history** (czy newloop port — `informalAgent.ts:741-763`):

```bash
# If sorry.history_log is non-empty (i.e., this sorry was retreated
# from at least once before), prepend the history block to the agent
# prompt so the LLM sees what was tried and can pick a DIFFERENT
# decomposition strategy.
HISTORY=$(python3 theme/scripts/read_history_log.py \
              --node-id "<sorry.id>" \
              --backlog-path theme/input/sorry_backlog.yaml)
# HISTORY is empty string if no history. Only prepend when non-empty
# (else we'd waste prompt tokens on a blank line):
if [ -n "$HISTORY" ]; then
    PROMPT_PREFIX="${HISTORY}\n\n"
else
    PROMPT_PREFIX=""
fi
```

The output (when non-empty) follows czy's exact format:

```
## Previous attempt history (DO NOT repeat failed strategies)
- Iteration N: decomposed into [...]
    Reason: <decision_reason>
  - <sub_id>: stuck (<fail_reason>)
  Retreat reason: <reason>
ACTION: Choose a DIFFERENT decomposition strategy from previous attempts.
```

Prepend this block to the body that follows. The agent prompt body:

```
{HISTORY block prepended here when sorry.history_log is non-empty}

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
Each terminal branch ends with `process_sorry_result.py` (real bash,
MANDATORY for proved/stuck/lake_build_fail). The need_sub_lemma branch
DOES NOT use process_sorry_result anymore — it calls validate_decomposition
+ decompose_node directly (decompose_node carries the sorry_list-refresh
+ sorry-pool-snapshot emit responsibility internally so the telemetry
invariant is preserved across this fork).

process_sorry_result.py bundles for proved/stuck/lake_build_fail:
backlog status update + sorry_list.json refresh + per-status milestone +
sorry-pool-snapshot telemetry + (proved branch only) cascade DONE
propagation upward via propagate_done.py. Skipping any individual step
breaks downstream consumers — bundling makes that structurally impossible.

```bash
python3 theme/scripts/process_sorry_result.py \
    --sandbox "$SANDBOX" \
    --sorry-id "<sorry_id>" \
    --status "proved|stuck|need_sub_lemma|lake_build_fail" \
    --module "Statlean.<Module>" \
    --lean-file "<path/to/file.lean>" \
    [--blocker "<one-line>"] \
    [--children-decomposition '<JSON>'] \
    [--parent-metrics '<JSON>']
```

```
if result.status == "proved":
  1. lake build Statlean.<Module>  — incremental verify
  2. if build OK:
     - Check whole-file zero sorry → update Verified.lean
     - git add + commit "prove: {theorem_name}"
     - Call process_sorry_result.py --status proved --sorry-id ... --module ...
       (czy newloop port: process_sorry_result internally also sets
        state=DONE + done_reason=proved AND calls propagate_done.py to
        cascade DONE up the tree. The next ready_queue computation will
        automatically pick up any newly-eligible nodes — no manual
        unlocks/dependencies handling needed in this branch.)
  3. if build FAIL:
     - Log error, mark sorry as pending, priority += 3
     - Call process_sorry_result.py --status lake_build_fail --sorry-id ... --blocker ...

if result.new_knowledge:
  - 将 new_knowledge YAML 块写入临时文件（如 /tmp/new_knowledge_{sorry_id}.yaml）
  - run("python3 scripts/ingest_knowledge.py --input /tmp/new_knowledge_{sorry_id}.yaml")
  - 脚本自动：验证 level/trigger/confidence → 去重 → 追加到 proof_knowledge.yaml → 输出摘要

elif result.status == "stuck":
  - Mark sorry as pending
  - Increase priority by 5 (deprioritize)
  - Log blocker info for future reference
  - Call process_sorry_result.py --status stuck --sorry-id ... --blocker ...
    (czy newloop port: process_sorry_result internally bumps stuck_rounds
     by 1; this is the field record_retreat thresholds against.)
  - **Two-counter stuck gate** (czy newloop port + A1 — see
    `controlAgent.ts:604-614` and `docs/A1_RESTRATEGIZE_SPEC.md` §7):
    Re-read the parent (parent_id of the failed sorry) from the backlog
    and apply this discrimination on `parent.attempts` and
    `parent.stuck_rounds`:

    1. **If `attempts >= 3` → call `record_retreat.py`** (decomposition
       itself wrong; full reset, attempts→0):

       ```bash
       python3 theme/scripts/record_retreat.py \
           --parent-id "<parent_id>" \
           --retreat-reason "attempts reached 3; decomposition exhausted" \
           --results-json '[{"sub_problem_id":"<sorry_id>","status":"stuck",
                             "fail_reason":"<blocker, sliced 200 char>"}]' \
           --sandbox "$SANDBOX"
       ```

       Bundles: removes ALL descendants, resets parent state→INITIALIZED,
       stuck_rounds→0, **attempts→0**, children→[], appends HistoryLogEntry
       with full retreat context, emits `retreat-triggered`.

    2. **Else if `stuck_rounds >= 3` → call `restrategize_node.py`**
       (proof STRATEGY wrong; preserve decomposition strategy via
       attempts++ bookkeeping):

       ```bash
       python3 theme/scripts/restrategize_node.py \
           --parent-id "<parent_id>" \
           --sandbox "$SANDBOX"
       ```

       Bundles: removes ALL descendants (parent stays — D-2 deviation
       per A1 spec §2.3), resets parent state→INITIALIZED,
       stuck_rounds→0, children→[], **bumps parent.attempts**, appends
       HistoryLogEntry with structured `retreat_reason: "restrategize:
       cleared N children, M proved"`, emits `restrategize-triggered`.

       The script enforces the gate at script level too: refuses if
       attempts >= 3 (caller should retreat instead). One less footgun.

    3. **Else** (attempts < 3 AND stuck_rounds < 3): continue the prover
       loop. Higher stuck_rounds will accumulate from process_sorry_result
       on subsequent stucks; eventually crosses one of the thresholds.

    Locked theorem signature on the parent is UNTOUCHED in either path
    (Rule 3 Layer 1).

    After EITHER script runs, the parent re-enters INITIALIZED with
    full history; the next iteration's ready_queue picks it up. When
    the next prove agent is dispatched, `read_history_log.py` (called
    by launch_background_agent above) will surface the prior attempts
    in the prompt with the "ACTION: Choose a DIFFERENT decomposition
    strategy" trailer (for retreat) or context that 3 prior strategy
    rounds failed (for restrategize).

    **Determinism tier (Rule 9 §3)**: T2. The agent reads two yaml
    fields and dispatches one named script — no LLM judgment in the
    gate itself. Skipping a script is detectable by absence of the
    matching milestone (`retreat-triggered` or `restrategize-triggered`).
  - **User-trust gate** (web-UI only — silently skipped in CLI-standalone
    mode when the tool is unavailable):
    If the blocker description mentions missing Mathlib infrastructure
    (patterns: "unknown identifier", "unknown constant", "no such lemma",
    "API doesn't exist", "需要 X 但 Mathlib 没有") OR the sorry has been
    stuck twice in a row, call
    `mcp__statlean_web_ui__request_user_decision` with these REQUIRED
    fields:

    ```
    question: <prose>. MUST use $...$ inline math and $$...$$ block math
              for any formula — the UI renders KaTeX. Don't leave LaTeX
              as plain text (it'll display as "$\sum_j..." which is
              unreadable).

    options:  ["trust_as_axiom", "trust_and_finish", "investigate_deeper", "abort"]
              · trust_as_axiom    → trust this one, KEEP attacking other
                                    items in ready_queue
              · trust_and_finish  → trust this one AND immediately wrap
                                    up the round (skip remaining queue,
                                    jump to Phase 3). Use when user
                                    likely wants to stop early.
              · investigate_deeper → re-dispatch with extra budget
              · abort              → give up

    trust_description: <plain Chinese, REQUIRED when options contain
                       trust_*>. Bulleted list naming each Mathlib /
                       Statlean infra gap or math fact being trusted.
                       Example for the χ² case:
                         "1. Mathlib 无 χ² 分布定义 (Probability.Distributions.ChiSquared 缺)
                          2. Mathlib 无 Hilbert-Schmidt 紧算子谱展开
                          3. Mathlib 无非 Gaussian iid 级数收敛 ∑_j λ_j(χ²-1) 判据"
                       Surfaces in UI as a separate audit panel so user
                       sees and the cross-job decisions table records
                       exactly what got trusted.

    ready_queue: <array — REQUIRED when options contain trust_*>.
                 Snapshot of remaining ready_queue (excluding current
                 sorry). One entry per item, with id + theorem + priority
                 + estimated_lines. Top 50 by priority. Lets user see
                 "if I trust_and_finish, this is what I'm skipping".
    ```

    Act on the reply:
      - USER_CHOICE: trust_as_axiom    → leave the sorry with comment
        `-- TRUSTED (user-approved infra gap: <one-line summary of
        trust_description>)`, skip further dispatches for this id,
        continue DAG loop attacking remaining ready_queue.
      - USER_CHOICE: trust_and_finish  → leave the sorry with comment
        `-- TRUSTED (user-approved infra gap: <reason>)`, mark all
        remaining ready_queue items as `pending (user requested early
        finish)`, **exit Phase 2 LOOP immediately and proceed to Phase 3
        finalize**. Do NOT dispatch additional items.
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
  Two-step process (czy newloop port — replaces the older
  validate_decomposition.py + manual yaml edit recipe):

  1. **Validate the decomposition** (still T2 — keep validate_decomposition
     as the size-monotone "pushing the pea" guard):

     ```bash
     python3 theme/scripts/validate_decomposition.py \
         --parent-metrics  '<JSON: goal_pp_lines, estimated_lines, deps_count>' \
         --children-metrics '<JSON: same shape, one per sub-lemma>'
     ```
     Exit 0 → continue to step 2. Exit 1 → emit decomposition-rejected,
     mark parent pending, do NOT add children.

  2. **Apply the decomposition atomically** via decompose_node.py
     (replaces the manually-written yaml mutation):

     ```bash
     python3 theme/scripts/decompose_node.py \
         --parent-id "<sorry_id>" \
         --sub-problems-json '[{"id":"<sorry_id>.sub1","theorem":"...",
                                "blocker":"...","estimated_lines":...},
                               {"id":"<sorry_id>.sub2",...}]' \
         --decision-reason "<why this decomposition; surfaces in retreat
                            history if children later fail>" \
         --sandbox "$SANDBOX"
     ```
     The script (T2 atomic):
      - Inserts sub-rows with state=INITIALIZED, parent_id=<parent>,
        children=[], history_log=[], stuck_rounds=0
      - Sets parent.state=INACTIVE_WAIT, parent.children=[new ids]
      - Stashes `--decision-reason` on parent as `_pending_decision_reason`
        (consumed by record_retreat if children later fail)
      - Locked theorem signature on parent UNTOUCHED (Rule 3 Layer 1)
      - Emits subtasks-split milestone
      - Validates: parent must exist; parent.state must be INITIALIZED
        (cannot decompose an already-decomposed parent without retreat
        first); sub ids globally unique (no collision; no dup in request)

  After step 2 the parent is INACTIVE_WAIT and the new sub-rows are
  INITIALIZED. The next ready_queue computation picks up the sub-rows
  automatically (parent is INACTIVE_WAIT → its children with
  state=INITIALIZED qualify as ready under the tree-walker rule above).
  No manual queue manipulation needed.
```

---

## Phase 3: Checkpoint

After the scheduling loop exits (all done, or time budget reached):

1. **Commit**: Any uncommitted proved work (incremental commits are
   handled by `process_sorry_result.py` per result; this is just for
   stragglers like Verified.lean updates).

2. **Collect new_knowledge** YAML blocks from this cycle's sub-agents
   into `/tmp/new_knowledge.yaml` (will be ingested by step 3 below).

3. **Cycle finalize (MANDATORY, real bash)**:
   ```bash
   python3 theme/scripts/prove_deep_end.py \
       --sandbox "$SANDBOX" \
       --target "<TARGET>" \
       --proved <K> --stuck <J> --remaining <R> \
       --memory-summary "<NATURAL LANGUAGE — see below>" \
       [--new-knowledge-file /tmp/new_knowledge.yaml]
   ```
   The script bundles: sync_sorry_backlog.py + MEMORY.md append +
   ingest_knowledge.py + `memory-md-updated` + `dag-cycle-done`
   milestones. **`--memory-summary` MUST be ≥ 20 chars after trim**;
   the script exits 1 (cycle NOT finalized) on empty/placeholder values.
   This makes "Update MEMORY.md" structural rather than aspirational —
   you don't get to skip it by forgetting.

   `--memory-summary` content guidelines: 1-3 sentences in natural
   language. Cover any of: (a) what new Mathlib pattern was learned,
   (b) which routes did NOT work and why (anti-patterns), (c) what
   blockers persisted and what would be needed upstream. Format is
   free; the script just appends under a dated header in MEMORY.md.

4. **Screen output** — see "屏幕输出" block below for the canonical
   compact-summary format.

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
