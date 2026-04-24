---
description: Attack a specific sorry with full Mathlib search
allowed-tools: Read, Edit, Grep, Glob, Bash(lake:*), Bash(grep:*), Task, WebSearch, WebFetch, mcp__statlean_web_ui__request_user_decision
model: opus
argument-hint: [file:line or theorem-name]
---

# Prove Sorry

Target: $ARGUMENTS

## Protocol

You are attacking a specific `sorry` in the StatLean project. Follow this exact workflow:

### Phase 0: Phase 0 工具链（强制，在任何编辑之前）
0. **签名索引**：`python3 scripts/extract_signatures.py <file>` 读声明索引，定位 sorry 行号后再 Read 指定范围（不盲读全文件 >200 行的）
1. **增量编译**：tactic 试错阶段用 `bash scripts/check_snippet.sh <file> <start> <end>`

### Phase 0.5: 路线搜索（五级 Fallback，在 Phase 1 之前执行）

按成本递增依次检查，一旦获得完整路线则跳过后续级别：

**R1: 人类显式输入**（成本: 0-5K token）
- 检查 `$ARGUMENTS` 是否包含 `--roadmap <path>` 或 `--roadmap "inline: ..."`
- 检查用户消息中是否有证明描述（关键词："证明路线"、"proof sketch"、"先...再...然后..."、"关键是用..."）
- 有文件路径 → `python3 scripts/parse_proof_roadmap.py <path> --theorem <name>`
- 有内联文字 → `python3 scripts/parse_proof_roadmap.py --inline "<text>" --theorem <name>`
- 输出 `completeness: full` → 直接进 Phase 3 执行
- 输出 `completeness: partial` → 已知步骤保留，对 `gap: true` 步骤继续 R2-R5
- 输出 `completeness: hint` → 提取关键词注入搜索，继续 R2-R5

**R2: 输入上下文中的证明体**（成本: 2-10K token）
- 进入条件：R1 无结果 或 R1 的 gap 步骤需要补全
- 检查当前会话是否有 PDF/LaTeX 输入（如 `/pipeline` 模式）
- 检查 `theorems.yaml` 是否有 `proof_body` 字段
- 有 → `python3 scripts/parse_proof_roadmap.py --format latex --inline "<proof_body>" --theorem <name>`
- 与 R1 部分路线合并（若有）

**R3: 本地知识库匹配**（成本: 0-2K token）— 已有流程
- 读 `theme/proof_knowledge.yaml`，按 trigger 匹配当前 goal 形态
- L3 匹配且 confidence ≥ 4 → 按策略执行，跳过 R4
- L2 匹配 → 部分路线，辅助后续搜索
- 未匹配 → 继续 R4（仅当等级 ≥ C 且定理是已知数学结果时）

**R4: Web 快速探测 + 深入获取**（成本: 3-50K token）
- 进入条件：R1+R2+R3 均无完整路线，且 sorry 等级 ≥ C，且定理是已知数学结果（非原创构造）
- S-B 级 sorry → 跳过 R4，直接 R5（简单 sorry 不值得花 Web 搜索 token）

- **Stage 1 — 快速探测**（~3-5K token，必做）：
  ```
  WebSearch "<theorem_name> proof Lean 4 Mathlib"
  ```
  读结果摘要（不 Fetch 任何页面）。判断：有 Lean 形式化？有 ProofWiki/教材证明？
  → 无有价值结果 → **立刻停止**，转 R5

- **Stage 2a — Lean 形式化获取**（~10-20K token）：
  触发：Stage 1 发现 Lean/Mathlib 形式化链接
  → WebFetch 目标页面 → 提取 API 名称 → 回到索引确认 → confidence: 5

- **Stage 2b — 证明骨架获取**（~15-30K token）：
  触发：Stage 1 发现 ProofWiki / 教材 / MathOverflow 证明
  → WebFetch 最相关 1-2 页 → `parse_proof_roadmap.py` 解析 → confidence: 3-4

**R5: LLM 自主探索**（当前流程，成本: 50-300K token）
- R1-R4 均无完整路线时进入
- 此时可能携带 R1-R4 的部分成果（hint 关键词、L1/L2 匹配、搜索背景信息）
- 不是从零开始，而是在累积的部分信息基础上探索

### Phase 1: Understand (do NOT edit yet)
1. Read the file containing the sorry (use extract_signatures first, then Read specific line range).
2. Read surrounding context (imports, helper lemmas, upstream definitions).
3. **条件搜索（省 token）**：
   - **如果 Phase 0.5 已获得完整路线** → 按路线 key_api 定向 grep 查签名，跳过全文读取
   - **如果 R3 的 L3/L2 已匹配** → 按 key_api 定向 grep 查签名，跳过全文读取：
     - StatLean API: `grep -i '<name>' theme/statlean_api_index.tsv`
     - Mathlib API: `grep -i '<name>' theme/mathlib_full_type_index.tsv`
   - **未匹配时第一级**：读 `theme/mathlib_api_index.md` + grep 两个索引
   - **第二级**：索引没有 → `#check` / `exact?`
   - **第三级**：前两级都失败 → grep Mathlib 源码（必须注明升级理由）

### Phase 2: Strategy
4. Pick the best strategy. Screen output: 1 line only — `Strategy: X via [API1, API2]`.
   Full tradeoff analysis only if user decision needed; otherwise write to report file.
5. Pick the simplest one that uses existing Mathlib API.

### Phase 3: Implement
6. Write the proof replacement (edit the sorry line).
7. Build with `lake build <module>` to check.
8. If build fails, read errors carefully. Fix and rebuild (max 5 iterations).
   - **API 名称错误快速修复**：如果 build 报 `unknown identifier` 或 `unknown constant`:
     1. 先查 `grep -i '<name>' theme/api_gotchas.tsv`（秒级，~12 条高频坑）
     2. 命中 → 按 correct_api 替换
     3. 未命中 → `grep -i '<name>' theme/mathlib_full_type_index.tsv`（51K 条）
     4. 仍未命中 → API 可能真不存在，考虑替代路线
     **不要猜第二个名字直接写代码。**

### Phase 3.5: 基础设施入库（强制 — 证完子引理立即执行）
每产生一个新引理/定义，立即：
1. 按数学对象放入正确 `Statlean/` 子目录（不存在则创建）
2. 与 sorry 共存于同一文件用 section 隔离即可，不搞 FooBase 拆分
3. 更新 `Statlean.lean` import
4. `lake build Statlean.<Module>` 验证编译通过

### Phase 4: Verify
9. Run `lake build` (full project) to ensure no regressions.
10. Report: what was proved, which Mathlib lemmas were used, and any new insights for MEMORY.md.

### Phase 5: Knowledge Ingestion（强制 — 无论成功或 stuck）

发现任何 L1/L2/L3 pattern（正面或负面）→ 通过 `scripts/ingest_knowledge.py` 标准流程入库，不等用户确认。

**效率反思（build 循环 ≥ 5 轮时强制）**：
回顾哪些轮次是重复劳动，提取 workflow pattern（"怎么组织证明以避免试错"），
作为 `workflow` 字段入库到 L2/L3 条目中。workflow 描述方法论而非 API。

**步骤**：
1. 把新 pattern 写成 YAML 文件（如 `/tmp/new_knowledge.yaml`）：

正面 pattern（证明成功时）：
```yaml
new_knowledge:
  - level: L3  # or L2, L1
    trigger: "<goal 形状>"
    strategy: "<证明架构>"  # L3
    # chain: "<引理链>"     # L2
    # tip: "<技巧>"         # L1
    key_api: [...]
    confidence: <3-5>
```

负面 pattern（发现死路时）：
```yaml
new_knowledge:
  - level: L3  # or L2, L1
    trigger: "<goal 形状>"
    anti: true
    strategy: "DO NOT <走这条路>. <原因>. Must use <正确路线>."
    confidence: <3-5>
```

2. 运行入库脚本：
```bash
python3 scripts/ingest_knowledge.py --input /tmp/new_knowledge.yaml
```
脚本自动执行：验证 level/trigger/confidence → 去重检查 → 追加到 `theme/proof_knowledge.yaml` → 输出入库摘要。

confidence 评分: 5=所有同类goal, 4=大部分, 3=特定子类, 2=仅本定理(不入库), 1=肯定特例(不入库)

在报告的「已入库 proof_knowledge」section 列出本轮写入的条目。

## Diverging Proof Trees — Handling Strategy

Real proofs diverge: closing one `sorry` often spawns 2-5 new sub-goals. Some branches are deep and hard. Use this protocol to stay productive.

### Triage: Classify Every Sorry

Before attacking, classify each sorry into one of four types:

| Type | Definition | Action |
|------|-----------|--------|
| **Leaf** | No dependencies on other sorries; self-contained sub-goal | Attack directly, highest ROI |
| **Intermediate** | Blocks downstream proofs but has no blockers itself | Attack second; unlocks more work |
| **Blocked** | Depends on another sorry being resolved first | Skip until blocker is resolved |
| **Honest** | Requires Mathlib infrastructure that genuinely doesn't exist | Mark with detailed comment, do NOT spend cycles |

Run triage BEFORE starting any proof work:
```
# Quick triage scan
grep -n 'sorry' <file> | head -30
```
For each sorry, spend 2 minutes checking if Mathlib has the needed API. If not → Honest. If yes → classify as Leaf/Intermediate/Blocked.

**User-trust gate for Honest sorries** (web-UI only — silently skipped in CLI-standalone mode when the tool is unavailable):
Immediately after classifying a sorry as Honest, call the MCP tool:
```
mcp__statlean_web_ui__request_user_decision({
  question: "Sorry <theorem_name> at <file:line> seems blocked by missing Mathlib infrastructure (describe what's missing in one sentence). How should we proceed?",
  options: ["trust_as_axiom", "investigate_deeper", "abort"]
})
```
Act on the returned tool result:
- `USER_CHOICE: trust_as_axiom` → leave the `sorry` in place with comment `-- TRUSTED (user-approved infra gap: <reason>)`, move to the next sorry. Do **not** spend further cycles on this one.
- `USER_CHOICE: investigate_deeper` → treat it as a non-Honest sorry and proceed to Phase 1.
- `USER_CHOICE: <free-text hint>` → the user gave a proof route; feed the hint into Phase 0.5 R1 (`parse_proof_roadmap.py --inline "<hint>" --theorem <name>`) and continue.
- `USER_ABORTED: …` → stop working on this sorry, report it in the final summary.
- Tool not found / tool error → fall back to CLI-default behavior (leave honest sorry with comment, do NOT spend cycles).

### Depth Budget

Each proof branch gets a **depth budget** (default: 3 levels of sorry-replacement before escalation).

- **Level 0**: Original sorry from the theorem statement.
- **Level 1**: Sub-goals created by replacing the original sorry with a tactic proof.
- **Level 2**: Sub-sub-goals from filling Level 1 sorries.
- **Level 3**: STOP. If a branch reaches depth 3 with remaining sorries:
  1. Extract the sub-goal as a standalone `lemma` with a descriptive name.
  2. Leave an honest sorry with a comment explaining what's needed.
  3. Report the extracted lemma as a new "ticket" for future work.

This prevents infinite descent into one hard branch while other branches wait.

### Divergence Protocol

When replacing one sorry creates multiple new sub-goals:

1. **Count**: How many new sorries appeared?
2. **Classify each** using the triage table above.
3. **Prioritize**:
   - Attack all Leaf sorries first (they close immediately).
   - Then attack Intermediate sorries that unblock the most downstream work.
   - Skip Blocked and Honest sorries.
4. **Extract if spreading**: If a single sorry spawns 4+ sub-goals, factor the proof into helper lemmas:
   ```lean
   -- Instead of one monolithic proof with 5 sorries:
   private lemma helper_integrability : ... := by sorry
   private lemma helper_bound : ... := by sorry
   theorem main : ... := by
     have h1 := helper_integrability ...
     have h2 := helper_bound ...
     exact ...
   ```
   This makes each sorry independently attackable (and parallelizable).

### Parallel Sub-Agent Spawning

When you detect **independent sub-goals** (sorries that don't depend on each other):

1. Extract each as a named lemma in the same file.
2. Build to confirm the extraction type-checks (main theorem uses the lemma names).
3. Report the list of independent lemma names — the pipeline can spawn one agent per lemma.

Independence test: Two sorries are independent if neither's proof would use the other's result. Check by reading the type signatures.

### Infrastructure Building (optional — when Mathlib lacks primitives)

When Mathlib genuinely does NOT have the needed lemma but it CAN be proved from
lower-level API (~5-50 lines), build it instead of giving up:

1. **Classify the gap**: Is it a missing algebraic identity, a missing bound,
   or a missing structural result?
2. **Estimate cost**: Can it be proved in ≤50 lines from existing Mathlib API?
   - YES → Build it as a `private lemma` in the same file.
   - NO (needs 100+ lines of new infrastructure) → Extract as a standalone
     module in `Statlean/` with honest sorry for the hardest sub-goals.
3. **Common buildable patterns**:
   - Product telescoping: `‖∏zᵢ - ∏wᵢ‖ ≤ ∑‖zᵢ-wᵢ‖` (Finset induction + `norm_mul_le`)
   - Custom Hölder / interpolation: from `MemLp` + `integrable_mul`
   - Fubini slicing: `integral_prod` + `integral_prod_symm`
   - Pointwise → integral: `integral_mono_ae` + custom pointwise lemma
4. **Build pattern**: Write the helper, build, fix, verify. Same 5-cycle limit.
5. **Report**: Tag built infrastructure as `[INFRA]` in the prove report.

Example: Mathlib has no `norm_prod_sub_prod_le` (ring product telescoping).
Built it via `Fin.prod_univ_castSucc` induction + `norm_add_le` + `norm_mul_le`
+ `Finset.norm_prod_le'` + `Finset.prod_le_one`. ~25 lines, reusable.

### Hard Branch Escalation

A branch is "hard" if after 3 fix-build cycles it still has sorries AND
Mathlib search hasn't found relevant API AND the infrastructure building
route above is too expensive (>50 lines). When this happens:

1. **Stop immediately.** Do not keep trying variations.
2. Write a structured comment:
   ```lean
   /- HARD BRANCH: <lemma_name>
      Goal: <the Lean goal state>
      Tried: <list strategies attempted>
      Missing: <what Mathlib API would be needed>
      Possible routes: <any partial leads>
      Infra cost: <estimated lines to build from scratch>
   -/
   sorry
   ```
3. Check if the hard branch is a **blocker** (does the main theorem depend on it?):
   - If yes: the main theorem stays sorry. Report this as the critical path.
   - If no: close other branches first, come back to this one later.

### Progress Tracking — 输出分流（强制）

**屏幕输出**（紧凑摘要，≤3 行）：
```
PROVE: <theorem_name> — sorry N→M | closed: [names] | 入库 K 条
详情: reports/prove_report_<theorem>.md
```

**文件存档**（完整详情，写入 `reports/prove_report_<theorem>.md`）：
```
PROVE REPORT: <theorem_name>
  Sorries before: N
  Sorries after:  M
  Closed:         [list of lemma names proved]
  Extracted:      [list of new helper lemmas with sorry]
  Honest:         [list of genuinely blocked gaps]
  Hard:           [list of branches that need escalation]
  Critical path:  <the one sorry that blocks everything>

  Strategy analysis: <full tradeoff analysis from Phase 2>
  Build errors encountered: <error summaries and fixes>

  已入库 proof_knowledge.yaml:
  - [L1/L2/L3] <trigger> — <正面/anti> — <来源>
```

用 Write 工具写入报告文件，屏幕只输出摘要行。

## Key Mathlib patterns (from project memory)
- `Pi.pow_apply` for `(f ^ 2) x` → `f x ^ 2`
- `ae_of_all` instead of `Eventually.of_forall`
- `variance_nonneg`, `variance_eq_sub`
- `integral_condVar_add_variance_condExp` for law of total variance
- `memLp_two_iff_integrable_sq` for L² ↔ integrable square
- `MemLp.condExp` for conditional expectation stays in L²
- `Polynomial.hasDerivAt_aeval` for analytic → algebraic derivative
- `integral_const_mul` (not `integral_mul_left`) for `∫ r * f = r * ∫ f`
- `push_cast [Nat.factorial_succ]` + `ring` for factorial arithmetic
- `Nat.strongRecOn` for strong induction

## Constant Relaxation Protocol

When a sorry involves a specific constant (like `1/6` in a Taylor bound), check:
1. Does the final theorem use `∃ C > 0`? If yes, the exact constant doesn't matter.
2. Can Mathlib prove a weaker constant? If yes, use it.
3. Reformulate the helper with the provable constant, verify the chain still works.

Example: `charfun_taylor_third_moment` — sharp bound is `|θ|³/6`, but Mathlib's `exp_bound`
gives `2/9` (for `|θ|≤1`). We proved `4|θ|³` via case split (`exp_bound` + triangle inequality),
which suffices because Berry-Esseen's final constant is existential.

## Charfun Proof Pattern (reusable template)

For proving bounds on `charFun (μ.map Y)`:
1. **Unfold**: `charFun_apply_real` + `integral_map_of_stronglyMeasurable`
2. **Integrability**: Extract from `MemLp` via `memLp_three_to_two/one`, `.integrable`, `.integrable_sq`, `.integrable_norm_rpow`
3. **Complex bridge**: `integral_complex_ofReal` to convert `∫ ↑f = ↑(∫ f)`
4. **Split integral**: `integral_sub`, `integral_add` (need integrability of each piece)
5. **Pointwise bound**: Prove/use a pointwise lemma, then `integral_mono_ae`
6. **Factor constants**: `integral_const_mul` to pull out `|t|³` etc.

## Guardrails
- Do NOT introduce hypothesis-passing tautologies (`theorem foo (h : P) : P := h`)
- If the sorry genuinely needs missing Mathlib infrastructure, say so explicitly and leave an honest sorry with a detailed comment
- Prefer short compositional lemmas over monolithic proofs
- Do NOT spend more than 5 build cycles on one sorry — extract or escalate
- Do NOT go deeper than depth 3 without extracting helper lemmas

## 输出预算规则（强制）

- 屏幕文本输出（非工具调用）总预算 ≤ 3K token（单 sorry）
- 超预算时自动切换为"极简模式"：只输出 sorry 计数变化 + 文件路径
- Phase 2 策略分析 → 1 行摘要（完整分析写报告文件）
- Phase 3 build 错误 → 1 行错误摘要 + fix 动作（build log 在 Bash 工具输出里已有）
- Phase 4 报告 → 2-3 行屏幕摘要 + 完整报告写 `reports/prove_report_<name>.md`
- Phase 5 知识入库 → "入库 N 条 pattern"（YAML 和脚本输出在 Bash 工具内）
- 工具调用输出（Bash、Read、Grep 等）不计入此预算
- `/prove-out` 模式豁免此限制（演示模式需要详细输出）

## Output Conventions (REQUIRED — web UI contract)

See `theme/conventions/ui-signals.md` for full specification.

When invoked as part of the web pipeline (report stream is being read
by `statlean-web`'s `StepBreakdown` panel), announce each Phase
transition with a line of the exact form:

```
## Step N: <short title>
```

(two hashes, space, word `Step`, space, integer, colon, space, title).
Map prove's internal Phases to Step numbers as follows (or as each
phase actually executes; the numbering is for UI ordering, not a
rigid protocol):

- `## Step 1: Phase 0 — route search + signature probe`
- `## Step 2: Phase 1 — goal analysis`
- `## Step 3: Phase 2 — tactic attempts + build loop`
- `## Step 4: Phase 3 — honesty check + extraction`
- `## Step 5: Phase 4 — report + knowledge ingestion`

Skip the UI announcement if the prove session is CLI-standalone
(no web connection) — adding harmless markdown headers does no harm
but is unnecessary noise for CLI-only users. When launched as a prove
subagent by `/pipeline`, you ARE driving the web UI and MUST emit.

Fallback shapes `### Step N:` / `**Step N:**` / `# Step N:` are
tolerated by the parser but MUST NOT be introduced in new skills.
