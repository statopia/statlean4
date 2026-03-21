# Claude Code 项目配置

## 操作授权

本项目已预授权所有操作，包括：
- git 操作（commit、push、branch 等）
- 文件读写、创建、删除
- 脚本执行（make、python、bash 等）
- Lean 编译（lake build 等）

**无需逐次确认，直接执行。**

## Git 远程仓库

- **仓库地址**: `git@github.com:mockingbird-gan/statlean4.git`（SSH）
- **SSH 公钥**: `ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIIYGAXq8NzQtFRG4YobuSL7jEOl+FuiAInKBHgvqKv4O mockingbird-gan`
- **push 时必须使用 SSH**，不要用 HTTPS。如果发现 remote URL 是 HTTPS，先执行：
  ```
  git remote set-url origin git@github.com:mockingbird-gan/statlean4.git
  ```

## 沟通语言

- **用中文回答用户问题**（除非用户用英文提问）
- Lean 代码中的注释和 docstring 用英文
- commit message 用中英文均可

---

## 模块组织原则

### 按数学对象组织，不按证明项目
- 文件路径反映数学对象：`Gaussian/Poincare.lean`，不是 `Concentration/GaussianPoincare.lean`
- 一个数学对象的所有内容（定义、已证定理、sorry gap）放同一文件，用 section 隔离
- 定理名必须语义化：`frechet_mean_existence_transfer`，不是 `proposition_008_proposition_9`

### 同一文件内 sorry 和已证引理共存
- 已证引理和 sorry gap 可以放在同一文件中，用 `section` 隔离
- **不需要**拆分为 `FooBase.lean` + `Foo.lean`
- `Statlean/Verified.lean` 是附加验收工具（只 import 整文件零 sorry 的模块），**不驱动文件拆分**

### Mathlib 文件组织规则（强制）
- **中间引理和主定理放同一文件**，用 section/namespace 隔离（Mathlib 标准：Taylor、Hahn-Banach 等）
- **只有「独立可复用」的基础设施才拆出单独文件**（如 ANOVA 方差分解可被 Poincaré、LSI 复用）
- **没有 `*Base.lean` 模式**：不按证明状态（已证/未证）拆分文件
- **500-900 行的单文件完全正常**：不必因为行数多就拆分
- **按数学对象/抽象层级组织**：文件路径反映数学概念，不反映证明项目或状态

### 薄封装必须删除
- 如果 `f x` 只是 Mathlib `g x` 的别名，不保留 wrapper，直接内联替换调用点
- 例：`memLp_three_to_two hLp` → `hLp.mono_exponent (by norm_num : (2 : ENNReal) ≤ 3)`

### 空壳必须清理
- 空目录、只含 `namespace ... end` 的空文件、不被 import 的孤立文件 → 删除
- `Statlean.lean` 的 import 列表应与实际文件一一对应

---

## Import 迁移规则

- 删/移模块前**必须 grep 全仓库**：`grep -r "旧模块名" --include="*.lean"`
- 替换 import 时分析实际依赖，只 import 真正用到的模块
- 同时更新非 Lean 文件中的路径引用（`scripts/`、`theme/` 等）
- Lean 4 硬性规则：`import` 必须在文件最前，module docstring `/-! ... -/` 在所有 import 之后

---

## 形式化策略

**交互式形式化手册见 `theme/formalize_playbook.md`**（输入解析 → 内容获取 → 签名设计 → 证明 → 诚实性检查）。
用户在会话中说「形式化 XX 里的 YY」时，**必须遵循该 playbook 的 Step 0-7**。

## 证明策略

**证明操作手册见 `theme/prove_playbook.md`**（决策树 + 错误修复表 + 策略选择表）。
交互式会话和 pipeline prove agent 都遵循该 playbook。

### 攻击顺序
- sorry 形成依赖 DAG，从叶节点开始攻击
- 分类：(A) Mathlib 缺前置 API → 等待或自建基础设施；(B) 路线清晰 → 直接攻击；(C) 依赖未解决的 sorry → 排后
- 优先级 B > A > C

### 关键模式
- **强归纳**优于普通归纳：需要 `∀ m < n` 时用 `Nat.strongRecOn`
- **Case split**：对连续参数（如 `|t|`）分大小情形，小值用精细链，大值用粗糙界
- **Telescope**：乘积/求和望远镜展开 Mathlib 未必有现成的，准备手搓
- **IBP 路线**：`integral_mul_deriv_eq_deriv_mul_of_integrable` + density chain rule
- **L^p 降级**：`MemLp.mono_exponent` + `integrable_withDensity_iff` 处理 Gaussian 可积性

### Sorry 等级判定与校准（强制）

**参考表**：`theme/sorry_grading.md`（等级定义 + 实际攻击记录 + 当前评估）

**攻击前**：对目标 sorry 进行 S/A/B/C/D/E 等级判定，输出预计时间和 token。
**攻击后**：记录实际数据到 `theme/sorry_grading.md` 的「实际攻击记录」表，校准等级范围。

校准规则：
- 实际偏离预计 >50% → 标注异常原因
- 同等级连续 3 次偏离 → 调整该等级的预计范围
- 新产生的 sorry → 判定等级并加入「当前评估」表
- 已关闭的 sorry → 从「当前评估」移到「实际记录」

详见 `theme/prove_playbook.md` §1（启动流程步骤 5）和 §9（攻击后校准）。

### 验收标准
- `lake build` 零错误
- sorry 数只减不增
- `lake build Statlean.Verified` 零 sorry 警告

### 反例搜索（强制，sorry 攻击 > 5 轮时触发）

**本节是硬性规则。违反 = 可能在 FALSE 声明上浪费 10+ 轮 agent。**

**触发条件**：同一 sorry 连续 stuck ≥ 5 轮（跨会话累计，查 `sorry_backlog.yaml` 的 `stuck_rounds`）。

**执行流程（不可跳过）**：
1. **暂停攻击**，花 1 轮专门搜索反例
2. **构造反例候选**：
   - 取极端参数（T→∞, M→0, μ=点质量, ν=均匀分布等）
   - 检查 LHS 和 RHS 的数值大小关系
   - 特别关注：紧支撑 vs 无穷支撑、密度有界 vs 点质量、矩有限 vs 矩无穷
3. **验证反例**：用 Lean `#eval` 或数值计算检查具体参数
4. **结果处理**：
   - 找到反例 → **立即修改声明**（不继续攻击 FALSE 目标）
   - 未找到 → 记录"已验证无反例"到 sorry_backlog.yaml，继续攻击
5. **入库**：如果发现 FALSE 声明，作为 anti-pattern 写入 `proof_knowledge.yaml`

**教训**：Berry-Esseen 中两个 FALSE 声明各浪费 5-10 轮 agent：
- `hν_density` 假设太弱（点质量满足但不等式不成立）— 轮 10 才发现
- `triangleKernel_fourier_bound`（Paley-Wiener 禁止）— 轮 30+ 才发现
如果在第 5 轮就搜索反例，可以节省 20+ 轮。

### Subagent prompt 模板（强制格式）

**本节是硬性规则。所有 prove/prove-deep 的 subagent prompt 必须遵循此格式。**

**模板结构（3 段）**：

**段 1: 指令头**

**原则: 让 agent 不需要 Read 就能工作。不是靠规则禁止 Read，而是靠提供完整信息让 Read 不必要。**

```
目标: 在 <file> 的 L<N> 处插入以下代码骨架并填充 sorry:
验收标准: sorry 数从 N 降到 M
约束: 只修改 <file>。build ≤ 5 次。

文件读取: 禁止 Read >50 行。用 `grep -n` 定位行号后 Read ±15 行。
  禁止对 >200 行文件直接 Read。先 `python3 scripts/extract_signatures.py <file>`。

编译验证（每次 lake build 之前必须完成至少一项）:
  Level 0 — API 预查: `echo '#check @API_Name' | lake env lean --stdin`（0 秒，写任何 API 前必做）
  Level 1 — temp file: `cat > /tmp/test.lean << 'EOF' ... EOF && lake env lean /tmp/test.lean`（5 秒，新引理前 3 次 tactic 尝试在此完成）
  Level 2 — snippet: `bash scripts/check_snippet.sh <file> <start> <end>`（10 秒，修改单个 declaration 后）
  Level 3 — module build: `lake build Statlean.<Module>`（仅在 Level 0-2 通过后使用，≤ 5 次）

API 名错误修复: build 报 unknown identifier 时:
  1. `grep -i '<name>' theme/api_gotchas.tsv`
  2. `grep -i '<name>' theme/mathlib_full_type_index.tsv`
  不要猜第二个名字直接写代码。

每证完一个子引理立即写入 .lean 文件并验证，不要攒到最后。
如果 stuck，sorry 暂留并继续下一个子引理，不要停下来分析。

Mathlib API 搜索顺序（逐级升级，不跳级）:
  0. 路线 key_api → `grep -i '<name>' theme/mathlib_full_type_index.tsv`
  1. `grep -i '<keyword>' theme/statlean_api_index.tsv` + `theme/mathlib_full_type_index.tsv`
  2. `echo '#check @Name' | lake env lean --stdin` 或 `exact?`
  3. grep Mathlib 源码（必须注明"索引无此条目，升级到 grep"）

proof_knowledge 匹配（写代码前先做）:
  `grep -i '<goal关键词>' theme/proof_knowledge.yaml`
  匹配到 → 按 strategy 执行。匹配到 anti:true → 跳过该路线。

发现死路或 FALSE 声明 → 立即写 anti-pattern 到 /tmp/new_knowledge.yaml:
  ```yaml
  new_knowledge:
    - level: L3
      trigger: "<goal 形状>"
      anti: true
      strategy: "DO NOT <路线>. <原因>."
      confidence: 4
  ```
```

**段 2: 按任务复杂度分级提供信息**

**原则**: 提供**刚好足够**的信息让 agent 完成任务，不多不少。

| 复杂度 | prompt 内容 | 示例 |
|--------|------------|------|
| **低**（新定义+性质） | 代码骨架 + API 列表 (~20 行) | sinc4Kernel 定义+4 性质 |
| **中**（单个引理证明） | sorry±15 行上下文 + API 签名 + 路线 (~50 行) | cesaro_integral_bound |
| **高**（多步 API 组合） | sorry±15 行 + scope 假设 + 代码骨架 + API 签名 (~100 行) | fejer_convolution_bound |
| **很高**（全局重构/sSup） | **不委派**。主会话自己写代码，或拆成多个中等任务 | esseen_smoothing_ineq |

**低复杂度格式** (agent 不需要 Read):
```
在 <file> 末尾添加:
  def foo := ...
  lemma foo_nonneg : ... := by sorry  -- 用 <API>
  lemma foo_integral : ... := by sorry  -- 用 <API>
```

**中复杂度格式** (agent 可能需要 Read ≤ 30 行):
```
sorry 上下文 (L<N>±15):
<30 行代码>

scope 假设: hT, hM, hI_nn, ...
证明路线: 用 <API_1> 得 h1, 用 <API_2> 得 h2, linarith 组装
```

**高复杂度格式** (agent 可能需要 Read ≤ 50 行):
```
sorry 上下文 + scope 假设 (同上)
代码骨架:
  have h1 : <type> := by sorry -- <提示>
  have h2 : <type> := by sorry -- <提示>
  <组装 tactic>
```

**很高复杂度**: 主会话先拆成 2-3 个中等子任务，分别委派。

**段 3: 证明路线 + 前任发现（≤ 300 字）**
主会话提供的简要证明路线 + 之前 agent 在同一 sorry 上的关键发现。

格式:
```
**证明路线**: <≤ 200 字的路线>

**前任发现（不要重复这些工作）**:
- ❌ 路线 A 不可行: <原因> (agent round N)
- ❌ API X 不存在, 应用 API Y (agent round M)
- ✅ 子引理 Z 已证 (在 L<行号>)
```

**主会话的强制操作**: 每次 agent 返回后:
1. 从 agent result 提取关键发现（死路、FALSE 声明、已证子引理）
2. 追加到 session 累积发现列表
3. 下次派 agent 时，把累积发现写入段 3

**工具支持**: 可用 `python3 scripts/gen_agent_prompt.py <file> <line>` 自动生成段 1+2。

**禁止的 prompt 内容**：
- ❌ "分析可行性" / "探索替代路线" / "评估难度"（这些是分析，不是实施）
- ❌ 超过 500 字的数学推导（应在主会话做，不浪费 agent 上下文）
- ❌ "如果 stuck 就报告"（应改为 "如果 stuck 就 sorry 暂留并继续下一个子引理"）

**必须包含的 prompt 内容**：
- ✅ 验收标准（明确的 sorry 数变化）
- ✅ 已有 API 列表（减少重复搜索）
- ✅ "每证完一个子引理立即写入文件"
- ✅ "每个 Mathlib API 先 `#check`"
- ✅ build 次数上限
- ✅ "先 extract_signatures.py 获取索引。禁止 Read >50 行。"

**Agent 返回后的强制检查**：
1. 检查 sorry 数是否减少（`grep -c ' sorry$' <file>`）
2. 检查 build 是否通过（`lake build <module>`）
3. 如果 sorry 未减少且 stuck_rounds ≥ 3 → 触发 R6
4. 如果 sorry 未减少且 stuck_rounds ≥ 5 → 触发反例搜索
5. **核心指标**：agent 成功 = sorry 数减少。sorry 不变 = 该轮浪费（无论分析多精彩）

---

## 证明路线搜索 — 六级 Fallback 协议（强制）

**本节是硬性规则，所有证明流程（`/prove`、`/prove-deep`、`/prove-out`、`/pipeline` prove 阶段）必须遵循。**
**六级 = R1-R5 (原五级) + R6 (基础设施升级)。**

攻击 sorry 前，按成本递增依次执行路线搜索。获得完整路线后跳过后续级别：

```
R1: 人类显式输入（0-5K token）→ parse_proof_roadmap.py 解析
R2: 输入上下文证明体（2-10K token）→ PDF/LaTeX proof 块解析
R3: 本地知识库（0-2K token）→ proof_knowledge.yaml L3/L2/L1 匹配
R4: Web 快速探测 + 深入获取（3-50K token）→ WebSearch + WebFetch
R5: LLM 自主探索（50-300K token）→ 当前流程
```

**关键原则**：R1-R4 都是为了避免 R5（最贵且最不可靠的阶段）。
**S-B 级 sorry → 跳过 R4，直接 R5**（简单 sorry 不值得 Web 搜索 token）。
**路线解析脚本**：`python3 scripts/parse_proof_roadmap.py`（多格式：纯文字/LaTeX/PDF/YAML）。

### R6: 基础设施升级 — Mathlib PR 级 sorry 的工程路线（强制，硬性规则）

**本节是硬性规则。违反 = 浪费 token，用户有权终止会话。**

**触发条件（自动，不需用户指令）**：
- agent 在**同一 sorry** 上 stuck ≥ 3 轮（包含跨会话的累计，查 `sorry_backlog.yaml` 的 `stuck_rounds` 字段）
- 或 agent 返回 "needs ~N lines infrastructure" / "not in Mathlib" 类结论
- 一旦触发，**禁止**再派 agent 做理论分析，**必须**执行以下 4 步

**执行流程（每步必须执行，不可跳过，不可合并）**：

**Step 1: Web 搜索（主会话执行，不委托给 agent）**
```
WebSearch "Lean 4 Mathlib <缺失概念> proof 2025 2026"
WebSearch "<定理名> formalization Lean Isabelle Coq"
WebSearch "arXiv <定理名> short proof elementary"
```
- 检查 Mathlib 最新版本是否已有（agent 的索引可能过时）
- 检查 Isabelle AFP / Coq MathComp 有无可参考路线
- 检查数学文献中最短的纯分析证明

**Step 2: WebFetch 获取具体 API / 证明步骤**
- Mathlib API 文档: `leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/...`
- arXiv 论文 HTML 版本: `arxiv.org/html/<id>`
- 提取: 所需 API **精确名称**、函数签名、依赖关系

**Step 3: 制定工程路线（写入文件）**
- 分解为独立子引理（每个 ≤ 50 行，可独立 build）
- 确定依赖 DAG（哪些可以并行）
- 估计总行数
- 写入 `sorry_backlog.yaml` 的 `engineering_route` 字段
- **输出 1 行摘要到屏幕**："R6 路线: N 个子引理, ~M 行, 依赖: A→B→C"

**Step 4: 立即实施（不等用户确认，不再分析）**
- 按 DAG 叶节点 → 根节点顺序实现
- 每个子引理: 写代码 → `lake build` → commit
- 子引理 stuck → sorry 暂留 + 继续下一个（不停下来分析）
- 所有子引理完成后组装主定理

**反模式（禁止）**：
- ❌ "需要 ~200 行基础设施" 然后停下来等用户
- ❌ 再派 agent 做 "分析可行性" / "探索替代路线"
- ❌ 写 design request 文档然后等待反馈
- ❌ 在同一个 sorry 上做第 4+ 轮理论分析

**正确模式**：
- ✅ 第 3 轮 stuck → 立即 WebSearch → 找到 Mathlib API → 制定路线 → 写代码
- ✅ 30 分钟内从 "stuck" 到 "开始写第一个子引理"

详细执行/升级条件见各 prove 命令的 Phase 0.5 和 `theme/prove_playbook.md` §3。

---

## Mathlib / StatLib 搜索策略（省 token 三级法）— 强制执行，硬性规则

**跳过本节任何步骤 = 违规。subagent prompt 中必须包含本节的检查清单。**
**subagent 返回结果中如果没有"已查 mathlib_full_type_index.tsv"的证据，主会话必须自己补查。**

**本节是硬性规则，所有证明流程（`/prove`、`/prove-deep`、subagent）必须遵循。**
**违反本节 = 浪费 token + 搜索结果不可靠，用户有权拒绝。**

搜索 Mathlib 或 StatLib API 时按以下顺序，**逐级升级**，不要跳级：

### 第零级：路线 key_api + 证明知识库 — 匹配到则跳过后续
- **如果 Phase 0.5 路线搜索获得了 key_api** → 按列表定向查签名，跳过全文读取
- **如果** `theme/proof_knowledge.yaml` 的 L3/L2 已匹配 → 同上
- key_api 中的名字按来源查签名：
  - **StatLean API** → `grep -i '<name>' theme/statlean_api_index.tsv`（614 条，毫秒级）
  - **Mathlib API** → `grep -i '<name>' theme/mathlib_full_type_index.tsv`（51K 条，毫秒级）
- 仅当路线和知识库均未覆盖当前 goal 时才进入第一级

### 第一级：查静态索引（~8.5K token）— 知识库未匹配时执行
- 读 `theme/mathlib_api_index.md`（~650+ 条，按 namespace 分 section）
- `grep -i '<keyword>' theme/statlean_api_index.tsv`（614 条 StatLean 自建 API）
- `grep -i '<keyword>' theme/mathlib_full_type_index.tsv`（51K 条全量 Mathlib 索引）
- 同时读 `Statlean/Verified.lean` 获取已入库模块列表

### 第二级：`#check` / `exact?`（精确但慢）
- 已知名字查签名：`echo '#check @ProbabilityTheory.foo' | lake env lean --stdin`
- 不知道名字但知道目标类型：写 `exact?` 或 `apply?`（~30-60 秒）
- 适用场景：索引没有、但怀疑 Mathlib 有

### 第三级：grep Mathlib 源码（最后手段）
- 只在前两级都失败时才用
- **使用前必须注明**："索引无此条目，第二级 #check 也未找到，升级到 grep"
- 限定目录：`Mathlib/Probability/`、`Mathlib/MeasureTheory/`、`Mathlib/Analysis/`
- 用 `Grep` 工具搜关键词，不要全目录扫描

### 索引维护
- 生成脚本：`scripts/gen_mathlib_index.lean`
- 重新生成：`lake env lean scripts/gen_mathlib_index.lean > theme/mathlib_api_index.md`
- Mathlib 升级后重跑一次（~30 秒）

---

## Phase 0 工具链（强制）

### 攻击 sorry 前必查路线 + 知识库
- **Phase 0.5 路线搜索**：按 R1→R2→R3→R4→R5→R6 六级 fallback 获取证明路线
- **R6 触发（强制）**：同一 sorry stuck ≥ 3 轮 → 必须 WebSearch + WebFetch 获取工程路线后再继续
- 有路线 → 按路线 key_api 定向查签名，**跳过 mathlib_api_index.md 全文读取**
- 无路线 → 读 `theme/proof_knowledge.yaml` 按 trigger 匹配 goal 形态
  - **匹配到 L3/L2** → 优先使用已记录的 strategy/chain（一轮验证即可），**跳过 mathlib_api_index.md**
  - **未匹配** → 升级到 mathlib_api_index.md 搜索（三级法第一级）
- **给 subagent 的 prompt 必须包含**：Phase 0.5 路线搜索指令 + "先读 `theme/proof_knowledge.yaml` 查找匹配的 pattern，匹配到则跳过 mathlib_api_index"

### proof_knowledge.yaml 维护规则
- **自动入库**：证明成功后 agent 输出 `new_knowledge` YAML 块，由 `scripts/ingest_knowledge.py` 自动入库
- **入库标准**：L1 frequency≥2（脚本累计）、L2 chain≥2 API、L3 confidence≥3
- **去重**：trigger 关键词 Jaccard>0.8 视为同条目（更新 frequency/source）
- **anti-pattern 强制入库（硬性规则）**：
  - 发现 FALSE 声明 → **立即**写入 anti-pattern（`anti: true`），不等证明完成
  - 发现死路（同一策略 stuck ≥ 3 轮）→ **立即**写入 anti-pattern
  - anti-pattern 格式：`strategy: "DO NOT <路线>. <原因>. Must use <正确路线>."`
  - **教训**：Berry-Esseen 中 "+1/2 smoothing error" 被 10+ 轮 agent 反复发现，
    如果第 1 轮就入库为 anti-pattern，后续 agent 会直接跳过
- **Mathlib 升级后验证** — 版本升级后抽查 pattern 是否仍有效，删除失效条目

### 签名提取代替全文件读取（强制，硬性规则）

**禁止对 >200 行的文件直接 `Read` 超过 50 行。违反 = token 浪费。**

**强制流程**：
1. **第一次接触文件**：`python3 scripts/extract_signatures.py <file>`（~1 秒，输出声明索引 + sorry 位置）
2. **定位目标**：从索引中找到目标 lemma 的行号
3. **精确读取**：`Read <file> offset=<行号-10> limit=30`（只读目标 ±15 行）
4. **仅在以下情况 Read >50 行**：
   - 需要修改跨越多个 lemma 的证明结构
   - 需要理解 import 链（此时读前 30 行）
   - 已用 extract_signatures 确认无法从索引获取所需信息

**反模式（禁止）**：
- ❌ `Read <file> offset=0 limit=200`（盲读大文件开头）
- ❌ `Read <file> offset=N limit=100`（读 100 行"上下文"）
- ❌ 对同一文件多次 `Read` 不同区域拼凑理解（应用 extract_signatures 一次获取全局索引）
- ❌ 不带 offset/limit 的 `Read`（读整个文件）

**正确模式**：
- ✅ `python3 scripts/extract_signatures.py Statlean/Foo.lean` → 找到 `lemma bar` 在 L150
- ✅ `Read Statlean/Foo.lean offset=140 limit=25` → 只读目标引理
- ✅ `grep -n 'sorry$' Statlean/Foo.lean` → 直接定位 sorry 行号

**给 subagent 的 prompt 必须包含**：
```
文件读取规则: 先 `python3 scripts/extract_signatures.py <file>` 获取索引。
禁止 Read >50 行。只 Read 目标行号 ±15 行。
```

### API 命名坑速查表
- `theme/api_gotchas.tsv`：~12 条高频 API 命名错误（wrong_guess → correct_api）
- 用法：`grep -i '<name>' theme/api_gotchas.tsv`
- **build 报 `unknown identifier` / `unknown constant` 时必须先查此表**，再查 full_type_index
- 维护：发现新命名坑时追加行（TSV 格式：wrong_guess\tcorrect_api\tnote）

### Mathlib 离线索引查询
- `theme/mathlib_full_type_index.tsv`：51K 条声明名+类型，grep 毫秒级
- 与 `theme/mathlib_api_index.md` 配合使用：先查 api_index（有注释），再查 full_type_index（全量）
- 用法：`grep -i 'condexp' theme/mathlib_full_type_index.tsv`
- Mathlib 升级后重新生成：`lake env lean scripts/gen_full_type_index.lean > theme/mathlib_full_type_index.tsv`

### 增量编译 + Build 循环最小化（强制，硬性规则）

**禁止**在未做预验证的情况下直接 `lake build`。每次 build 前必须先做至少一种预验证。

**三级验证（按速度排序，优先用快的）**：

**Level 0: API 预查（0 秒，写代码前必做）**
```bash
# 在写 tactic 之前确认 API 存在 + 签名
echo '#check @API_Name' | lake env lean --stdin
# 或查索引
grep -i 'api_name' theme/mathlib_full_type_index.tsv
```
- **写任何 Mathlib API 调用之前**必须先 `#check` 确认名字和参数顺序
- 违反 = API 名猜错 → 白等一次 build（30-150 秒浪费）
- **给 subagent 的 prompt 必须包含**："每个 Mathlib API 使用前先 `#check` 验证签名"

**Level 1: temp file 原型（5 秒）**
```bash
cat > /tmp/test_lemma.lean << 'EOF'
import Mathlib
import Statlean.Fourier.JacksonKernel  -- 按需 import
-- 测试单个引理
example (T : ℝ) (hT : 0 < T) : ... := by
  exact?  -- 或 tactic 试验
EOF
lake env lean /tmp/test_lemma.lean
```
- 适用于：新引理的 tactic 探索、API 组合测试
- 比 snippet check 更灵活（可以 import 任意模块）
- **新引理的前 3 次 tactic 尝试应在 temp file 中完成**，确认方向正确后再写入目标文件

**Level 2: snippet check（10 秒）**
```bash
bash scripts/check_snippet.sh <file> <start_line> <end_line>
```
- 适用于：已有文件中修改单个 declaration
- 比 `lake build` 快 3-15x

**Level 3: 模块 build（30-150 秒）**
```bash
lake build Statlean.<Module>
```
- **仅在以下时机使用**：
  - Level 0-2 全部通过后的最终验证
  - import 链变更后
  - 提交 commit 前
- **比例要求**：Level 0-2 验证次数 ≥ 3 × Level 3 次数

**subagent build 循环上限**：
- 每个 subagent 的 `lake build` 次数不应超过 5 次
- 如果超过 5 次 build 仍有错误 → 停下来用 Level 0 (#check) 重新确认所有 API
- DPI 教训：80 次 lake build ≈ 3.5h 纯编译 = 42% 墙钟时间

---

## 效率规则

- **并行 subagent（强制，上限 3 个）**：`/prove-deep` 和多 sorry 攻击时，启动独立 agent 并行，**同时运行的 agent 不超过 3 个**
  - 不同模块的 sorry（如 Poincaré vs LSI vs BerryEsseen）→ 同时启动多个 Task agent
  - 同一定理的 sub-lemma 如果互不依赖 → 也可以并行
  - 仅当有数据依赖时才串行（如 A 的输出是 B 的输入）
  - **硬性上限 3 并发**：待攻击任务超过 3 个时，按优先级选前 3 个并行，剩余排队等空位
  - 纯研究/搜索型 agent → `model: haiku`；需要写代码的 agent → `model: sonnet` 或默认
- **同文件写互斥（强制）+ 缓解策略**：多个 agent 不得同时修改同一 .lean 文件
  - 同一文件的不同 sorry → **串行**（A 完成 → commit → B 在新文件状态上启动）
  - 不同文件的 sorry → 可并行
  - 违反此规则会导致 agent 在过时代码上浪费 token（DPI 教训：~220K token 浪费于文件冲突）
  - **缓解策略（减少同文件 sorry 的串行开销）**：
    1. **提前拆文件**：如果一个文件有 ≥ 3 个独立 sorry → 先拆成多个文件再并行攻击
    2. **worktree 隔离**：用 `Agent(isolation: "worktree")` 让 agent 在 git worktree 中工作，
       修改不冲突时自动合并，冲突时丢弃。适用于不同 sorry 修改文件的不同区域
    3. **temp file 预验证**：agent 在 `/tmp/test_<lemma>.lean` 中写完整证明，验证通过后
       主会话负责 paste 到目标文件。这样 agent 不直接修改目标文件，避免冲突
- **跨会话 agent 及时终止**：新会话开始后，检查旧 agent 的目标代码是否已变更
  - 若代码已被其他 agent 修改 → 不等待旧 agent，用新 agent 从当前文件状态续接
  - 旧 agent 返回后若结果与当前文件冲突 → 丢弃，不合并
- **subagent 用 haiku**：纯搜索、grep、读文件指定 `model: haiku`
- **增量编译（强制优先 snippet check）**：
  - tactic 试错阶段（单个 sorry 攻击）→ **必须用** `bash scripts/check_snippet.sh <file> <start> <end>`（~10s）
  - 全模块验证（子引理完成后）→ `lake build Statlean.<Module>`（~150s）
  - 全库验证（提交前）→ `lake build`
  - **比例要求**：snippet check ≥ 3x lake build 次数（违反 = 编译时间浪费）
  - DPI 教训：18 agent 累计 ~80 次 lake build ≈ 3.5h 纯编译，占墙钟 42%
- **grep 先于 read**：用 Grep 定位行号再 Read 指定范围，不盲读大文件
- **不重复搜索**：委派给 subagent 的搜索不要自己再做一遍
- **深度预算**：`/prove` 模式 3 轮发散即 triage；`/prove-deep` 模式不设轮数限制，可以运行数小时
- **上下文保护**：大量搜索结果放 subagent 消化，只返回结论到主会话
- **上下文满自动续接（强制）**：
  - 当检测到上下文接近容量限制时，**立即**执行以下保存动作，不要等到最后：
    1. 更新 `sorry_backlog.yaml`：所有已完成/新增 sorry 的状态变更
    2. 更新 `MEMORY.md`：新学到的 Mathlib patterns、已完成的证明
    3. Commit 所有已完成的工作（即使部分完成也 commit 已验证通过的部分）
  - 新会话开始时，用户只需发 `/prove-deep all-leaves` 或 `/prove-deep next`
  - Claude 会自动读取 `sorry_backlog.yaml` + `MEMORY.md` 恢复状态并继续
  - **不要在中间轮次停下来写总结报告** — 持续推进直到上下文真正用完
  - 用户可以用 `claude --continue` 在同一会话续接，或新会话中靠 backlog 恢复
- **subagent 实时落盘（强制）**：
  - subagent 证明过程中，每完成一个 sub-lemma 或发现关键 pattern，**立即写入目标 .lean 文件**（即使主定理还有 sorry）
  - 这样 subagent 上下文耗尽时，已完成的部分已经落盘，新 agent 可以从文件当前状态续接
  - 给 subagent 的 prompt 必须包含："每证完一个子引理立即写入 .lean 文件并 lake build 验证，不要攒到最后一起写"
- **subagent 返回后自动检查续派**：
  - subagent 返回后，主会话检查目标 sorry 是否已关闭（grep sorry 或 lake build）
  - 若未关闭且 subagent 有实质进展（文件已修改），立即派新 agent 续接，prompt 注明"从文件当前状态继续，前任已完成 X"
  - 若无进展（策略耗尽）且 stuck 轮数 < 3，记录到 sorry_backlog.yaml 并转攻下一个目标
  - **若 stuck ≥ 3 轮（强制升级 R6，硬性规则）**：
    1. **禁止**再派 agent 做理论分析（违反 = 浪费 token）
    2. **主会话亲自执行** WebSearch + WebFetch（不委托给 agent，因为 agent 会跳过）
    3. 制定子引理分解 + 依赖 DAG（写入 sorry_backlog.yaml）
    4. 按 DAG 逐个实现（每个子引理单独 agent，prompt 必须是"写代码"不是"分析"）
    5. 不等用户确认，立即实施
    6. **sorry_backlog.yaml 中记录 stuck_rounds 字段**，跨会话累计
- **基础设施增量入库（强制 — 证明过程中实时执行，不等主定理完成）**：
  证明过程中产生的内容分两类处理：

  **A. 零 sorry 基础设施**（自身无 sorry，且依赖链也无 sorry 的引理/定义）→ **立即入库**：
  1. **确定归属模块**：按数学对象确定属于哪个 `Statlean/` 子目录
     - 例：Gaussian 相关 → `Statlean/Gaussian/`，熵相关 → `Statlean/Entropy/`
     - 如果目标目录或文件不存在，**创建之**（Mathlib-style 命名 + module docstring）
  2. **放入正确文件**：已有对应主题文件 → 追加到合适 section
  3. **更新 import 链**：使用方添加 import，`Statlean.lean` 同步更新
  4. **验证**：`lake build Statlean.<Module>` 编译通过
  5. 如果整个文件零 sorry → 同时更新 `Verified.lean`
  6. **不要等**——每个子引理独立入库，不等主定理完成

  **B. 含 sorry 的定理**（自身有 sorry，或依赖链有 sorry）→ **同文件存放，等待攻击**：
  1. 放在同一数学对象文件中，用 `section` 与零 sorry 部分隔离
  2. 添加结构化 sorry 注释（blocker、proof sketch、estimated effort）
  3. 在 `sorry_backlog.yaml` 中注册，标明依赖关系和优先级
  4. 以后有资源时通过 `/prove-deep` 攻击

---

## 输出预算规则（强制）— 屏幕摘要 vs 文件存档

**根本原则**：屏幕上只放用户需要"扫一眼"的信息；所有详情写文件，告诉用户文件路径。

| 内容 | 屏幕输出 | 文件存档 |
|------|---------|---------|
| PROVE 报告 | `PROVE: <name> — sorry N→M \| closed: [names]`（1-3 行） | `reports/prove_report_<name>.md` |
| DAG PROVE 报告 | `DAG PROVE: Xmin \| sorry N→M`（3-5 行） | `reports/prove_deep_<target>.md` |
| 经验报告 | `经验报告已写入 reports/session_report.md`（1 行） | `reports/session_report.md` |
| 知识入库 | `入库 N 条 pattern`（1 行） | YAML + 脚本输出在 Bash 工具内 |
| 策略分析 | `Strategy: X via [API1, API2]`（1 行） | 写入对应报告文件 |
| build 错误 | 1 行摘要 + fix 动作 | build log 在 Bash 工具输出里 |

**预算上限**：
- `/prove` 单 sorry → 屏幕文本 ≤ 3K token
- `/prove-deep` 多 sorry → 屏幕文本 ≤ 5K token
- 超预算 → 极简模式：只输出 sorry 计数变化 + 文件路径
- `/prove-out` 演示模式豁免此限制
- 工具调用输出（Bash、Read、Grep 等）不计入预算

---

## 经验反馈闭环（强制）— 输出分流模式

**每次会话的实质性工作结束后**，执行以下流程：

### 流程

1. **完整报告写文件**（用 Write 工具写入 `reports/session_report.md`）：
```
## 本轮经验报告

### 已入库 proof_knowledge.yaml
- [L1/L2/L3] <trigger 摘要> — <正面/anti> — <来源 sorry/定理>

### 新发现的 Lean/Mathlib 模式（待用户确认入库）
- <编号>. <模式描述> — <发现场景>

### Pipeline / 工具链改进建议
- <建议描述> — <动机>

### 分类 / 路由规则建议
- <规则描述> — <触发的误分类案例>

### 踩坑记录（避免重复）
- <坑描述> — <解决方案>
```

2. **屏幕只输出 1 行摘要**：
```
经验报告已写入 reports/session_report.md（入库 N 条 pattern，K 条踩坑）
```

3. **proof_knowledge 入库（强制，不等用户确认）**：
   - 证明过程中发现的 L1/L2/L3 pattern（正面或 anti）→ 写入临时 YAML 文件后运行
     `python3 scripts/ingest_knowledge.py --input <file>` 标准入库（自动验证 + 去重）
   - `anti: true` 条目 = 负面经验（"不要走这条路"），与正面条目放在同一层级
   - 原来的「证明策略新 pattern」和「踩坑记录中的证明相关部分」**统一进 proof_knowledge**
4. **用户审阅** — 用户决定 Pipeline 改进、分类规则等是否值得固化
5. **用户指令固化** — 用户说「采纳 X」后，Claude 执行：
   - Pipeline 改进 → 更新对应 `theme/scripts/` 代码或 pipeline skill
   - 分类规则 → 更新 `theme/scripts/classify.py` 的 `_THEOREM_RULES` 或 ontology
   - 非证明类踩坑 → 写入 `memory/pitfalls.md`

### Memory 分层写入规则（强制）

Memory 目录：`~/.claude/projects/-home-gavin-statlean/memory/`

**MEMORY.md**（自动加载前 200 行）只放：
- 项目状态、文件结构、sorry 概要、关键 API、slash commands
- **Recently Learned Patterns** 区域：最近常用的 pattern（单行摘要，≤15 条）
- 超过 15 条时，把最旧的移入 `patterns.md`

**Topic 文件**（按需 Read 加载）：
| 文件 | 内容 |
|------|------|
| `patterns.md` | 全部编号 Lean/Mathlib 模式（按类别分组） |
| `pitfalls.md` | 踩坑记录 + 结构性 blocker |
| `completed.md` | 里程碑历史 |
| `convergence_patterns.md` | 收敛证明详细模式 |

**写入流程**：
1. 新 pattern → 先加到 `MEMORY.md` 的 "Recently Learned Patterns"（单行摘要）
2. 同时加到 `patterns.md` 的对应类别下（完整描述 + 来源）
3. 踩坑记录 → 加到 `pitfalls.md`
4. 里程碑 → 加到 `completed.md`
5. 新的专题（如某类证明的详细 pattern 积累 ≥5 条）→ 创建新 topic 文件，从 MEMORY.md 链接
6. **MEMORY.md 必须保持 <200 行** — 每次写入后检查行数，超出则精简或移入 topic 文件

### 什么算「实质性工作」（触发报告）

- 完成 ≥1 个定理的证明或形式化
- Pipeline 运行一轮完整流程（PDF → Gate）
- 攻击 sorry 有实质进展（减少 sorry 或发现新 blocker）
- 修复 ≥2 个编译错误的调试过程

### 什么不需要报告

- 纯问答、文件浏览、简单编辑
- 只跑了 `lake build` 确认编译通过
- 纯 git 操作（commit、push）
