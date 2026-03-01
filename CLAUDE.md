# Claude Code 项目配置

## 操作授权

本项目已预授权所有操作，包括：
- git 操作（commit、push、branch 等）
- 文件读写、创建、删除
- 脚本执行（make、python、bash 等）
- Lean 编译（lake build 等）

**无需逐次确认，直接执行。**

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

### 验收标准
- `lake build` 零错误
- sorry 数只减不增
- `lake build Statlean.Verified` 零 sorry 警告

---

## Mathlib / StatLib 搜索策略（省 token 三级法）— 强制执行

**本节是硬性规则，所有证明流程（`/prove`、`/prove-deep`、subagent）必须遵循。**
**违反本节 = 浪费 token + 搜索结果不可靠，用户有权拒绝。**

搜索 Mathlib 或 StatLib API 时按以下顺序，**逐级升级**，不要跳级：

### 第一级：查静态索引（0 token 成本）— 必须首先执行
- **每次**搜索前先读 `theme/mathlib_api_index.md`（~650+ 条，按 namespace 分 section）
- 同时读 `Statlean/Verified.lean` 获取已入库模块列表
- 覆盖范围：variance、MGF/CGF、charFun、Independence、IdentDistrib、condExp、condVar、Gaussian、MemLp、integral、Measure.map、exp bounds、convexity/Jensen、polynomial derivatives、IBP、Grönwall、tilted measures、Lp density、Topology/Metric、Compactness、StrongLaw/SLLN、Filter/ae
- **80% 的搜索在这一步就能解决**
- 索引路径是 `theme/mathlib_api_index.md`（不是 `mathlib_stats_index.md`）
- **给 subagent 的 prompt 必须包含**: "先读 `theme/mathlib_api_index.md` 查找相关 API，只有索引不够时才 grep Mathlib 源码"

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

## 效率规则

- **并行 subagent（强制，上限 3 个）**：`/prove-deep` 和多 sorry 攻击时，启动独立 agent 并行，**同时运行的 agent 不超过 3 个**
  - 不同模块的 sorry（如 Poincaré vs LSI vs BerryEsseen）→ 同时启动多个 Task agent
  - 同一定理的 sub-lemma 如果互不依赖 → 也可以并行
  - 仅当有数据依赖时才串行（如 A 的输出是 B 的输入）
  - **硬性上限 3 并发**：待攻击任务超过 3 个时，按优先级选前 3 个并行，剩余排队等空位
  - 纯研究/搜索型 agent → `model: haiku`；需要写代码的 agent → `model: sonnet` 或默认
- **subagent 用 haiku**：纯搜索、grep、读文件指定 `model: haiku`
- **增量编译**：`lake build Statlean.Gaussian.Poincare` 只编目标，不要每次全量 build
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
  - 若无进展（策略耗尽），记录到 sorry_backlog.yaml 并转攻下一个目标，不无限重试
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

## 经验反馈闭环（强制）

**每次会话结束前**，输出一份「本轮经验报告」，格式如下：

### 报告格式

```
## 本轮经验报告

### 新发现的 Lean/Mathlib 模式
- <编号>. <模式描述> — <发现场景>

### Pipeline / 工具链改进建议
- <建议描述> — <动机>

### 分类 / 路由规则建议
- <规则描述> — <触发的误分类案例>

### 证明策略新 pattern
- <策略描述> — <适用场景>

### 踩坑记录（避免重复）
- <坑描述> — <解决方案>
```

### 流程

1. **Claude 输出报告** — 每次会话的实质性工作结束后，主动输出上述报告
2. **用户审阅** — 用户决定哪些值得固化
3. **用户指令固化** — 用户说「采纳 X」后，Claude 执行：
   - Lean/Mathlib 模式 → 写入 `MEMORY.md`（已有机制）
   - Pipeline 改进 → 更新对应 `theme/scripts/` 代码或 pipeline skill
   - 分类规则 → 更新 `theme/scripts/classify.py` 的 `_THEOREM_RULES` 或 ontology
   - 证明策略 → 更新 `theme/prove_playbook.md`
   - 踩坑记录 → 写入 `MEMORY.md` 或 CLAUDE.md 的「关键模式」小节
4. **不自动写入** — 报告本身只是建议，**未经用户确认不修改任何文件**

### 什么算「实质性工作」（触发报告）

- 完成 ≥1 个定理的证明或形式化
- Pipeline 运行一轮完整流程（PDF → Gate）
- 攻击 sorry 有实质进展（减少 sorry 或发现新 blocker）
- 修复 ≥2 个编译错误的调试过程

### 什么不需要报告

- 纯问答、文件浏览、简单编辑
- 只跑了 `lake build` 确认编译通过
- 纯 git 操作（commit、push）
