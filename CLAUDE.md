# Claude Code 项目配置

## 操作授权

本项目已预授权所有操作，包括：
- git 操作（commit、push、branch 等）
- 文件读写、创建、删除
- 脚本执行（make、python、bash 等）
- Lean 编译（lake build 等）

**无需逐次确认，直接执行。**

---

## 模块组织原则

### 按数学对象组织，不按证明项目
- 文件路径反映数学对象：`Gaussian/Poincare.lean`，不是 `Concentration/GaussianPoincare.lean`
- 一个数学对象的所有内容（定义、已证定理、sorry gap）放同一文件，用 section 隔离
- 定理名必须语义化：`frechet_mean_existence_transfer`，不是 `proposition_008_proposition_9`

### Proved/Sorry 分离（大模块）
- 当一个定理的证明产生 ≥3 个可复用子引理时，拆分为 `FooProved.lean`（零 sorry）+ `Foo.lean`（含 sorry 的主定理）
- `Statlean/Verified.lean` 是零 sorry 入口点，只 import 完全无 sorry 的模块
- 拆分后必须检查 Verified 链是否被 sorry 污染
- 小模块（≤2 个辅助引理）保持单文件，用 section 隔离

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

## 证明策略

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

## Mathlib 搜索策略（省 token 三级法）

搜索 Mathlib API 时按以下顺序，**逐级升级**，不要跳级：

### 第一级：查静态索引（0 token 成本）
- 先读 `theme/mathlib_api_index.md`（~650+ 条，按 namespace 分 section）
- 覆盖范围：variance、MGF/CGF、charFun、Independence、IdentDistrib、condExp、condVar、Gaussian、MemLp、integral、Measure.map、exp bounds、convexity/Jensen、polynomial derivatives、IBP、Grönwall、tilted measures、Lp density、**Topology/Metric**、**Compactness**、**StrongLaw/SLLN**、**Filter/ae**
- **80% 的搜索在这一步就能解决**
- 索引路径是 `theme/mathlib_api_index.md`（不是 `mathlib_stats_index.md`）

### 第二级：`#check` / `exact?`（精确但慢）
- 已知名字查签名：`echo '#check @ProbabilityTheory.foo' | lake env lean --stdin`
- 不知道名字但知道目标类型：写 `exact?` 或 `apply?`（~30-60 秒）
- 适用场景：索引没有、但怀疑 Mathlib 有

### 第三级：grep Mathlib 源码（最后手段）
- 只在前两级都失败时才用
- 限定目录：`Mathlib/Probability/`、`Mathlib/MeasureTheory/`、`Mathlib/Analysis/`
- 用 `Grep` 工具搜关键词，不要全目录扫描

### 索引维护
- 生成脚本：`scripts/gen_mathlib_index.lean`
- 重新生成：`lake env lean scripts/gen_mathlib_index.lean > theme/mathlib_api_index.md`
- Mathlib 升级后重跑一次（~30 秒）

---

## 效率规则

- **并行 subagent**：独立搜索/研究任务用 Task 并发，不串行
- **subagent 用 haiku**：纯搜索、grep、读文件指定 `model: haiku`
- **增量编译**：`lake build Statlean.Gaussian.Poincare` 只编目标，不要每次全量 build
- **grep 先于 read**：用 Grep 定位行号再 Read 指定范围，不盲读大文件
- **不重复搜索**：委派给 subagent 的搜索不要自己再做一遍
- **深度预算**：`/prove` 模式 3 轮发散即 triage；`/prove-deep` 模式不设轮数限制，可以运行数小时
- **上下文保护**：大量搜索结果放 subagent 消化，只返回结论到主会话
- **基础设施优先入库**：证明过程中产生的可复用定义和引理，即使主定理仍 sorry，也必须拆分入 `Statlean/` 并注册到 `Verified.lean`
