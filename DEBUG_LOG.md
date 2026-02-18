# DEBUG_LOG（按 Step 追加）

## Step 1-2：检查基础依赖 / 安装 Lean 工具链

- 命令：
```bash
which lean && lean --version
which elan && elan --version
which lake && lake --version
```

- 终端输出：
```
/home/gavin/.elan/bin/lean
Lean (version 4.27.0, x86_64-unknown-linux-gnu, commit db93fe1..., Release)
/home/gavin/.elan/bin/elan
/home/gavin/.elan/bin/lake
```

- 解释：
  - 这一步在做什么：确认 WSL 里已有 elan / lean / lake
  - 成功标志是什么：三条命令都有路径和版本号输出
  - 我现在看到的现象说明什么：环境已就绪，不需要重新安装
  - 下一步要做什么：创建项目

---

## Step 3：创建 Lean + Mathlib 项目

- 命令：
```bash
cd /home/gavin/statlean
lake +leanprover-community/mathlib4:lean-toolchain init statlean math
```

- 终端输出（关键部分）：
```
info: downloading https://releases.lean-lang.org/lean4/v4.28.0-rc1/lean-4.28.0-rc1-linux.tar.zst
info: installing /home/gavin/.elan/toolchains/leanprover--lean4---v4.28.0-rc1
info: statlean: no previous manifest, creating one from scratch
info: leanprover-community/mathlib: cloning https://github.com/leanprover-community/mathlib4
info: leanprover-community/mathlib: checking out revision '5352afc...'
...（克隆 8 个依赖库：plausible, LeanSearchClient, importGraph, proofwidgets, aesop, Qq, batteries, Cli）...
info: mathlib: running post-update hooks
✔ [23/23] Built cache:exe
Fetching ProofWidgets cloud release... done!
```

- 解释：
  - 这一步在做什么：用 `math` 模板创建带 Mathlib 依赖的 Lean 项目
  - `+leanprover-community/mathlib4:lean-toolchain` 让 elan 自动切换到 Mathlib 需要的 Lean 版本（v4.28.0-rc1）
  - 成功标志：目录下出现 `lakefile.toml`、`lean-toolchain`、`Statlean/`、`Statlean.lean`
  - 我现在看到的现象说明什么：项目创建成功，所有依赖已克隆

---

## Step 4：下载 Mathlib 缓存

- 命令：
```bash
# math 模板在 init 时自动执行了 lake update + lake exe cache get
# 无需手动执行
```

- 终端输出（关键部分）：
```
Attempting to download 7873 file(s) from leanprover-community/mathlib4 cache
Downloaded: 7873 file(s) [attempted 7873/7873 = 100%]
```

- 解释：
  - 这一步在做什么：下载预编译的 .olean 缓存文件，避免从源码编译 Mathlib（否则要数小时）
  - 成功标志：7873 个文件全部下载完成
  - 下一步要做什么：第一次构建

---

## Step 5：第一次构建（空项目）

- 命令：
```bash
lake build
```

- 终端输出：
```
✔ [2/4] Built Statlean.Basic (130ms)
✔ [3/4] Built Statlean (133ms)
Build completed successfully (4 jobs).
```

- 解释：
  - 这一步在做什么：编译项目自身的文件（Mathlib 已有缓存，不需重编）
  - 成功标志：`Build completed successfully`，无 error
  - 下一步要做什么：添加定理 skeleton 文件

---

## Step 7：创建 Rao-Blackwell MSE skeleton 文件

- 文件路径：`Statlean/RaoBlackwell_MSE.lean`

- 内容：
```lean
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}

theorem rb_mse_skeleton
    (G : MeasurableSpace Ω) (hG : G ≤ m₀)
    (Y : Ω → ℝ) (θ : ℝ)
    [IsProbabilityMeasure μ]
    (hY : Integrable Y μ) :
    ∫ ω, (μ[Y|G] ω - θ) ^ 2 ∂μ
      ≤
    ∫ ω, (Y ω - θ) ^ 2 ∂μ := by
  sorry
```

- 解释：
  - PRD 原始代码用了 `ProbabilitySpace Ω`，但 Mathlib 中不存在此类型类
  - 修正为 `[IsProbabilityMeasure μ]`，这是 Mathlib 实际使用的 API
  - PRD 原始代码用了 `MemLp Y 2`，这里改为 `Integrable Y μ`（条件期望只需 L¹ 可积）
  - `μ[Y|G]` 是 Mathlib 中条件期望 `condExp G μ Y` 的记号

- 与 PRD 原始代码的差异记录：
  - `[ProbabilitySpace Ω]` → `[IsProbabilityMeasure μ]`（Mathlib 没有 ProbabilitySpace 类）
  - `(hY : MemLp Y 2)` → `(hY : Integrable Y μ)`（条件期望需要 L¹ 可积性）
  - `condexp G Y ω` → `μ[Y|G] ω`（使用 Mathlib 记号）
  - `∂(ℙ : Measure Ω)` → `∂μ`（使用显式测度变量）
  - `import Mathlib.MeasureTheory.Integral.Bochner` → `...Bochner.Basic`（v4.28 拆分了模块）

---

## Step 8：添加 import 到入口文件

- 文件：`Statlean.lean`
- 修改：添加 `import Statlean.RaoBlackwell_MSE`

- 解释：
  - 这一步在做什么：让主入口文件引入定理文件，使其参与编译
  - import 规则：`import <库名>.<文件相对路径（去掉.lean，目录用点号）>`

---

## Step 9：构建并观察报错/警告

- 命令：
```bash
lake build
```

- 第一次尝试 — 失败：
```
error: no such file or directory (error code: 2)
  file: .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner.lean
error: Statlean/RaoBlackwell_MSE.lean: bad import 'Mathlib.MeasureTheory.Integral.Bochner'
```

- 失败原因：Mathlib v4.28 将 `Bochner.lean` 拆分为 `Bochner/Basic.lean` 等子文件
- 修复：将 import 改为 `Mathlib.MeasureTheory.Integral.Bochner.Basic`

- 第二次尝试 — 成功：
```
⚠ [2558/2560] Built Statlean.RaoBlackwell_MSE (1.3s)
warning: Statlean/RaoBlackwell_MSE.lean:20:8: declaration uses `sorry`
✔ [2559/2560] Built Statlean (1.2s)
Build completed successfully (2560 jobs).
```

- 解释：
  - Build 通过（情况 A）
  - 有一个 warning：`declaration uses sorry`（第 20 行第 8 列）
  - 这说明 Lean 成功编译了定理的**声明**（类型检查通过），但证明体是 `sorry`（占位）
  - 这正是 MVP 成功标准要求的结果

---

## Step 10：VS Code 中读取 Goal

- 操作：在 VS Code 中打开 `Statlean/RaoBlackwell_MSE.lean`，光标放到 `sorry` 行
- 预期在 Lean Infoview 中看到的 Goal：

```
Ω : Type u_1
m₀ : MeasurableSpace Ω
μ : MeasureTheory.Measure Ω
G : MeasurableSpace Ω
hG : G ≤ m₀
Y : Ω → ℝ
θ : ℝ
inst✝ : MeasureTheory.IsProbabilityMeasure μ
hY : MeasureTheory.Integrable Y μ
⊢ ∫ (ω : Ω), (MeasureTheory.condExp G μ Y ω - θ) ^ 2 ∂μ
    ≤ ∫ (ω : Ω), (Y ω - θ) ^ 2 ∂μ
```

- 你应该看到什么：
  - `⊢` 后面是要证明的目标（条件期望的 MSE ≤ 原始 MSE）
  - 上面列出的是当前可用的假设（G、hG、Y、θ 等）
  - `sorry` 用黄色波浪线标记

---

## 延伸任务：消灭 `sorry` — 完整证明 Rao-Blackwell MSE 不等式

### 定理变更

原始 skeleton 的假设 `Integrable Y μ` (L¹) 改为 `MemLp Y 2 μ` (L²)。
原因：方差分解需要 `E[Y²] < ∞`，即 L² 可积性。原始 L¹ 条件下，两侧的积分可能都是无穷。

### 证明策略

**偏差-方差分解法**（3 步）：

1. **全方差定律** → `Var[E[Y|G]] ≤ Var[Y]`
   - `integral_condVar_add_variance_condExp`: `E[Var[Y|G]] + Var[E[Y|G]] = Var[Y]`
   - `condExp_nonneg` + `integral_nonneg_of_ae`: `E[Var[Y|G]] ≥ 0`
   - 相减得 `Var[E[Y|G]] ≤ Var[Y]`

2. **偏差-方差分解** → `E[(X-c)²] = Var[X] + (E[X]-c)²`
   - `variance_eq_sub`: `Var[X] = E[X²] - E[X]²`
   - `variance_sub_const`: `Var[X-c] = Var[X]`
   - 代数变换得到恒等式

3. **Tower property** → 偏差项相等
   - `integral_condExp`: `E[E[Y|G]] = E[Y]`
   - 因此 `(E[E[Y|G]] - θ)² = (E[Y] - θ)²`
   - 结合 Step 1: `Var[E[Y|G]] + (E[Y]-θ)² ≤ Var[Y] + (E[Y]-θ)²` ✓

### 迭代过程（4 轮）

**第 1 轮** — 手动展开二项式平方的积分
- 尝试用 `integral_add`, `integral_sub`, `integral_const_mul` 展开 `∫(X-c)²`
- 失败：`integral_const` 返回 `μ.real univ • c` 格式，`rw [measure_univ]` 模式不匹配
- 失败：`ring` 无法识别 `X ω ^ 2` 和 `(X ^ 2) x` 是同一个东西（Pi vs lambda）

**第 2 轮** — 改用 `variance_eq_sub` 间接推导
- 用 `variance_eq_sub (hX.sub (memLp_const c))` 获得 `Var[X-c] = E[(X-c)²] - (E[X-c])²`
- 用 `variance_sub_const` 获得 `Var[X-c] = Var[X]`
- 用 `integral_sub` + `integral_const` + `simp [Measure.real]` 计算 `E[X-c] = E[X] - c`
- 失败：`linarith` 无法统一 `∫ ((fun ω ↦ X ω - c) ^ 2) x ∂μ` 与 `∫ (X ω - c) ^ 2 ∂μ`

**第 3 轮** — 添加 `simp only [Pi.pow_apply]` 规范化
- 在 `h1 := variance_eq_sub hXc` 后添加 `simp only [Pi.pow_apply] at h1`
- 这将 `((fun ω ↦ X ω - c) ^ 2) x` 化简为 `(X x - c) ^ 2`
- 构建成功！但有 lint 警告：`Pi.sub_apply` 参数未使用

**第 4 轮** — 清理 lint 警告
- 移除多余的 `Pi.sub_apply`
- **零 warning、零 error、零 sorry** ✓

### 使用的关键 Mathlib 引理

| 引理 | 来源文件 | 作用 |
|------|---------|------|
| `variance_eq_sub` | `Probability/Moments/Variance.lean` | Var[X] = E[X²] - E[X]² |
| `variance_sub_const` | 同上 | Var[X-c] = Var[X] |
| `integral_condVar_add_variance_condExp` | `Probability/CondVar.lean` | 全方差定律 |
| `condExp_nonneg` | `ConditionalExpectation/Basic.lean` | 条件期望保持非负性 |
| `integral_condExp` | 同上 | Tower property: E[E[Y\|G]] = E[Y] |
| `MemLp.condExp` | 同上 | L² 可积性对条件期望封闭 |
| `integral_nonneg_of_ae` | `Integral/Bochner/Basic.lean` | a.e. 非负 → 积分非负 |
| `ae_of_all` | `OuterMeasure/AE.lean` | 逐点条件 → a.e. 条件 |
| `integral_sub` | `Integral/Bochner/Basic.lean` | 积分线性性 |
| `Pi.pow_apply` | `Mathlib/Algebra/Group/Pi/Lemmas.lean` | `(f ^ n) x = f x ^ n` |

### 遇到的 Lean 典型坑

1. **Pi 函数 vs Lambda**：`X - fun _ => c` 和 `fun ω => X ω - c` 定义上相等，但 `ring`/`linarith` 不做定义展开。需要 `simp only [Pi.pow_apply]` 手动规范化。

2. **`integral_const` 的格式**：不返回 `c` 而是返回 `μ.real univ • c`。对概率测度需要额外 `simp [Measure.real]` 化简。

3. **`Eventually.of_forall` 重命名**：在 measure theory 上下文中应使用 `ae_of_all μ`。

---

## 最终总结

### 完成的全部成果
1. WSL 环境中 elan/lean/lake 完整可用 ✓
2. 创建了带 Mathlib 依赖的 Lean 4 项目 `statlean` ✓
3. 下载了 Mathlib 预编译缓存（7873 个文件）✓
4. 创建了 Rao-Blackwell MSE 定理 ✓
5. **完成了完整的形式化证明，零 sorry** ✓
6. 证明过程中发现并记录了 3 个 Lean 典型坑 ✓

### 最终构建结果
```
✔ [2592/2592] Built Statlean.RaoBlackwell_MSE (1.4s)
Build completed successfully (2592 jobs).
```
零 error、零 warning、零 sorry。

### 下一阶段要做什么
- 搭建自动化 tactic 基础设施（MeasurabilityAuto、IntegrabilityAuto 等）
- 创建更多统计定理的模板框架
- 将 Pi/Lambda 规范化等常见操作封装为自动化 tactic
