# StatLean 项目骨架搭建方案

## 目标
搭建一个基于 Mathlib 的 Lean 4 项目，目标是最大程度自动化统计定理的形式化。
项目支持三层自动化架构：**Tactic 层** → **Template 层** → **LLM Agent 层**。

---

## Step 1: 初始化 Lake 项目

```bash
cd /home/gavin/statlean
lake +leanprover-community/mathlib4:lean-toolchain init statlean math
```

自动生成：
- `lean-toolchain`（匹配 Mathlib 要求的 v4.28.0-rc1）
- `lakefile.toml`（含 Mathlib 依赖声明）
- `StatLean/Basic.lean`（入口文件）

---

## Step 2: 下载 Mathlib 预编译缓存

```bash
lake update        # 拉取依赖清单
lake exe cache get # 下载预编译 .olean（不下的话从源码编译要几个小时）
```

---

## Step 3: 创建目录结构

```
StatLean/
├── Basic.lean                  # 公共 import 和工具函数
│
├── Concentration/              # 浓度不等式
│   ├── Basic.lean              # 公共定义（sub-Gaussian 等扩展）
│   ├── EfronStein.lean         # Efron-Stein 不等式
│   ├── GaussianPoincare.lean   # Gaussian Poincaré 不等式
│   ├── LogSobolev.lean         # Gaussian Log-Sobolev 不等式
│   ├── GaussianLipschitz.lean  # Gaussian Lipschitz 浓度
│   └── Bernstein.lean          # Bernstein 不等式
│
├── EmpiricalProcess/           # 经验过程理论
│   ├── Basic.lean              # 覆盖数、度量熵的核心定义
│   ├── CoveringNumber.lean     # 覆盖数性质与计算
│   ├── Chaining.lean           # 链方法（dyadic chaining）
│   ├── Dudley.lean             # Dudley 熵积分定理
│   ├── Rademacher.lean         # Rademacher 复杂度
│   └── Symmetrization.lean     # 对称化论证
│
├── Regression/                 # 回归框架
│   ├── Basic.lean              # RegressionModel 结构体
│   ├── LeastSquares.lean       # 最小二乘估计
│   └── Linear.lean             # 线性回归收敛率
│
├── Tactic/                     # 【第一层】自动化 tactic
│   ├── MeasurabilityAuto.lean  # 自动证明可测性 side goals
│   ├── IntegrabilityAuto.lean  # 自动证明可积性 side goals
│   ├── IntegralBridge.lean     # lintegral ↔ integral 自动转换
│   └── StatAuto.lean           # 统一入口 meta tactic
│
└── Template/                   # 【第二层】定理模板框架
    ├── ConcentrationIneq.lean  # 浓度不等式通用模板
    └── TailBound.lean          # 尾概率界通用模板
```

> 第三层（LLM Agent）在 `scripts/` 目录下，后续搭建。

---

## Step 4: lakefile.toml 配置

Lake 只需声明一个 `lean_lib`（`StatLean`），会自动递归扫描子目录中的所有 `.lean` 文件：

```toml
[package]
name = "statlean"

[[require]]
name = "mathlib"
scope = "leanprover-community"

[[lean_lib]]
name = "StatLean"
```

---

## Step 5: 创建各模块 stub 文件

每个 `.lean` 文件包含：
- 正确的 Mathlib import
- 模块说明注释
- 关键定义的 `sorry` 占位（后续逐步替换为真实证明）

示例 — `StatLean/Concentration/Basic.lean`：

```lean
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Bochner

/-! # Concentration Inequalities — Basic Definitions

Common definitions and utilities used across concentration inequality proofs.
Extends Mathlib's sub-Gaussian infrastructure with additional characterizations.
-/

namespace StatLean.Concentration

end StatLean.Concentration
```

---

## Step 6: 验证构建

```bash
lake build
```

确认：
- 所有 stub 文件能正确 import Mathlib 模块
- 编译无错误通过
- `sorry` 仅出现在占位处

---

## Step 7: 初始化 Git

```bash
git init
git add .
git commit -m "Initial project skeleton: StatLean with Mathlib dependency"
```

---

## Mathlib 覆盖情况参考

| 需要的功能 | Mathlib 有？ | 说明 |
|-----------|-------------|------|
| 测度论基础 | ✅ | σ-代数、Borel、Lebesgue/Bochner 积分 |
| L^p 空间 | ✅ | `MeasureTheory.Lp` |
| 概率测度 | ✅ | `IsProbabilityMeasure` |
| 条件期望 | ✅ | `condexp` |
| 独立性 | ✅ | `ProbabilityTheory.iIndepFun` |
| Sub-Gaussian (MGF) | ✅ | `HasSubgaussianMGF` |
| Hoeffding / Azuma | ✅ | 基本版本 |
| 大数强律 | ✅ | Etemadi 证明 |
| 鞅论 | ✅ | 停时、Doob 收敛 |
| **覆盖数** | ❌ | 需自建 |
| **Dudley 积分** | ❌ | 需自建 |
| **Gaussian LSI** | ❌ | 需自建 |
| **Efron-Stein** | ❌ | 需自建 |
| **Bernstein 不等式** | ❌ | 需自建 |
| **Rademacher 复杂度** | ❌ | 需自建 |
| **中心极限定理** | ❌ | Mathlib 尚无 |
| **统计推断** | ❌ | MLE、假设检验等全部需自建 |

---

## 三层自动化架构概览

```
┌─────────────────────────────────────────────┐
│  Layer 3: LLM Agent                         │
│  自然语言定理 → Lean 骨架 → 人修关键步骤      │
├─────────────────────────────────────────────┤
│  Layer 2: Template                          │
│  浓度不等式/尾界/大数律等通用 schema           │
├─────────────────────────────────────────────┤
│  Layer 1: Tactic                            │
│  measurability_auto / integrability_auto /   │
│  integral_bridge / stat_auto                │
├─────────────────────────────────────────────┤
│  Foundation: Mathlib + 自建基础设施            │
│  测度论 / 概率 / 覆盖数 / Gaussian 分析       │
└─────────────────────────────────────────────┘
```
