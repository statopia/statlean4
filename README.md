# StatLean — Lean 4 形式化统计库

用 Lean 4 + Mathlib 形式化统计的核心定理，目前已涵盖估计理论、充分性、极限定理、集中不等式、回归分析等。

**当前规模**：50 个 Lean 文件 · ~15,400 行 · ~600 个声明 · 44 个零 sorry 模块 · **6 个 sorry 待证（BerryEsseen 仅剩 1 个）**

> **想参与贡献？请阅读 [INSTRUCTION.md](INSTRUCTION.md)**

---

## 已完成定理（零 sorry，机器可验证）

### 极限定理（Shao Ch.1）

| 定理 | 文件 | 参考 |
|------|------|------|
| 中心极限定理 (iid CLT) | `LimitTheorems/CLT.lean` | Shao Thm 1.4 |
| Lindeberg-Feller CLT（三角阵列） | `LimitTheorems/LindebergFeller.lean` | Shao Thm 1.6 |
| Berry-Esseen 定理（模 Stieltjes 反演） | `LimitTheorems/BerryEsseen.lean` | Shao Thm 1.7 |
| Lévy 连续性定理（正+逆） | `LimitTheorems/Levy.lean` | Shao Thm 1.9 |
| Slutsky 定理（加法 / 乘法 / 除法） | `LimitTheorems/Slutsky.lean` | Shao Thm 1.10 |
| 连续映射定理 (CMT) | `LimitTheorems/DeltaMethod.lean` | |
| Delta 方法 + √n 推论 | `LimitTheorems/DeltaMethod.lean` | Shao Thm 1.12 |
| Cramér-Wold 装置（多元 Lévy + 投影 ⟺ 弱收敛） | `LimitTheorems/CramerWold.lean` | Shao Thm 1.9(iii) |
| Scheffé 定理（密度 → L¹ 收敛） | `LimitTheorems/Scheffe.lean` | Shao Thm 1.5 |
| 均匀强大数律 (USLLN) | `LimitTheorems/USLLN.lean` | |
| 收敛模式（a.s. / 概率 / Lp） | `LimitTheorems/Convergence.lean` | |
| 特征函数 Taylor 链（charfun → exp decay） | `CharFun/Taylor.lean` | |

### 估计理论

| 定理 | 文件 |
|------|------|
| Rao-Blackwell MSE 定理 | `Variance/RaoBlackwell.lean` |
| MSE = Bias² + Variance | `Estimator/Basic.lean` |
| Lehmann-Scheffé UMVUE 定理 | `Sufficiency/LehmannScheffe.lean` |
| UMVUE a.e. 唯一性（平行四边形恒等式） | `Estimator/UMVUE.lean` |
| Efficient ⇒ UMVUE | `Estimator/UMVUE.lean` |
| 指数族 UMVUE（完备充分 + Doob-Dynkin） | `Estimator/UMVUE.lean` |
| 完备充分下不可估性定理 | `Estimator/UMVUE.lean` |
| Cramér-Rao 信息不等式 | `Information/CramerRao.lean` |
| 指数族 MLE 存在唯一性 | `ExpFamily/Basic.lean` |
| MLE 定义 + 不变性定理 | `Estimator/Basic.lean` |
| 渐近正态性 + 渐近 MSE + ARE | `Estimator/Asymptotic.lean` |
| 线性模型可估性 + BLUE/UMVUE | `Regression/Estimability.lean` |

### 充分性

| 定理 | 文件 |
|------|------|
| Fisher-Neyman 因子分解（双向） | `Sufficiency/Factorization.lean` |
| Basu 定理 | `Sufficiency/Basu.lean` |
| 最小充分统计量密度比判据 | `Sufficiency/MinimalSufficiency.lean` |
| 子族扩展判据 | `Sufficiency/MinimalSufficiency.lean` |

### 回归分析

| 定理 | 文件 |
|------|------|
| Gauss-Markov 定理 (BLUE) | `Regression/GaussMarkov.lean` |
| 最小二乘 + 主误差界 | `Regression/MasterBound.lean` |
| 线性回归定义 + OLS | `Regression/Linear.lean` |
| 可估性 BLUE = UMVUE | `Regression/Estimability.lean` |

### Gaussian 分析 + 集中不等式

| 定理 | 文件 |
|------|------|
| Hermite 正交性 + Parseval + IBP | `Gaussian/Hermite.lean` |
| Stein 恒等式 | `Gaussian/Stein.lean` |
| ANOVA 方差分解 | `Variance/ANOVA.lean` |
| Gaussian Poincaré 1D | `Gaussian/Poincare.lean` |
| Efron-Stein 不等式 | `Variance/EfronStein.lean` |
| 熵非负性（Jensen） + 链式规则 | `Entropy/Basic.lean` + `Entropy/LogSobolev.lean` |

### 统计基础定义

| 定义 | 文件 |
|------|------|
| 假设检验（检验函数、功效、UMP、Neyman-Pearson） | `Testing/Basic.lean` |
| 置信集（覆盖概率、置信区间、枢轴量） | `Confidence/Basic.lean` |
| 样本统计（样本均值 / 方差、次序统计量、分位数、中位数） | `Statistic/Sample.lean` |
| 矩（k 阶矩 / 中心矩、偏度、峰度、绝对矩、截断矩、累量） | `Moments/Basic.lean` |
| Chebyshev 不等式 | `Moments/Basic.lean` |
| Var(X)=E[X²]-(EX)²、Cov(X,X)=Var(X) | `Moments/Basic.lean` |
| Cauchy-Schwarz (协方差)、\|ρ\|≤1、独立方差可加 | `Moments/Covariance.lean` |
| 收敛模式（完全收敛、矩收敛、全变差收敛） | `LimitTheorems/Convergence.lean` |
| 决策理论（损失函数、风险、容许、Minimax、Bayes） | `Estimator/Basic.lean` |

### 其他

| 定理 | 文件 |
|------|------|
| 覆盖数 + Dudley 积分 | `EmpiricalProcess/` |
| SPD Log-Cholesky Fréchet 均值 | `SPD/` |

---

## Berry-Esseen 证明链

Berry-Esseen 定理是本库中最深的证明链之一，当前 **18 个引理已证明，仅剩 1 个 sorry**：

```
charfun_taylor_third_moment       ← Taylor 展开 + 三阶矩界
    ↓
norm_charFun_le_one_sub           ← 单因子模界 |φ(s)| ≤ 1 - σ²s²/4
    ↓
norm_prod_sub_prod_le_sum_mul_pow ← 乘积望远镜 ‖∏z - ∏w‖ ≤ M^{n-1} · ∑‖z-w‖
    ↓
charfun_diff_exp_bound            ← 指数衰减界 ‖φ_S - φ_Φ‖ ≤ Cδ(|t|³+t⁴)e^{-t²/8}
    ↓
charfun_integral_bound            ← 积分界 ∫ ‖φ_S-φ_Φ‖/|t| ≤ Cδ
    ↓
abel_sinc_integral                ← ∫₀^∞ e^{-εt} sin(at)/t dt = arctan(a/ε)
    ↓
levy_cdf_diff_fourier_bound       ← [sorry] Lévy 反演 → CDF 界（~100 行 Fourier 分析）
    ↓
esseen_concentration_universal    ← Esseen 不等式 + Gauss 密度界
    ↓
berry_esseen_theorem              ← |F_S(y) - Φ(y)| ≤ Cρ/(σ³√n)
```

> **⚠️ 已知问题**：`esseen_concentration_universal` 的当前声明对重尾分布（无有限一阶矩）在数学上不正确——
> Bochner 积分对不可积被积函数返回 0，导致 RHS = C₂/T 不足以控制 LHS ≈ 1。
> 修复方案：添加可积性假设。下游调用 `esseen_charfun_integral_bound` 可从 Taylor 界提供此条件。

---

## CLT 证明链

iid CLT 和 Lindeberg-Feller CLT 已完整证明（零 sorry）：

```
iid CLT (Shao Thm 1.4):
  charfun_normalized_sum_bound    ← charfun Taylor + 三角阵列界
      ↓
  levy_continuity                 ← Lévy 连续性定理（含 Prokhorov + charFun 唯一性）
      ↓
  central_limit_theorem           ← 标准化和 ⟹ N(0,1)

Lindeberg-Feller CLT (Shao Thm 1.6):
  lindeberg_implies_max_var_tendsto  ← Lindeberg ⟹ Feller 条件
      ↓
  charfun_lindeberg_pointwise        ← charfun 逐点收敛到 Gaussian charfun
      ↓
  lindeberg_feller_clt               ← 三角阵列标准化行和 ⟹ N(0,1)

Cramér-Wold 装置 (Shao Thm 1.9(iii)):
  isTight_of_charFun_tendsto (1D)   ← 1D Lévy 紧性（Esseen 界 + DCT）
      ↓
  isTight_of_charFun_tendsto_inner  ← 多元紧性（ONB 逐坐标紧性 + Parseval 鸽巢）
      ↓
  cramer_wold_charFun               ← 多元 Lévy 连续性（Prokhorov + charFun 唯一性）
      ↓
  cramer_wold_iff                   ← μₙ →ᵈ μ₀ ⟺ ∀c, ⟨c,·⟩♯μₙ →ᵈ ⟨c,·⟩♯μ₀
```

---

## 项目结构

```
Statlean/
├── Gaussian/           # 标准高斯、Stein、Hermite、Poincaré (4 files)
├── Variance/           # Rao-Blackwell、ANOVA、Efron-Stein (3 files)
├── Entropy/            # 熵定义、Log-Sobolev (2 files)
├── SubGaussian/        # Herbst 论证、Lipschitz 集中 (2 files)
├── CharFun/            # 特征函数 Taylor 链 (1 file)
├── LimitTheorems/      # CLT、Lindeberg-Feller、Lévy、Cramér-Wold、Berry-Esseen、
│                       # USLLN、Slutsky、Delta Method、Scheffé、收敛模式 (10 files)
├── Sufficiency/        # 因子分解、Basu、最小充分、Lehmann-Scheffé (4 files)
├── Information/        # Fisher 信息、Cramér-Rao (2 files)
├── Estimator/          # MSE 分解、MLE 不变性、UMVUE 定理、渐近理论 (3 files)
├── ExpFamily/          # 指数族 MLE + NatExpFamily 结构 (1 file)
├── Testing/            # 假设检验（UMP、Neyman-Pearson） (1 file)
├── Confidence/         # 置信集、枢轴量 (1 file)
├── Moments/            # 矩、偏度、峰度 (1 file)
├── Statistic/          # ParametricFamily、IsUnbiased、样本统计 (2 files)
├── EmpiricalProcess/   # 覆盖数、Dudley 积分 (2 files)
├── Regression/         # 最小二乘、主误差界、Gauss-Markov、可估性 (5 files)
├── SPD/                # Log-Cholesky Fréchet 均值 (3 files)
├── Pipeline/           # Pipeline 生成的存根 (1 file)
└── Verified.lean       # 零 sorry 模块索引（44 个模块）
```

---

## Sorry 缺口（6 个，3 独立 blocker + 3 下游依赖）

| ID | Blocker | 模块 | 预估行数 | 状态 |
|----|---------|------|---------|------|
| P1 | **Lévy CDF 反演界** | BerryEsseen | ~100 | stuck — `abel_sinc_integral` 已证，需 Fubini + DCT + Gaussian 尾界；**当前声明对重尾分布有误**（需加可积性假设） |
| P2 | **Gaussian LSI** | LogSobolev | ~250 | stuck — 推荐路线：Two-point LSI + CLT transfer（95% 可行，Statlean 依赖全部就绪）|
| P10 | **熵子可加性 n≥2** | LogSobolev | ~120 | honest — Han 不等式，n=0/1 已证，需 telescoping + data processing，**无 Mathlib blocker** |
| P3 | f²·log(f²) 可积 | LogSobolev | ~80 | blocked by P2 |
| P13 | 条件熵可积 | LogSobolev | ~20 | blocked by P10 |
| P9 | Sub-Gaussian MGF | Herbst | ~60 | blocked by P2 + P10 |

```
依赖 DAG:
  P1 (Berry-Esseen) ── 独立
  P2 (Gaussian LSI) ─┬─→ P3 (f²log 可积)
                      └─→ P9 (Sub-Gaussian MGF) ←─┐
  P10 (熵子可加) ────┬─→ P13 (条件熵可积)          │
                      └────────────────────────────┘
```

完整清单与依赖关系 → [`sorry_backlog.yaml`](theme/input/sorry_backlog.yaml)

---

## 快速开始

```bash
git clone https://github.com/mockingbird-gan/statlean4.git && cd statlean4
curl https://elan-init.tracing.rs/elan-init.sh -sSf | sh   # 安装 elan（已有则跳过）
lake exe cache get                                           # 下载 Mathlib 缓存
lake build Statlean                                          # 编译全库（零错误）
lake build Statlean.Verified                                 # 验证零 sorry 模块
```

---

## 验收标准

```bash
lake build                       # 零错误
lake build Statlean.Verified     # 零 sorry 警告
```

sorry 数只减不增，每次 commit 保证 `lake build` 零错误。

---

## 文档索引

| 文档 | 说明 |
|------|------|
| **[INSTRUCTION.md](INSTRUCTION.md)** | **贡献指南** — 环境搭建、贡献方式、验收标准 |
| [theme/PIPELINE.md](theme/PIPELINE.md) | Pipeline 详解 — PDF → Lean 4 全流程 |
| [theme/formalize_playbook.md](theme/formalize_playbook.md) | 形式化操作手册 — 7 步 SOP |
| [theme/prove_playbook.md](theme/prove_playbook.md) | 证明操作手册 — 策略选择表、Mathlib 搜索法 |
| [theme/input/sorry_backlog.yaml](theme/input/sorry_backlog.yaml) | Sorry 清单 — 优先级、blocker、依赖关系 |
| [theme/mathlib_api_index.md](theme/mathlib_api_index.md) | Mathlib API 索引 — 650+ 条常用 API |
