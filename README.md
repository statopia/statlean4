# StatLean — Lean 4 形式化统计学库

用 Lean 4 + Mathlib 形式化数理统计的核心定理，涵盖估计理论、充分性、极限定理、集中不等式、回归分析、Gaussian 分析等。

**当前规模**：55 个 Lean 文件 · ~27,000 行 · ~900+ 个声明 · 52 个零 sorry 模块 · **2 个 sorry 待证**

> **想参与贡献？请阅读 [INSTRUCTION.md](INSTRUCTION.md)**

---

## 已完成定理（零 sorry，机器可验证）

### 极限定理（Shao Ch.1 全覆盖）

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
| 收敛蕴含（a.s.→概率 / 概率→子列a.s. / 完全→a.s.） | `LimitTheorems/Convergence.lean` | |
| Borel-Cantelli 引理（第一 + 第二） | `LimitTheorems/Convergence.lean` | |
| Kolmogorov 零一律 | `LimitTheorems/Convergence.lean` | Shao Thm 1.1 |
| Helly 选择定理 | `LimitTheorems/Convergence.lean` | |
| Portmanteau 定理（弱收敛等价条件） | `LimitTheorems/Convergence.lean` | |
| Lyapunov → Lindeberg 条件 | `LimitTheorems/Convergence.lean` | after Shao Thm 1.6 |
| Pólya 定理（连续极限 CDF ⟹ 一致收敛） | `LimitTheorems/Convergence.lean` | |
| Glivenko-Cantelli（经验 CDF 一致收敛） | `LimitTheorems/Convergence.lean` | |
| Kolmogorov 极大不等式 | `LimitTheorems/Convergence.lean` | |
| 多元 CLT（Cramér-Wold + 1D CLT） | `LimitTheorems/Convergence.lean` | |
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
| Bayes 估计 + 后验风险 | `Estimator/Bayes.lean` |
| 稳健估计（影响函数、崩溃点） | `Estimator/Robust.lean` |

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
| Gaussian Poincaré 不等式 | `Gaussian/Poincare.lean` |
| **Ornstein-Uhlenbeck 半群** (Mehler 公式) | `Gaussian/OrnsteinUhlenbeck.lean` |
| OU 不变性（∫P_t f dγ = ∫f dγ） | `Gaussian/OrnsteinUhlenbeck.lean` |
| OU 空间交换（(P_t f)' = e⁻ᵗ P_t(f')） | `Gaussian/OrnsteinUhlenbeck.lean` |
| OU 收敛（P_t f → E[f]） | `Gaussian/OrnsteinUhlenbeck.lean` |
| OU 正性（P_t g > 0 a.e.） | `Gaussian/OrnsteinUhlenbeck.lean` |
| Gaussian Dirichlet form（∫Lφ·ψ dγ = -∫φ'ψ' dγ） | `Gaussian/OrnsteinUhlenbeck.lean` |
| 积分 Cauchy-Schwarz（(∫h)²/(∫k) ≤ ∫h²/k） | `Gaussian/OrnsteinUhlenbeck.lean` |
| **1D Gaussian Log-Sobolev 不等式**（Bakry-Emery, C²） | `Gaussian/OrnsteinUhlenbeck.lean` |
| **1D Gaussian LSI（一般 W^{1,2} 版本）** | `Entropy/LogSobolev.lean` |
| **n 维 Gaussian LSI（张量化）** | `Entropy/LogSobolev.lean` |
| 熵耗散（d/dt Ent(P_t g) = -I(P_t g)） | `Gaussian/OrnsteinUhlenbeck.lean` |
| Fisher 信息收缩（I(P_t g) ≤ e⁻²ᵗ I(g)） | `Gaussian/OrnsteinUhlenbeck.lean` |
| ANOVA 方差分解 | `Variance/ANOVA.lean` |
| Efron-Stein 不等式 | `Variance/EfronStein.lean` |
| 熵非负性（Jensen）+ 条件熵非负 | `Entropy/Basic.lean` |
| **数据处理不等式 (DPI)**（条件熵单调性） | `Entropy/LogSobolev.lean` |
| 熵凸性（混合熵 ≤ 混合的熵） | `Entropy/LogSobolev.lean` |
| Log-sum 不等式（连续版） | `Entropy/LogSobolev.lean` |
| 熵子可加性（链式规则 + DPI） | `Entropy/LogSobolev.lean` |

### 假设检验

| 定理 | 文件 |
|------|------|
| Neyman-Pearson 引理 | `Testing/Basic.lean` |
| Karlin-Rubin（单调似然比 → UMP） | `Testing/Basic.lean` |

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
| 收敛模式（完全收敛、矩收敛、全变差收敛、弱收敛） | `LimitTheorems/Convergence.lean` |
| 决策理论（损失函数、风险、容许、Minimax、Bayes） | `Estimator/Basic.lean` |
| 覆盖数 + Dudley 积分 | `EmpiricalProcess/` |
| SPD Log-Cholesky Fréchet 均值 | `SPD/` |

---

## 已完成：Gaussian Log-Sobolev 不等式（1D + n 维张量化）✅

完整形式化 **Gaussian Log-Sobolev 不等式**，从 Bakry-Emery 到 n 维张量化，**零 sorry**（~5650 行）：

$$\text{Ent}_{\gamma^n}(f^2) \leq 2 \sum_{i=1}^n \int (\partial_i f)^2 \, d\gamma^n$$

### 证明架构（8 层逼近链 + OU 半群核心）

```
gaussian_lsi_normalized_from_ou ✅  Ent(f²) ≤ 2∫(f')² (C², bounded, ae-pos)  [OU 半群]
  └─ lsi_of_bounded_C2_ae_pos  ✅  thin wrapper around OU theorem
     └─ lsi_of_bounded_C2      ✅  ε-正则化 h=√(f²+ε)/√(1+ε) + DCT 极限
        └─ lsi_of_bounded_C1   ✅  OU 平滑 C¹→C² (Stein repr + Leibniz)
           └─ lsi_approximation_from_bounded  ✅  空间截断 + DCT
              └─ gaussian_lsi_normalized_of_integrable  ✅  组装
                 └─ gaussian_lsi_1d_ibp_core  ✅  by_cases + vacuous exfalso
                    └─ gaussian_lsi_1d_core   ✅  SatisfiesLSI stdGaussian 2
tensorization_lsi_core          ✅  n 维 LSI（熵子可加性 + 1D LSI per slice）
gaussian_log_sobolev            ✅  最终 n 维定理
```

### OU 半群基础设施（零 sorry，~3400 行）

```
ouSemigroup_zero               ✅  P_0 = id
integral_ouSemigroup           ✅  ∫ P_t f dγ = ∫ f dγ
ouSemigroup_hasDerivAt         ✅  (P_t f)' = e⁻ᵗ P_t(f')
ouSemigroup_tendsto            ✅  P_t f(x) → E[f]
ouSemigroup_pos_ae             ✅  P_t g > 0 a.e. for t > 0
ouSemigroup_stein_repr         ✅  P_t f' = (1/b)∫f(ax+by)·y dγ(y)
ouSemigroup_hasSecondDeriv     ✅  P_t f is C² for C¹ input
ouSemigroup_cameron_martin     ✅  Cameron-Martin tilt representation
entropy_dissipation            ✅  d/dt Ent(P_t g) = -I(P_t g)
fisherInfo_ouSemigroup_le      ✅  I(P_t g) ≤ e⁻²ᵗ I(g)
gaussian_lsi_normalized_from_ou ✅  Ent(f²) ≤ 2∫(f')² (C² version)
```

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

---

## CLT 证明链（零 sorry，完整形式化）

```
iid CLT (Shao Thm 1.4):
  charfun_normalized_sum_bound    ← charfun Taylor + 三角阵列界
      ↓
  levy_continuity                 ← Lévy 连续性定理
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
  isTight_of_charFun_tendsto_inner  ← 多元紧性（ONB 逐坐标紧性 + Parseval）
      ↓
  cramer_wold_charFun               ← 多元 Lévy 连续性
      ↓
  cramer_wold_iff                   ← μₙ →ᵈ μ₀ ⟺ ∀c, ⟨c,·⟩♯μₙ →ᵈ ⟨c,·⟩♯μ₀
```

---

## 项目结构

```
Statlean/
├── Gaussian/           # 标准高斯、Stein、Hermite、Poincaré、Ornstein-Uhlenbeck (5 files)
├── Variance/           # Rao-Blackwell、ANOVA、Efron-Stein (3 files)
├── Entropy/            # 熵定义、Log-Sobolev (2 files)
├── SubGaussian/        # Herbst 论证、Lipschitz 集中 (2 files)
├── CharFun/            # 特征函数 Taylor 链 (1 file)
├── LimitTheorems/      # CLT、Lindeberg-Feller、Lévy、Cramér-Wold、Berry-Esseen、
│                       # USLLN、Slutsky、Delta Method、Scheffé、收敛模式 (12 files)
├── Sufficiency/        # 因子分解、Basu、最小充分、Lehmann-Scheffé (4 files)
├── Information/        # Fisher 信息、Cramér-Rao (2 files)
├── Estimator/          # MSE 分解、MLE 不变性、UMVUE、渐近、Bayes、稳健 (6 files)
├── ExpFamily/          # 指数族 MLE + NatExpFamily (1 file)
├── Testing/            # 假设检验（UMP、Neyman-Pearson、Karlin-Rubin） (1 file)
├── Confidence/         # 置信集、枢轴量 (1 file)
├── Moments/            # 矩、偏度、峰度、协方差 (2 files)
├── Statistic/          # ParametricFamily、样本统计 (2 files)
├── EmpiricalProcess/   # 覆盖数、Dudley 积分 (2 files)
├── Regression/         # 最小二乘、Gauss-Markov、可估性 (5 files)
├── SPD/                # Log-Cholesky Fréchet 均值 (3 files)
├── Distribution/       # t 分布 (1 file)
└── Verified.lean       # 零 sorry 模块索引
```

---

## Sorry 缺口（2 个）

| 模块 | Sorry | 简述 | Blocker |
|------|-------|------|---------|
| BerryEsseen | 1 | Lévy CDF 反演界 | Stieltjes inversion (~100 行 Fourier) |
| Herbst | 1 | hasSubgaussianMGF of Lipschitz | 需要 LSI + Grönwall |

```
依赖 DAG:
  BerryEsseen (1 sorry)              ── 独立
  OrnsteinUhlenbeck (0 sorry) ✅ ──→ LogSobolev (0 sorry) ✅
                                   └─→ Herbst (1 sorry，需要 LSI + Grönwall)
```

完整清单 → [`sorry_backlog.yaml`](theme/input/sorry_backlog.yaml)

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
