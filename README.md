# StatLean — Lean 4 形式化统计库

用 Lean 4 + Mathlib 形式化统计的核心定理，涵盖估计理论、充分性、极限定理、集中不等式等。

**当前规模**：40 个 Lean 文件 · ~11,300 行 · ~400 个声明 · 31 个零 sorry 模块 · **7 个 sorry 待证**

> **想参与贡献？请阅读 [INSTRUCTION.md](INSTRUCTION.md)**

---

## 已完成定理（零 sorry，机器可验证）

### 估计理论

| 定理 | 文件 |
|------|------|
| Rao-Blackwell MSE 定理 | `Variance/RaoBlackwell.lean` |
| MSE = Bias² + Variance | `Estimator/Basic.lean` |
| Lehmann-Scheffé UMVUE 定理 | `Sufficiency/LehmannScheffe.lean` |
| Cramér-Rao 信息不等式 | `Information/CramerRao.lean` |
| Gauss-Markov 定理 (BLUE) | `Regression/GaussMarkov.lean` |
| 指数族 MLE 存在唯一性 | `ExpFamily/Basic.lean` |
| MLE 定义 + 不变性定理 | `Estimator/Basic.lean` |

### 充分性

| 定理 | 文件 |
|------|------|
| Fisher-Neyman 因子分解（双向） | `Sufficiency/Factorization.lean` |
| Basu 定理 | `Sufficiency/Basu.lean` |
| 最小充分统计量密度比判据 | `Sufficiency/MinimalSufficiency.lean` |
| 子族扩展判据 | `Sufficiency/MinimalSufficiency.lean` |

### 极限定理

| 定理 | 文件 |
|------|------|
| 均匀强大数律 (USLLN) | `LimitTheorems/USLLN.lean` |
| Slutsky 定理（加法 / 乘法 / 除法） | `LimitTheorems/Slutsky.lean` |
| 连续映射定理 (CMT) | `LimitTheorems/DeltaMethod.lean` |
| Delta 方法 + √n 推论 | `LimitTheorems/DeltaMethod.lean` |
| Scheffé 定理（密度 → L¹ 收敛） | `LimitTheorems/Scheffe.lean` |
| Berry-Esseen 定理（模 1 个分析引理） | `LimitTheorems/BerryEsseen.lean` |
| 特征函数 Taylor 链（charfun → exp decay） | `CharFun/Taylor.lean` |
| 收敛模式（a.s. / 概率 / Lp） | `LimitTheorems/Convergence.lean` |

### Gaussian 分析

| 定理 | 文件 |
|------|------|
| Hermite 正交性 + Parseval + IBP | `Gaussian/Hermite.lean` |
| Stein 恒等式 | `Gaussian/Stein.lean` |
| ANOVA 方差分解 | `Variance/ANOVA.lean` |
| Gaussian Poincaré 1D | `Gaussian/Poincare.lean` |

### 其他

| 定理 | 文件 |
|------|------|
| 覆盖数 + Dudley 积分 | `EmpiricalProcess/` |
| 最小二乘 + 主误差界 | `Regression/` |
| SPD Log-Cholesky Fréchet 均值 | `SPD/` |

---

## Berry-Esseen 证明链

Berry-Esseen 定理是本库中最深的证明链之一，当前 **13 个引理已证明，仅剩 1 个分析 sorry**：

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
esseen_concentration_universal    ← [sorry] Stieltjes 反演公式
    ↓
berry_esseen_theorem              ← |F_S(y) - Φ(y)| ≤ Cρ/(σ³√n)
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
├── LimitTheorems/      # USLLN、Berry-Esseen、CLT、Slutsky、Delta Method、
│                       # Scheffé、收敛模式 (7 files)
├── Sufficiency/        # 因子分解、Basu、最小充分、Lehmann-Scheffé (4 files)
├── Information/        # Fisher 信息、Cramér-Rao (2 files)
├── Estimator/          # MSE 分解、MLE 不变性 (1 file)
├── ExpFamily/          # 指数族 MLE + NatExpFamily 结构 (1 file)
├── Statistic/          # ParametricFamily、IsUnbiased (1 file)
├── EmpiricalProcess/   # 覆盖数、Dudley 积分 (2 files)
├── Regression/         # 最小二乘、主误差界、Gauss-Markov (4 files)
├── SPD/                # Log-Cholesky Fréchet 均值 (3 files)
├── Pipeline/           # Pipeline 生成的存根 (1 file)
└── Verified.lean       # 零 sorry 模块索引（31 个模块）
```

---

## Sorry 缺口（7 个）

| Blocker | 模块 | sorry 数 | 说明 |
|---------|------|---------|------|
| Stieltjes 反演公式 | BerryEsseen | 1 | Esseen 1945，需 Fourier 反演 |
| Gaussian 超收缩性 | Poincaré + LogSobolev | 1 + 2 | Nelson 1973，需 Hermite 乘积线性化 |
| Measure.pi Fubini | EfronStein + LogSobolev | 2 + 1 | Mathlib 缺 Bochner Fubini for Measure.pi |
| ← blocked by LSI | Herbst | 1 | blocked by gaussian_lsi_normalized |

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
