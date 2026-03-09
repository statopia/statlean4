# Mathematical Statistics 形式化估算报告

> 基于 Jun Shao《Mathematical Statistics》(2nd ed, 607 页, 7 章)
> 更新日期: 2026-03-04
> 项目: statlean (Lean 4 + Mathlib)

---

## 一、书籍范围

| 章 | 主题 | 节数 | 正式声明数 |
|---|------|------|-----------|
| Ch1 | Probability Theory (基础) | 17 | ~44 (Thm/Prop/Lem/Cor) |
| Ch2 | Sufficiency & Completeness | 6 | ~11 |
| Ch3 | UMVUE, Cramér-Rao, U-statistics, Linear Models | 17 | ~28 |
| Ch4 | Bayes, Minimax, Equivariance, Asymptotic Efficiency | 20 | ~32 |
| Ch5 | Nonparametric Estimation (Functionals, L/M/R-estimators, Bootstrap) | 20 | ~30 |
| Ch6 | Hypothesis Testing (NP, UMP, UMPU, LR/Wald/Rao) | 8 | ~25 |
| Ch7 | Confidence Sets | ~4 | ~17 |
| **合计** | | **92 节** | **~187 个正式声明** |

每"节"（如 1.15）可能包含多个定理、推论、引理。以下索引按节编号。

### 完整定理索引

**Chapter 1 — Probability Theory**
- 1.1 Fatou's lemma, DCT, MCT
- 1.2 Change of variables
- 1.3 Fubini's theorem
- 1.4 Radon-Nikodym theorem
- 1.5 Cochran's theorem
- 1.6 Uniqueness of distribution with a given ch.f.
- 1.7 Existence of conditional distributions
- 1.8 Convergence and uniform integrability
- 1.9 Weak convergence, Lévy-Cramér continuity theorem, Cramér-Wold device
- 1.10 Continuous mapping theorem
- 1.11 Slutsky's theorem
- 1.12 Delta-method
- 1.13 WLLN and SLLN
- 1.14 WLLN and SLLN (extensions)
- 1.15 Lindeberg's CLT (iid CLT + Lindeberg-Feller CLT)
- 1.16 Edgeworth expansion
- 1.17 Cornish-Fisher expansion

**Chapter 2 — Sufficiency & Completeness**
- 2.1 Properties of exponential families
- 2.2 Factorization theorem
- 2.3 Minimal sufficiency
- 2.4 Basu's theorem
- 2.5 Rao-Blackwell theorem
- 2.6 Asymptotic MSE

**Chapter 3 — UMVUE & Linear Models**
- 3.1 Lehmann-Scheffé theorem
- 3.2 Conditions for UMVUE
- 3.3 Cramér-Rao lower bound
- 3.4 Hoeffding's theorem (U-statistic variance bound)
- 3.5 Asymptotic distribution of a U-statistic
- 3.6 Estimability in linear models
- 3.7 UMVUE's in normal linear models
- 3.8 Distributions of UMVUE's in normal linear models
- 3.9 Gauss-Markov theorem
- 3.10 Conditions for BLUE's in linear models
- 3.11 Consistency of LSE's
- 3.12 Asymptotic normality of LSE's
- 3.13 Watson and Royall theorem
- 3.14 UMVUE's under stratified simple random sampling
- 3.15 Horvitz-Thompson estimator
- 3.16 Asymptotic distribution of a V-statistic
- 3.17 Asymptotic normality of weighted LSE's

**Chapter 4 — Decision Theory & Asymptotic Efficiency**
- 4.1 Bayes formula
- 4.2 Admissibility of Bayes rules
- 4.3 Admissibility of a limit of Bayes rules
- 4.4 Consistency of MCMC
- 4.5 MRIE for location
- 4.6 Pitman estimator
- 4.7 Properties of invariant rules
- 4.8 MRIE for scale
- 4.9 MRIE for location (extension)
- 4.10 MRIE in normal linear models
- 4.11 Minimaxity of Bayes estimators
- 4.12 Minimaxity of limits of Bayes estimators
- 4.13 Estimators with constant risks
- 4.14 Admissibility in exponential families
- 4.15 Risk of James-Stein estimators
- 4.16 Asymptotic information inequality
- 4.17 Asymptotic efficiency of RLE's in i.i.d. cases
- 4.18 Asymptotic efficiency of RLE's in GLM's
- 4.19 Asymptotic efficiency of one-step MLE's
- 4.20 Asymptotic efficiency of Bayes estimators

**Chapter 5 — Nonparametric Estimation**
- 5.1 Asymptotic properties of empirical c.d.f.'s
- 5.2 Asymptotic properties of empirical c.d.f.'s (extensions)
- 5.3 Nonparametric MLE
- 5.4 Asymptotic normality of MELE's
- 5.5 Asymptotic properties of differentiable functionals
- 5.6 Differentiability of L-functionals
- 5.7 Differentiability of M-functionals
- 5.8 Differentiability of functionals for R-estimators
- 5.9 A probability bound for sample quantiles
- 5.10 Asymptotic normality of sample quantiles
- 5.11 Bahadur's representation
- 5.12 Asymptotic normality of L-estimators in linear models
- 5.13 Asymptotic normality of GEE's in i.i.d. cases
- 5.14 Asymptotic normality of GEE's in non-i.i.d. cases
- 5.15 Consistency of substitution variance estimators
- 5.16 Substitution variance estimators for GEE's
- 5.17 Consistency of jackknife variance estimators for functions of sample means
- 5.18 Consistency of jackknife variance estimators for LSE's
- 5.19 Consistency of jackknife variance estimators for GEE's
- 5.20 Consistency of bootstrap estimators for functionals

**Chapter 6 — Hypothesis Testing**
- 6.1 Neyman-Pearson lemma
- 6.2 UMP tests in families having monotone likelihood ratio
- 6.3 UMP tests for two-sided hypotheses in exponential families
- 6.4 UMPU tests in exponential families
- 6.5 Asymptotic distribution of LR tests
- 6.6 Asymptotic distribution of Wald's and Rao's score tests
- 6.7 Asymptotic tests in GLM's
- 6.8 χ²-test convergence

**Chapter 7 — Confidence Sets**
- 7.1-7.3 Confidence set construction methods
- 7.4 Asymptotic comparison of confidence sets in terms of volume

---

## 二、当前项目覆盖率（2026-03-04 更新）

**总规模**：44 files · ~14,100 lines · ~480 declarations · 37 零 sorry 模块 · **6 sorry 待证**

### Chapter 1 — Probability Theory（10/17 节覆盖，~59%）

| 节 | 对应 Shao 定理 | 状态 | 文件 |
|---|----------------|------|------|
| 1.1-1.4 Fatou/DCT/Fubini/RN | Thm 1.1-1.3 | Mathlib 已有 | — |
| 1.5 Cochran | | ❌ 未开始 | — |
| 1.6 CharFun 唯一性 | Thm 1.6 | Mathlib 已有 (`Measure.ext_of_charFun`) | — |
| 1.7 条件分布 | | 部分 Mathlib | — |
| 1.8 收敛模式 + 一致可积 | | **✅ zero sorry** (收敛模式) | `LimitTheorems/Convergence.lean` |
| 1.9 Lévy-Cramér 连续性 | Thm 1.9 | **✅ zero sorry** | `LimitTheorems/Levy.lean` |
| 1.9 Cramér-Wold device | Cor | **1 sorry** (tightness) | `LimitTheorems/CramerWold.lean` |
| 1.10 连续映射 (CMT) | Thm 1.10 | **✅ zero sorry** | `LimitTheorems/DeltaMethod.lean` |
| 1.11 Slutsky | Thm 1.10 | **✅ zero sorry** | `LimitTheorems/Slutsky.lean` |
| 1.12 Delta Method + √n | Thm 1.12, Cor 1.1 | **✅ zero sorry** | `LimitTheorems/DeltaMethod.lean` |
| 1.13-1.14 SLLN | | **✅ zero sorry** (USLLN) | `LimitTheorems/USLLN.lean` |
| 1.5 Scheffé | Thm 1.5 | **✅ zero sorry** | `LimitTheorems/Scheffe.lean` |
| 1.15 iid CLT | Thm 1.4 | **✅ zero sorry** | `LimitTheorems/CLT.lean` |
| 1.15 Lindeberg-Feller CLT | Thm 1.6 | **✅ zero sorry** | `LimitTheorems/LindebergFeller.lean` |
| Berry-Esseen (书外补充) | Thm 1.7 | **1 sorry** (Stieltjes 反演) | `LimitTheorems/BerryEsseen.lean` |
| CharFun Taylor 链 (书外) | | **✅ zero sorry** | `CharFun/Taylor.lean` |
| 1.16-1.17 Edgeworth/Cornish-Fisher | | ❌ 未开始 | — |

### Chapter 2 — Sufficiency & Completeness（5/6 节覆盖，~83%）

| 节 | 状态 | 文件 |
|---|------|------|
| 2.1 指数族性质 + MLE + NatExpFamily | **✅ zero sorry** | `ExpFamily/Basic.lean` |
| 2.2 因子分解（双向） | **✅ zero sorry** | `Sufficiency/Factorization.lean` |
| 2.3 最小充分性（3 判据） | **✅ zero sorry** | `Sufficiency/MinimalSufficiency.lean` |
| 2.4 Basu 定理 | **✅ zero sorry** | `Sufficiency/Basu.lean` |
| 2.5 Rao-Blackwell (12 变体) | **✅ zero sorry** | `Variance/RaoBlackwell.lean` |
| 2.6 渐近 MSE (Bayes) | ❌ 未开始 | — |

### Chapter 3 — UMVUE, Cramér-Rao, Linear Models（7/17 节覆盖，~41%）

| 节 | 状态 | 文件 |
|---|------|------|
| 3.1 Lehmann-Scheffé UMVUE | **✅ zero sorry** | `Sufficiency/LehmannScheffe.lean` |
| 3.2 UMVUE 条件 | ✅ 隐含于 Lehmann-Scheffé | — |
| 3.3 Cramér-Rao 下界 | **✅ zero sorry** | `Information/CramerRao.lean` |
| 3.4 Hoeffding U-stat 方差界 | ❌ 未开始 | — |
| 3.5 U-stat 渐近分布 | ❌ 未开始 | — |
| 3.6 线性模型可估性 | **✅ zero sorry** | `Regression/Estimability.lean` |
| 3.7-3.8 正态线性模型 UMVUE | ❌ 未开始 | — |
| 3.9 Gauss-Markov | **✅ zero sorry** | `Regression/GaussMarkov.lean` |
| 3.10 BLUE 条件 | **✅ zero sorry** | `Regression/Estimability.lean` |
| 3.11-3.12 LSE 相合性 + 渐近正态 | ❌ 未开始 | — |
| 3.13-3.17 (高级) | ❌ 未开始 | — |

**新增**: 渐近正态性定义 + ARE + CLT→渐近桥梁 (`Estimator/Asymptotic.lean` — zero sorry), 可估性 + BLUE=UMVUE (`Regression/Estimability.lean` — zero sorry)

### 书外补充（集中不等式 + 高斯分析）

| 模块 | 状态 | sorry |
|------|------|-------|
| Gaussian Poincaré (1D proved, nD condVar) | 部分 | 在 LogSobolev 中 |
| Log-Sobolev (LSI + entropy infrastructure) | 部分 | 3 sorry |
| Efron-Stein 不等式 | **✅ zero sorry** | 0 |
| Sub-Gaussian / Herbst | 部分 | 1 sorry (blocked by LSI) |
| ANOVA 方差分解 | **✅ zero sorry** | 0 |
| Hermite 正交 + IBP + Parseval | **✅ zero sorry** | 0 |
| 覆盖数 + Dudley 积分 | **✅ zero sorry** | 0 |
| SPD Log-Cholesky Fréchet 均值 | **✅ zero sorry** | 0 |

### 汇总

| 指标 | 数值 |
|------|------|
| 书中 92 节覆盖 | **~27 个零 sorry**（~29%） |
| 187 个正式声明覆盖 | **~40 个零 sorry 定理**（~21%） |
| Phase 0（工具链） | **100% 完成** |
| Phase 1（Ch1 概率基础） | **~59% 完成** |
| Phase 2（Ch2 充分性） | **~83% 完成** |
| Phase 3（Ch3 UMVUE/CR/LM） | **~41% 完成** |
| Phase 4-7 | **0% 完成** |

---

## 三、Sorry 缺口（6 个）

| ID | 模块 | 定理 | 类型 | Blocker | 预计行 |
|----|------|------|------|---------|--------|
| P1 | BerryEsseen | `esseen_concentration_universal` | stuck | Fourier 反演桥接到 CDF/概率设置 | ~200 |
| P2 | LogSobolev | `gaussian_lsi_normalized_of_integrable` | stuck | Bakry-Emery Γ₂ + OU 半群 | ~300 |
| P3 | LogSobolev | `integrable_sq_mul_log_sq_of_memLp` | blocked | blocked by P2 | ~80 |
| P9 | Herbst | `hasSubgaussianMGF_centered_of_lipschitz` | blocked | blocked by P2 + P10 | ~60 |
| P10 | LogSobolev | `entropy_subadditivity_of_nonneg` (n≥2) | honest | 数据处理不等式 / Han 不等式 | ~80 |
| P13 | LogSobolev | `integrable_condEntropyAt` | blocked | blocked by P10 | ~20 |

**依赖 DAG**:
```
P1 (BerryEsseen, stuck) ← Fourier inversion
P2 (Gaussian LSI, stuck) ← Bakry-Emery
  → P3 (f²·log(f²) integrable) ← blocked by P2
  → P9 (Sub-Gaussian MGF) ← blocked by P2 + P10
P10 (entropy subadditivity n≥2, honest) ← data processing inequality
  → P13 (conditional entropy integrable) ← blocked by P10
  → P9 ← blocked by P2 + P10
```

全部 6 个 sorry 均为**深层数学 blocker**，无快速目标。下一可攻目标为 P10（~80 行纯数学）。

完整清单与依赖关系 → [`sorry_backlog.yaml`](input/sorry_backlog.yaml)

---

## 四、Token 估算

### 按难度分层

根据项目实际经验（Rao-Blackwell ~30M、Factorization ~80M、Lehmann-Scheffé ~60M、USLLN ~100M、Lévy+CLT+Lindeberg ~150M），每个定理的 token 消耗按难度分层：

| 难度 | 定理数 | 特征 | 单定理成本 | 小计 |
|------|--------|------|-----------|------|
| **Tier S**（极难） | ~8 | MLE 渐近正态 (4.16-4.19)、经验过程 (5.1-5.2)、GEE 渐近 (5.13-5.14)、Bootstrap 相合性 (5.20) | 200-500M | **1.6-4B** |
| **Tier A**（难） | ~20 | Neyman-Pearson、UMPU (6.4)、James-Stein (4.15)、U-statistic 渐近 (3.5)、Bahadur 表示 (5.11) | 60-200M | **1.2-4B** |
| **Tier B**（中等） | ~35 | Cramér-Wold、minimax (4.11-4.12)、UMP (6.2)、LR 检验 (6.5)、jackknife/bootstrap | 20-60M | **0.7-2.1B** |
| **Tier C**（易/Mathlib 已有） | ~30 | Cochran、Bayes formula、基本 Bayes、一致可积、Glivenko-Cantelli | 5-20M | **0.15-0.6B** |

**全书估算：3.5-11B tokens**（中位数 ~**7B tokens**）

### 换算成 Max 20x 周用量

Max 20x 的 opus 实际周预算，按重度 Claude Code prove-deep 使用估计约 **50-150M tokens/周**。取中位 ~100M/周：

| 指标 | 保守估计 | 中位估计 | 乐观估计 |
|------|---------|---------|---------|
| 总 token | 11B | 7B | 3.5B |
| 20x 周用量倍数 | **110 倍** | **70 倍** | **35 倍** |
| 等价全职时间 | ~2.2 年 | ~1.4 年 | ~8 个月 |

### Token 消耗构成分析（2026-03-04 实测更新）

```
证明搜索（试错循环）    ≈ 40%   ← tactic_patterns.yaml 减少了 ~5%
上下文重读（长文件反复读）≈ 15%   ← extract_signatures.py 减少了 ~5%
Mathlib API 发现         ≈ 10%   ← full_type_index.tsv 减少了 ~5%
类型错误调试              ≈ 12%
编译等待 + 增量编译       ≈  8%   ← check_snippet.sh 加速了单 decl 验证
代码生成（实际写代码）    ≈  8%
Agent 调度开销            ≈  7%
```

---

## 五、工具链状态（Phase 0 — 100% 完成）

| 工具 | 状态 | 效果 |
|------|------|------|
| `theme/mathlib_api_index.md`（650+ API 索引） | ✅ 已完成 | 80% 搜索命中 |
| `scripts/gen_mathlib_index.lean`（自动生成） | ✅ 已完成 | Mathlib 升级后一键重建 |
| `theme/mathlib_full_type_index.tsv`（51K 条全量索引） | ✅ 已完成 | grep 毫秒级查询 |
| `scripts/extract_signatures.py`（声明索引提取） | ✅ 已完成 | 大文件上下文节省 60-70% |
| `scripts/check_snippet.sh`（单 decl 增量编译） | ✅ 已完成 | 编译反馈 ×3-5 加速 |
| `theme/tactic_patterns.yaml`（58 条验证 pattern） | ✅ 已完成 | 减少 20-30% 试错循环 |
| `MEMORY.md`（66+ 条 Lean/Mathlib pattern） | ✅ 持续积累 | 跨会话经验复用 |
| 增量编译（`lake build Statlean.Module`） | ✅ 已成标准流程 | 避免全量 build |

**综合节省：实测 ~25-30% token（符合预期 20-40% 区间）。**

---

## 六、前期基础设施建设推荐（按优先级排序）

### Phase 1：Ch1 概率基础补全 — ✅ ~59% 完成

| 优先级 | 定理 | 状态 | 预计工作量 |
|--------|------|------|-----------|
| — | 1.10 CMT | **✅ zero sorry** | — |
| — | 1.11 Slutsky (add/mul/div) | **✅ zero sorry** | — |
| — | 1.12 Delta Method + √n | **✅ zero sorry** | — |
| — | 1.5 Scheffé | **✅ zero sorry** | — |
| — | 1.13-1.14 SLLN (USLLN) | **✅ zero sorry** | — |
| — | 1.9 Lévy-Cramér 连续性 | **✅ zero sorry** | — |
| — | 1.15 iid CLT | **✅ zero sorry** | — |
| — | 1.15 Lindeberg-Feller CLT | **✅ zero sorry** | — |
| — | Berry-Esseen (书外) | **1 sorry** (Stieltjes) | Tier S, ~200 行 |
| — | CharFun Taylor 链 (书外) | **✅ zero sorry** | — |
| P1 | **1.9 Cramér-Wold device** | **1 sorry** (tightness in FiniteDim) | `CramerWold.lean`, ~200 行 |
| P2 | **1.8 一致可积补全** | ❌ 未开始 | ~50 行 |
| — | 1.5 Cochran | ❌ 未开始 | Tier B, ~60 行 |
| — | 1.16-1.17 Edgeworth/Cornish-Fisher | ❌ 未开始 | Tier S |

### Phase 2：Ch2 充分性补全 — ✅ ~83% 完成

| 优先级 | 内容 | 状态 | 预计工作量 |
|--------|------|------|-----------|
| P3 | **指数族完备性 (Completeness)** | ❌ 未开始 | ~80 行，Ch6 前提 |
| — | 2.6 渐近 MSE (Bayes) | ❌ 未开始 | ~40 行 |

### Phase 3：Ch3 UMVUE/CR/LM 补全 — ✅ ~41% 完成

| 优先级 | 内容 | 状态 | 预计工作量 |
|--------|------|------|-----------|
| — | 3.1-3.3 Lehmann-Scheffé + Cramér-Rao | **✅ zero sorry** | — |
| — | 3.6 可估性 + 3.10 BLUE 条件 | **✅ zero sorry** | — |
| — | 3.9 Gauss-Markov | **✅ zero sorry** | — |
| — | 渐近正态性 + ARE | **✅ zero sorry** | — |
| P4 | **3.4 Hoeffding decomposition** | ❌ 未开始 | Tier B, ~100 行 |
| P5 | **3.5 U-stat 渐近分布** | ❌ 未开始 | Tier A, 需 CLT |
| — | 3.7-3.8 正态线性模型 UMVUE | ❌ 未开始 | Tier B |
| — | 3.11-3.12 LSE 相合性/渐近 | ❌ 未开始 | Tier B |
| — | 3.13-3.17 高级 | ❌ 未开始 | Tier A-S |

### Phase 4：决策论 + Bayes 基础

| 优先级 | 内容 | 复用度 | 难度 | 预计 token |
|--------|------|--------|------|-----------|
| P6 | Loss, Risk, Bayes risk 定义体系 | 高（Ch4 全用） | 易 | 15-25M |
| P7 | 4.1 Bayes formula + 4.2 Admissibility | 高 | 中 | 30-50M |
| P8 | 4.11-4.12 Minimax (Bayes estimator) | 中 | 中 | 40-60M |

### Phase 5：检验论

| 优先级 | 内容 | 复用度 | 难度 | 预计 token |
|--------|------|--------|------|-----------|
| P9 | 6.1 Neyman-Pearson Lemma | 极高 | 难 | 60-100M |
| P10 | 6.2 UMP (monotone likelihood ratio) | 高 | 中 | 40-60M |
| P11 | 6.4 UMPU in exponential families | 中 | 难 | 80-120M |

### Phase 6：渐近效率 + 非参（最难）

| 优先级 | 内容 | 复用度 | 难度 | 预计 token |
|--------|------|--------|------|-----------|
| P12 | 4.16 Asymptotic information inequality | 极高 | 极难 | 200-400M |
| P13 | 4.17-4.19 MLE 渐近效率 | 极高 | 极难 | 300-500M |
| P14 | 5.1-5.2 经验过程渐近 | 高 | 极难 | 200-400M |
| P15 | 5.5-5.7 可微统计泛函 | 中 | 难 | 100-200M |

---

## 七、修正后总估算

| 场景 | 总 token | 20x 周用量倍数 | 日历时间（每周满载） |
|------|---------|---------------|-------------------|
| 无工具改进 | ~7B | ~70 倍 | ~1.4 年 |
| 有工具改进（Phase 0 ✅ 已完成） | ~5B | ~50 倍 | ~1 年 |
| 只做核心 80%（跳过 Tier S） | ~2.5B | ~25 倍 | ~6 个月 |
| 只做 Phase 1-3（概率基础 + 充分性 + UMVUE/LM） | ~0.4B | ~4 倍 | ~4 周 |

---

## 八、优先形式化清单（推荐顺序）

按**复用度 × 可行性 / 难度**排序。已有基础设施越多、解锁下游越多的优先。

### Tier 1：下一批目标（近期，预计 2-4 周）

| # | 定理 | Shao 节 | 复用度 | 难度 | 行数 | 理由 |
|---|------|---------|--------|------|------|------|
| 1 | **Cramér-Wold device** | 1.9 | 极高 | 易 | ~30 | 已有 Lévy，直接用；解锁多维 CLT |
| 2 | **指数族完备性** | 2.1 | 极高 | 中 | ~80 | Ch6 UMPU 的关键前提 |
| 3 | **Hoeffding 分解** (U-stat 方差界) | 3.4 | 高 | 中 | ~100 | 核心估计论工具 |
| 4 | **Cochran 定理** | 1.5 | 高 | 中 | ~60 | χ²/F 检验的基础 |
| 5 | **一致可积补全** | 1.8 | 中 | 易 | ~50 | 收敛理论完备 |

### Tier 2：中期目标（4-8 周）

| # | 定理 | Shao 节 | 复用度 | 难度 | 行数 |
|---|------|---------|--------|------|------|
| 6 | U-stat 渐近分布 | 3.5 | 高 | 难 | ~200 |
| 7 | Loss/Risk/Bayes risk 定义 | 4.1 前置 | 极高 | 易 | ~60 |
| 8 | Neyman-Pearson lemma | 6.1 | 极高 | 难 | ~200 |
| 9 | Bayes formula + Admissibility | 4.1-4.2 | 高 | 中 | ~150 |
| 10 | UMP (monotone LR) | 6.2 | 高 | 中 | ~150 |

### Tier 3：远期目标（2-6 月）

| # | 定理 | Shao 节 | 复用度 | 难度 |
|---|------|---------|--------|------|
| 11 | UMPU in exponential families | 6.4 | 中 | 难 |
| 12 | Minimax (Bayes estimator) | 4.11-4.12 | 中 | 中 |
| 13 | 正态线性模型 UMVUE | 3.7-3.8 | 中 | 中 |
| 14 | LSE 渐近正态性 | 3.12 | 中 | 中 |
| 15 | LR/Wald/Rao 检验渐近 | 6.5-6.6 | 高 | 难 |

### Tier S：深层目标（需大量基础设施）

| # | 定理 | Shao 节 | Blocker |
|---|------|---------|---------|
| 16 | Asymptotic information inequality | 4.16 | 需 LAN theory |
| 17 | MLE 渐近效率 | 4.17-4.19 | 需 4.16 |
| 18 | 经验过程渐近 | 5.1-5.2 | 需 empirical process CLT |
| 19 | Bootstrap 相合性 | 5.20 | 需 5.1-5.2 |
| 20 | Edgeworth 展开 | 1.16 | 需 Fourier inversion |

---

## 附录：难度分级标准

- **Tier S（极难）**：Mathlib 缺根基性基础设施（如 Fourier inversion for distributions、LAN theory、empirical process CLT），需要从头建 200+ 行基础设施。单定理 200-500M tokens。
- **Tier A（难）**：Mathlib 有部分基础设施但有 gap，需要 5-15 个中间引理。单定理 60-200M tokens。
- **Tier B（中等）**：Mathlib API 基本够用，但组合方式非平凡，需要 instance resolution 调试。单定理 20-60M tokens。
- **Tier C（易）**：Mathlib 有直接 API 或 1-2 步组合即可。单定理 5-20M tokens。

## 附录：版本变更记录

| 日期 | 变更 |
|------|------|
| 2026-03-02 | 初始报告（40 files, 11.3K lines, 31 verified, 7 sorry） |
| 2026-03-04 | 更新：+Lévy, +CLT, +Lindeberg-Feller, +渐近估计, +可估性 BLUE/UMVUE。44 files, 14.1K lines, 37 verified, 6 sorry。Phase 0 工具链 100% 完成。 |
