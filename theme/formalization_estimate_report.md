# Mathematical Statistics 形式化估算报告

> 基于 Jun Shao《Mathematical Statistics》(~570 页, 7 章)
> 生成日期: 2026-03-02
> 项目: statlean (Lean 4 + Mathlib)

---

## 一、书籍范围

| 章 | 主题 | 定理数 | 定义数 |
|---|------|--------|--------|
| Ch1 | Probability Theory (基础) | 17 | ~15 |
| Ch2 | Sufficiency & Completeness | 6 | ~10 |
| Ch3 | UMVUE, Cramér-Rao, U-statistics, Linear Models | 17 | ~8 |
| Ch4 | Bayes, Minimax, Equivariance, Asymptotic Efficiency | 20 | ~12 |
| Ch5 | Nonparametric Estimation (Functionals, L/M/R-estimators, Bootstrap) | 20 | ~10 |
| Ch6 | Hypothesis Testing (NP, UMP, UMPU, LR/Wald/Rao) | 8 | ~8 |
| Ch7 | Confidence Sets | ~4 | ~5 |
| **合计** | | **~92 个定理** | **~68 个定义** |

总计 **~160 个正式数学声明**（定理 + 定义 + 推论 + 引理），加上书中大量非编号命题和例子。

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
- 1.15 Lindeberg's CLT
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

## 二、当前项目覆盖率（2026-03-02 更新）

**总规模**：40 files · ~11,300 lines · ~400 declarations · 31 零 sorry 模块 · **7 sorry 待证**

### Chapter 1 — Probability Theory（7/17 完成，~41%）

| 定理 | 状态 | 文件 |
|------|------|------|
| 1.1-1.4 Fatou/DCT/Fubini/RN | Mathlib 已有 | — |
| 1.10 Continuous Mapping | **✅ zero sorry** | `LimitTheorems/DeltaMethod.lean` |
| 1.11 Slutsky (add/mul/div) | **✅ zero sorry** | `LimitTheorems/Slutsky.lean` |
| 1.12 Delta Method + √n 推论 | **✅ zero sorry** | `LimitTheorems/DeltaMethod.lean` |
| 1.13-1.14 SLLN | **✅ zero sorry** (USLLN) | `LimitTheorems/USLLN.lean` |
| 1.5 Scheffé | **✅ zero sorry** | `LimitTheorems/Scheffe.lean` |
| 1.9 Lévy-Cramér 连续性 | ❌ **阻塞** — Mathlib 缺 | — |
| 1.15 Lindeberg CLT | ❌ **阻塞** — 需 Lévy | `LimitTheorems/CLT.lean` |
| 1.16-1.17 Edgeworth/Cornish-Fisher | ❌ 未开始 | — |
| Berry-Esseen (书外) | **1 sorry** (Stieltjes) | `LimitTheorems/BerryEsseen.lean` |
| CharFun Taylor 链 | **✅ zero sorry** | `CharFun/Taylor.lean` |
| 收敛模式定义 (a.s./P/Lp) | **✅ zero sorry** | `LimitTheorems/Convergence.lean` |

### Chapter 2 — Sufficiency & Completeness（5/6 完成，~83%）

| 定理 | 状态 | 文件 |
|------|------|------|
| 2.1 指数族性质 + MLE + NatExpFamily | **✅ zero sorry** | `ExpFamily/Basic.lean` |
| 2.2 因子分解（双向） | **✅ zero sorry** | `Sufficiency/Factorization.lean` |
| 2.3 最小充分性（3 判据） | **✅ zero sorry** | `Sufficiency/MinimalSufficiency.lean` |
| 2.4 Basu 定理 | **✅ zero sorry** | `Sufficiency/Basu.lean` |
| 2.5 Rao-Blackwell (12 变体) | **✅ zero sorry** | `Variance/RaoBlackwell.lean` |
| 2.6 渐近 MSE | ❌ 未开始 | — |

### Chapter 3 — UMVUE, Cramér-Rao, Linear Models（4/17 完成，~24%）

| 定理 | 状态 | 文件 |
|------|------|------|
| 3.1 Lehmann-Scheffé UMVUE | **✅ zero sorry** | `Sufficiency/LehmannScheffe.lean` |
| 3.2 UMVUE 条件 | ✅ 隐含于 L-S | — |
| 3.3 Cramér-Rao 下界 | **✅ zero sorry** | `Information/CramerRao.lean` |
| 3.4 Hoeffding U-stat 方差界 | ❌ 未开始 | — |
| 3.5 U-stat 渐近分布 | ❌ 未开始 | — |
| 3.6-3.8 线性模型可估 + UMVUE | ❌ 未开始 | — |
| 3.9 Gauss-Markov | **✅ zero sorry** | `Regression/GaussMarkov.lean` |
| 3.10-3.17 (高级) | ❌ 未开始 | — |

### 书外补充（集中不等式等）

| 模块 | 状态 | sorry |
|------|------|-------|
| Gaussian Poincaré (1D proved) | 部分 | 2 sorry (Fubini) |
| Log-Sobolev | 部分 | 3 sorry (hypercontractivity) |
| Efron-Stein | 部分 | 2 sorry (Fubini) |
| Sub-Gaussian / Herbst | 部分 | 1 sorry (blocked by LSI) |
| ANOVA 方差分解 | **✅ zero sorry** | 0 |
| Hermite 正交 + IBP | **✅ zero sorry** | 0 |

### 汇总

| 指标 | 数值 |
|------|------|
| 书中 92 个定理覆盖 | **~21 个零 sorry**（~23%） |
| Phase 0（工具链） | **~90% 完成** |
| Phase 1（Ch1 概率基础） | **~65% 完成**（Lévy 阻塞 CLT） |
| Phase 2（Ch2 充分性） | **~83% 完成**（仅缺 2.6 + 指数族完备性） |
| Phase 3（Ch3 UMVUE/CR/LM） | **~24% 完成**（+Gauss-Markov，缺 U-stat） |
| Phase 4-7 | **0% 完成** |

---

## 三、Token 估算

### 按难度分层

根据项目实际经验（Rao-Blackwell ~30M、Factorization ~80M、Lehmann-Scheffé ~60M、USLLN ~100M），每个定理的 token 消耗按难度分层：

| 难度 | 定理数 | 特征 | 单定理成本 | 小计 |
|------|--------|------|-----------|------|
| **Tier S**（极难） | ~8 | MLE 渐近正态 (4.16-4.19)、经验过程 (5.1-5.2)、GEE 渐近 (5.13-5.14)、Bootstrap 相合性 (5.20) | 200-500M | **1.6-4B** |
| **Tier A**（难） | ~20 | Neyman-Pearson、UMPU (6.4)、James-Stein (4.15)、U-statistic 渐近 (3.5)、Gauss-Markov、Bahadur 表示 (5.11) | 60-200M | **1.2-4B** |
| **Tier B**（中等） | ~35 | Cramér-Rao、minimax (4.11-4.12)、UMP (6.2)、LR 检验 (6.5)、jackknife/bootstrap | 20-60M | **0.7-2.1B** |
| **Tier C**（易/Mathlib 已有） | ~30 | Slutsky、delta-method、continuous mapping、Basu、基本 Bayes | 5-20M | **0.15-0.6B** |

**全书估算：3.5-11B tokens**（中位数 ~**7B tokens**）

### 换算成 Max 20x 周用量

Max 20x 的 opus 实际周预算，按重度 Claude Code prove-deep 使用估计约 **50-150M tokens/周**。取中位 ~100M/周：

| 指标 | 保守估计 | 中位估计 | 乐观估计 |
|------|---------|---------|---------|
| 总 token | 11B | 7B | 3.5B |
| 20x 周用量倍数 | **110 倍** | **70 倍** | **35 倍** |
| 等价全职时间 | ~2.2 年 | ~1.4 年 | ~8 个月 |

### Token 消耗构成分析

```
证明搜索（试错循环）    ≈ 45%   ← 最大浪费源
上下文重读（长文件反复读）≈ 20%
Mathlib API 发现         ≈ 15%
类型错误调试              ≈ 12%
代码生成（实际写代码）    ≈  8%
```

---

## 四、工具链改进——思路与原理

### 4.1 Proof Search 优化（目标：节省 45% 中的一半）

**原理**：当前证明搜索是"生成-编译-报错-修改"循环，每轮 ~50-100K tokens，一个难定理可能循环 50-200 次。优化方向是减少循环次数和单次成本。

**A. Tactic 预测模型（最高 ROI）**
- **思路**：维护一个 `tactic_patterns.yaml`，记录 "目标形态 → 成功 tactic 序列" 的映射
- **原理**：同一种证明模式反复出现（如 "∀ ae, ∫ f ≤ ∫ g" → `integral_mono + ae_of_all`），但每次都从头搜索
- **实现**：每次证明成功后，提取 `(goal_type_pattern, tactic_sequence)` 写入索引。下次遇到类似 goal 先查索引
- **预期收益**：减少 20-30% 的试错循环

**B. 增量 `lake build` + 错误定位**
- **思路**：当前每次试一个 tactic 都要编译整个文件（~10-30 秒）。改为只编译目标 declaration
- **原理**：`lake env lean --stdin` 可以单独编译一个 snippet，但需要正确的 import 上下文
- **实现**：写一个 `scripts/check_snippet.sh`，自动注入 import 头 + 目标 declaration → `lean --stdin`
- **预期收益**：编译反馈速度 ×3-5，间接减少等待中的上下文浪费

**C. `exact?` / `apply?` 批量化**
- **思路**：对一个有 5 个 sorry 的文件，当前是逐个跑 `exact?`。可以并行化
- **原理**：每个 `exact?` 调用是独立的搜索，可以同时开 3 个 subagent 各跑一组
- **实现**：`scripts/batch_exact.lean` — 接受目标列表，并行搜索，返回候选
- **预期收益**：搜索时间 ÷3

### 4.2 上下文管理优化（目标：节省 20% 中的大部分）

**原理**：当前模式是"读 800 行文件 → 改 3 行 → 编译失败 → 重新读 800 行"。大文件在上下文中反复出现是巨大的浪费。

**A. Declaration-level 缓存**
- **思路**：不再每次读整个文件，改为维护一个"当前文件声明索引"
- **原理**：证明 lemma_42 时只需要 lemma_42 的签名和它依赖的签名，不需要 lemma_1 到 lemma_41 的完整证明体
- **实现**：`scripts/extract_signatures.py` — 提取文件中所有 `theorem/def/lemma` 的签名（不含证明体），生成 ~50 行的摘要供 agent 参考
- **预期收益**：上下文消耗减少 60-70%

**B. Diff-only 反馈**
- **思路**：编译失败后只返回错误消息 + 出错行的 ±5 行上下文，不重读整个文件
- **原理**：Lean 的错误消息已经包含足够的定位信息
- **预期收益**：每轮循环的 input token 从 ~80K 降到 ~10K

### 4.3 Mathlib API 发现自动化（目标：节省 15%）

**原理**：当前的三级搜索法已经很好，但第二级（`#check` / `exact?`）仍然很慢。

**A. 离线类型索引**
- **思路**：预生成 Mathlib 所有声明的 `(name, type_signature)` 索引（~100K 条，~5MB）
- **原理**：当前 `#check` 是在线查询，需要启动 Lean 进程。离线索引可以用 grep 在 0.1 秒完成
- **实现**：`lake env lean scripts/gen_full_type_index.lean > mathlib_type_index.tsv`
- **预期收益**：API 发现从 30-60 秒降到 <1 秒，且 0 token 成本

**B. 语义搜索 embeddings**
- **思路**：对 Mathlib 声明做 embedding，按 goal 类型做语义相似度搜索
- **原理**：当前搜索靠关键词匹配，会漏掉命名风格不同但语义相同的 API
- **实现**：用 haiku 对每个 Mathlib 声明生成一句话摘要，做向量检索
- **预期收益**：找到 API 的概率从 ~80% 提升到 ~95%

### 4.4 综合改进潜力

| 改进项 | 实现难度 | 预期 token 节省 |
|--------|---------|----------------|
| Tactic pattern 索引 | 低（yaml 文件） | 15-20% |
| Declaration-level 缓存 | 中（python 脚本） | 10-15% |
| 离线类型索引 | 低（lean 脚本） | 5-10% |
| 增量编译 snippet | 中 | 5-10% |
| Diff-only 反馈 | 低（prompt 改进） | 5-8% |
| 语义搜索 | 高（需 embedding 基础设施） | 3-5% |

**理论上限：节省 35-55%**，实际实现后预计 **节省 20-40%**（取中位 30%）。

---

## 五、前期基础设施建设推荐（按优先级排序）

核心原则：**先建复用度最高的基础设施，使后续定理的边际成本最低**。

### Phase 0：工具链（1-2 周）— ✅ 已完成 ~90%

| 工具 | 状态 |
|------|------|
| `theme/mathlib_api_index.md`（650+ API 索引） | ✅ 已完成 |
| `scripts/gen_mathlib_index.lean`（自动生成） | ✅ 已完成 |
| 增量编译（`lake build Statlean.Module`） | ✅ 已成标准流程 |
| `MEMORY.md`（97 条 tactic pattern） | ✅ 持续积累 |
| 完整 Mathlib 类型索引 tsv | ❌ 未做 |
| `scripts/check_snippet.sh` 单 decl 编译 | ❌ 未做 |

### Phase 1：Ch1 概率基础补全 — ✅ ~65% 完成

| 优先级 | 定理 | 状态 |
|--------|------|------|
| P1 | 1.10 Continuous Mapping Theorem | **✅ zero sorry** |
| P2 | 1.11 Slutsky's Theorem | **✅ zero sorry** |
| P3 | 1.12 Delta Method + √n 推论 | **✅ zero sorry** |
| — | 1.5 Scheffé | **✅ zero sorry** |
| — | 1.13-1.14 SLLN (USLLN) | **✅ zero sorry** |
| — | Berry-Esseen（书外） | **1 sorry**（Stieltjes 反演） |
| — | CharFun Taylor 链（书外） | **✅ zero sorry** |
| P4 | 1.9 Lévy-Cramér 连续性定理 | ❌ **阻塞** — Mathlib 缺（~500-700 行） |
| P5 | 1.15 Lindeberg CLT | ❌ **阻塞** — 需 Lévy |
| — | 1.16-1.17 Edgeworth/Cornish-Fisher | ❌ 未开始 |

### Phase 2：指数族 + 充分性补全 — ✅ ~83% 完成

| 优先级 | 内容 | 状态 |
|--------|------|------|
| P6 | 2.1 指数族性质 + MLE 存在唯一 | **✅ zero sorry** |
| P7 | 2.3 Minimal Sufficiency（3 判据） | **✅ zero sorry** |
| — | 2.2 Fisher-Neyman 因子分解（双向） | **✅ zero sorry** |
| — | 2.4 Basu 定理 | **✅ zero sorry** |
| — | 2.5 Rao-Blackwell MSE（12 变体） | **✅ zero sorry** |
| P8 | 指数族完备性（Completeness） | ❌ **未开始** — Phase 6 (UMP/UMPU) 的前提 |
| — | 2.6 渐近 MSE (Bayes) | ❌ 未开始 |

**剩余工作**：指数族完备性是 Ch6 (UMPU) 的关键前提，建议优先形式化。

### Phase 3：Fisher Information + Cramér-Rao + 线性模型 — ✅ 核心完成 + Gauss-Markov

| 优先级 | 内容 | 状态 |
|--------|------|------|
| P9 | Fisher information 定义 + score function | **✅ zero sorry** |
| P10 | 3.3 Cramér-Rao Lower Bound | **✅ zero sorry** |
| P11 | 3.1 Lehmann-Scheffé + 3.2 UMVUE 条件 | **✅ zero sorry** |
| — | MLE 定义 + 不变性 (isMLE_comp) | **✅ zero sorry** |
| — | MSE = Bias² + Variance | **✅ zero sorry** |
| P12 | 3.4 Hoeffding U-stat 方差界 | ❌ 未开始 |
| P13 | 3.5 U-stat 渐近分布 | ❌ 未开始（需 CLT） |
| P14 | 3.6-3.8 线性模型可估 + UMVUE | ❌ 未开始 |
| P15 | 3.9 Gauss-Markov | **✅ zero sorry** — 正交投影 API |
| — | NatExpFamily 结构 + 密度比因子分解 | **✅ zero sorry** |
| — | 3.10-3.17 (高级) | ❌ 未开始 |

**剩余工作**：U-stat (3.4-3.5) 和线性模型高级理论 (3.6-3.8, 3.10-3.17)。

### Phase 4：U-statistics + Linear Models 基础（3-4 周）

| 优先级 | 内容 | 复用度 | 难度 | 预计 token |
|--------|------|--------|------|-----------|
| **P12** | 3.4 Hoeffding decomposition | 高 | 中 | 30-50M |
| **P13** | 3.5 U-statistic 渐近分布 | 高 | 难 | 60-100M |
| **P14** | 3.6-3.8 线性模型可估性 + UMVUE | 中 | 中 | 40-60M |
| **P15** | 3.9 Gauss-Markov | 中 | 易 | **✅ 已完成** |

### Phase 5：决策论 + Bayes 基础（3-4 周）

| 优先级 | 内容 | 复用度 | 难度 | 预计 token |
|--------|------|--------|------|-----------|
| **P16** | Loss, Risk, Bayes risk 定义体系 | 高（Ch4 全用） | 易 | 15-25M |
| **P17** | 4.1 Bayes formula + 4.2 Admissibility | 高 | 中 | 30-50M |
| **P18** | 4.11-4.12 Minimax (Bayes estimator) | 中 | 中 | 40-60M |

### Phase 6：检验论（4-5 周）

| 优先级 | 内容 | 复用度 | 难度 | 预计 token |
|--------|------|--------|------|-----------|
| **P19** | 6.1 Neyman-Pearson Lemma | 极高 | 难 | 60-100M |
| **P20** | 6.2 UMP (monotone likelihood ratio) | 高 | 中 | 40-60M |
| **P21** | 6.4 UMPU in exponential families | 中 | 难 | 80-120M |

### Phase 7：渐近效率 + 非参（最难，8-12 周）

| 优先级 | 内容 | 复用度 | 难度 | 预计 token |
|--------|------|--------|------|-----------|
| **P22** | 4.16 Asymptotic information inequality | 极高 | 极难 | 200-400M |
| **P23** | 4.17-4.19 MLE 渐近效率 | 极高 | 极难 | 300-500M |
| **P24** | 5.1-5.2 经验过程渐近 | 高 | 极难 | 200-400M |
| **P25** | 5.5-5.7 可微统计泛函 | 中 | 难 | 100-200M |

---

## 六、修正后总估算

| 场景 | 总 token | 20x 周用量倍数 | 日历时间（每周满载） |
|------|---------|---------------|-------------------|
| 无工具改进 | ~7B | ~70 倍 | ~1.4 年 |
| 有工具改进（Phase 0） | ~5B | ~50 倍 | ~1 年 |
| 只做核心 80%（跳过 Tier S） | ~2.5B | ~25 倍 | ~6 个月 |
| 只做 Phase 1-3（概率基础 + 充分性 + Cramér-Rao） | ~0.5B | ~5 倍 | ~5 周 |

**建议路径**：先做 Phase 0（工具）+ Phase 1（概率基础），这两块 ~5-7 个 20x 周用量就能完成，但会为后续所有工作铺路，降低 30-50% 的后续成本。

---

## 附录：难度分级标准

- **Tier S（极难）**：Mathlib 缺根基性基础设施（如没有 Fourier inversion for distributions、没有 empirical process theory），需要从头建 200+ 行基础设施后才能写目标定理。单定理 200-500M tokens。
- **Tier A（难）**：Mathlib 有部分基础设施但有 gap，需要 5-15 个中间引理。单定理 60-200M tokens。
- **Tier B（中等）**：Mathlib API 基本够用，但组合方式非平凡，需要 instance resolution 调试。单定理 20-60M tokens。
- **Tier C（易）**：Mathlib 有直接 API 或 1-2 步组合即可。单定理 5-20M tokens。
