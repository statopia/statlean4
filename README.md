# StatLean — 统计定理的 Lean 4 形式化的自动化工具

用 Lean 4 + Mathlib 形式化统计的核心定理和概念。

**当前规模**：36 个 Lean 文件，~180 个声明，28 个零 sorry 模块。

> **想参与贡献？请阅读 [INSTRUCTION.md](INSTRUCTION.md)** — 包含环境搭建、贡献方式、Pipeline 用法、验收标准等完整指南。

---

## 已完成定理（全部零 sorry，机器可验证）

| 领域 | 定理 | 文件 |
|------|------|------|
| 估计 | Rao-Blackwell MSE 定理 | `Variance/RaoBlackwell.lean` |
| 估计 | MSE = Bias² + Variance | `Estimator/Basic.lean` |
| 估计 | Lehmann-Scheffé UMVUE | `Sufficiency/LehmannScheffe.lean` |
| 估计 | Cramér-Rao 下界 | `Information/CramerRao.lean` |
| 估计 | 指数族 MLE 存在唯一性 | `ExpFamily/Basic.lean` |
| 估计 | MLE 定义 + 不变性定理 | `Estimator/Basic.lean` |
| 充分性 | Fisher-Neyman 因子分解（双向） | `Sufficiency/Factorization.lean` |
| 充分性 | Basu 定理 | `Sufficiency/Basu.lean` |
| 充分性 | 最小充分统计量密度比判据 | `Sufficiency/MinimalSufficiency.lean` |
| 充分性 | 子族扩展判据 | `Sufficiency/MinimalSufficiency.lean` |
| 集中不等式 | ANOVA 方差分解 | `Variance/ANOVA.lean` |
| 集中不等式 | Hermite 正交性 + Parseval + IBP | `Gaussian/Hermite.lean` |
| 极限定理 | 均匀强大数律 (USLLN) | `LimitTheorems/USLLN.lean` |
| 极限定理 | Berry-Esseen 定理（模 2 个分析引理） | `LimitTheorems/BerryEsseen.lean` |
| 极限定理 | 特征函数 Taylor 链 | `CharFun/Taylor.lean` |

**9 个真实数学 sorry** 等待攻击（另有 18 个 Pipeline 生成的占位符 sorry）→ [`sorry_backlog.yaml`](theme/input/sorry_backlog.yaml)

---

## 快速开始

```bash
git clone https://github.com/<your-username>/statlean4.git && cd statlean4
curl https://elan-init.tracing.rs/elan-init.sh -sSf | sh   # 安装 elan（已有则跳过）
lake exe cache get                                           # 下载 Mathlib 缓存（~5 分钟）
lake build Statlean                                          # 验证编译
```

```bash
# (可选) 用 Codex CLI 替代 Claude Code
AGENT_BACKEND=codex make -C theme prove-fallback
```

详细指南见 **[INSTRUCTION.md](INSTRUCTION.md)**。

---

## 项目结构

```
Statlean/
  Gaussian/          # 标准高斯、Stein、Hermite、Poincaré
  Variance/          # Rao-Blackwell、ANOVA、Efron-Stein
  Entropy/           # 熵、Log-Sobolev
  SubGaussian/       # Herbst、Lipschitz 集中
  CharFun/           # 特征函数 Taylor
  LimitTheorems/     # USLLN、Berry-Esseen、CLT、收敛模式
  Sufficiency/       # 因子分解、Basu、最小充分、Lehmann-Scheffé
  Information/       # Fisher 信息、Cramér-Rao
  Estimator/         # MSE 分解、MLE 不变性、风险支配
  ExpFamily/         # 指数族 MLE
  Statistic/         # ParametricFamily、IsUnbiased
  EmpiricalProcess/  # 覆盖数、Dudley 积分
  Regression/        # 最小二乘、主误差界
  SPD/               # Log-Cholesky Fréchet 均值
  Pipeline/          # Pipeline 生成的存根（待整理）
  Verified.lean      # 零 sorry 模块索引
```

---

## 验收标准

```bash
lake build                       # 零错误
lake build Statlean.Verified     # 零 sorry 警告
```

sorry 数只减不增，详见 [INSTRUCTION.md](INSTRUCTION.md)。

---

## Sorry 缺口概览

| Blocker | 阻塞 | sorry 数 |
|---------|------|---------|
| Measure.pi Fubini | EfronStein (2) + Poincaré 纤维化 (1) | 3 |
| Gaussian hypercontractivity | LogSobolev (2) + Herbst (1) | 3 |
| Fourier analysis | Berry-Esseen 通用常数 (3) | 3 |

完整清单 → [`sorry_backlog.yaml`](theme/input/sorry_backlog.yaml)

---

## 文档索引

| 文档 | 说明 |
|------|------|
| **[INSTRUCTION.md](INSTRUCTION.md)** | **贡献指南** — 环境搭建、4 种贡献方式、`theorems.yaml` 格式、验收标准、FAQ |
| [theme/PIPELINE.md](theme/PIPELINE.md) | Pipeline 详解 — 各阶段（extract → ingest → generate → prove → gate）的输入输出和用法 |
| [theme/formalize_playbook.md](theme/formalize_playbook.md) | 形式化操作手册 — 「形式化 XX 里的 YY」的 7 步 SOP（Claude Code / Codex 共用） |
| [theme/prove_playbook.md](theme/prove_playbook.md) | 证明操作手册 — 策略选择表、Mathlib API 三级搜索法、condExp 专项模式、编译错误修复表 |
| [theme/input/sorry_backlog.yaml](theme/input/sorry_backlog.yaml) | Sorry 缺口清单 — 所有待证目标的优先级、blocker、依赖关系 |
| [CLAUDE.md](CLAUDE.md) | Claude Code 项目配置 — 文件组织原则、证明策略、Mathlib 搜索规则、效率规则 |
| [AGENTS.md](AGENTS.md) | Codex CLI 项目配置 — 模块组织、证明策略、Mathlib 搜索（CLAUDE.md 的后端无关子集） |
| [theme/mathlib_api_index.md](theme/mathlib_api_index.md) | Mathlib API 索引 — 650+ 条常用 API，按 namespace 分类（证明前必读） |
| [theme/INFRA_CLASSIFICATION.md](theme/INFRA_CLASSIFICATION.md) | 基础设施分类方案 — definition vs theorem 的判定与文件归属规则 |
