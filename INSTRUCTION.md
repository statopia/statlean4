# StatLean Contributor Guide

## 项目简介

StatLean 是一个用 Lean 4 + Mathlib 形式化数理统计定理的开源项目。

**当前规模**：34 个 Lean 文件，~180 个声明，22 个零 sorry 模块已入库 `Verified.lean`。

**已完成的核心定理**（全部零 sorry）：
- Rao-Blackwell MSE 定理、ANOVA 方差分解
- Fisher-Neyman 因子分解定理（双向）、Basu 定理
- 最小充分统计量判据（密度比 + 子族扩展 + 密度比统计量 DRC）
- Lehmann-Scheffé UMVUE 定理、Cramér-Rao 下界
- Berry-Esseen 定理（模 2 个分析 sorry）、均匀强大数律
- Hermite 正交性 + Parseval + IBP、MSE = Bias² + Var
- 指数族 MLE 存在唯一性 + MLE 不变性

**10 个 sorry 缺口**正等待攻击（详见 `theme/input/sorry_backlog.yaml`）。

---

## 快速开始：Claude Code 会话内使用

> 这是最常用的方式。进入 `claude` 会话后，用自然语言下达指令即可。

### 从 PDF 到形式化

```bash
# 整份 PDF 一站式
> /pipeline theme/input/raw/lecture-9-handout.pdf

# 只要 PDF 中的某个定理（自然语言即可）
> 帮我形式化 lecture-9-handout.pdf 里的 Scheffé 定理
> 把 lecture-9-handout.pdf 第 3 页的 Theorem 2 形式化到 Lean

# 只要某个定义
> 形式化 lecture-9-handout.pdf 里 Fisher Information 的定义

# 多个目标
> 把 lecture-9-handout.pdf 里的 CLT 和 Slutsky 定理形式化
```

### 攻击已有 sorry

```bash
# 交互式攻击单个 sorry
> /prove Statlean/Gaussian/Poincare.lean condExp_eq_fiberAvg_pi

# 自动攻击所有叶节点 sorry（DAG 调度，3 并发 agent）
> /prove-deep all-leaves
```

### 工具命令

```bash
# 检查所有 sorry 状态
> /sorry-status

# 编译修复
> /build-fix

# 保存进度到 memory + commit
> /checkpoint
```

---

## 终端命令（不进入 claude 会话）

### 一句话形式化

```bash
# 用 claude -p 指定（走 Max 额度，非 API credit）
claude -p "形式化 theme/input/raw/lecture-9-handout.pdf 里的 Scheffé 定理"
claude -p "把 lecture-9-handout.pdf 第 8 页的 Continuous Mapping Theorem 形式化到 Lean"
```

### Make 命令

```bash
# ── 完整 pipeline（从 PDF 到 gate）──
make -C theme pdf-formalize PDF=path/to/paper.pdf

# ── 从 LaTeX 开始 ──
make -C theme tex-formalize TEX=path/to/paper.tex

# ── 从已有 YAML 开始（跳过提取）──
make -C theme formalize

# ── 只跑 prove + gate ──
make -C theme prove-fallback   # prove 循环（调用 claude/codex agent）
make -C theme gate              # gate 验收（含 auto-shelve 自动入库）

# ── 单独跑 auto-shelve ──
make -C theme auto-shelve

# ── 常用参数 ──
make -C theme formalize AGENT_BACKEND=claude
make -C theme formalize MAX_PARALLEL=3 PROVE_BUDGET=3600
```

### 分步操作（更可控）

```bash
# 1. 把 PDF 放入 theme/input/raw/
cp lecture-5-handout.pdf theme/input/raw/

# 2. 提取 + 识别
make -C theme from-pdf PDF=lecture-5-handout.pdf   # PDF → LaTeX
make -C theme from-tex                             # LaTeX → YAML（自动识别定理名）

# 3. 生成骨架 + 证明 + 验收
make -C theme formalize

# 4. 精确提取特定定理
python3 theme/scripts/pdf_extract.py theme/input/raw/lecture-9-handout.pdf \
  --theorem "Scheffé" --pages 3-5
```

---

## 环境准备

```bash
# 1. Fork & clone
git clone https://github.com/<your-username>/statlean4.git
cd statlean4

# 2. 安装 elan + Lean（已有则跳过）
curl https://elan-init.tracing.rs/elan-init.sh -sSf | sh

# 3. 下载 Mathlib 编译缓存（~5 分钟，避免 2 小时全量编译）
lake exe cache get

# 4. 验证编译
lake build Statlean
```

**Lean 版本**：4.28.0-rc1（elan 会自动管理）。

### Claude Code 安装

```bash
# 需要 Claude Pro/Max 订阅
npm install -g @anthropic-ai/claude-code
cd statlean4
claude
```

### Codex CLI 安装（可选）

```bash
# 需要 ChatGPT Plus/Pro 或 OPENAI_API_KEY
npm install -g @openai/codex
cd statlean4
codex --version && codex login
bash theme/mcp/register_codex.sh
```

---

## 贡献方式一览

| 方式 | 适合场景 | 入口 |
|------|----------|------|
| **Claude Code 会话** | 最常用，自然语言驱动 | `claude` → 自然语言指令 |
| **终端 Make** | CI / 批量处理 | `make -C theme pdf-formalize PDF=...` |
| **终端 claude -p** | 快速一次性任务 | `claude -p "形式化 ..."` |
| **Codex CLI** | 替代后端 | `AGENT_BACKEND=codex make -C theme ...` |
| **纯手写 Lean** | 不需要工具链 | `vim Statlean/... && lake build` |

---

## Pipeline 各阶段说明

```
PDF
 │
 ▼ (from-pdf)
LaTeX
 │
 ▼ (from-tex: 提取 + heuristic/AI 定理名识别)
theorems.yaml (含 canonical name + topic)
     │
     ▼
  resolve ──→ ingest ──→ plan ──→ generate ──→ build-check
                                      │
                                      ▼
                              sync-backlog ──→ prove ──→ gate
                                                          │
                                                     auto-shelve
                                                   (Verified.lean
                                                    Statlean.lean
                                                    sorry_backlog)
```

| 阶段 | 做什么 | 消耗 |
|------|--------|------|
| `from-pdf` | PDF → LaTeX（pymupdf 本地提取） | 零 |
| `from-tex` | LaTeX → theorems.yaml + notation.yaml。**自动识别定理名**（heuristic 零 API，或 AI fallback） | 零~少量 |
| `resolve` | 概念名 → YAML（可选，`CONCEPTS=` 时触发） | 零 |
| `generate` | YAML → Lean 骨架。按 `topic` 字段路由到 `Statlean/<Topic>/` 对应文件 | 零 |
| `prove` | 生成 prove_targets.json；自动证明由 `prove-fallback` 调用 agent | Max 额度 |
| `gate` | build + sorry 计数 + PIPELINE_ID 检查 + **auto-shelve** | 零 |

**API 消耗策略**：Pipeline 默认**零 API credit 消耗**。证明阶段走 Claude/Codex CLI 账号额度。

**定理名自动识别**（`from-tex` 阶段）：三级 fallback：
1. **Anthropic SDK**（需 `ANTHROPIC_API_KEY`）→ Claude Haiku 批量识别
2. **Claude CLI**（需 Max 订阅）→ `claude -p`
3. **Heuristic 匹配**（零 API，始终可用）→ ~70 条关键词规则

### 参数

| 变量 | 默认 | 说明 |
|------|------|------|
| `AGENT_BACKEND` | `claude` | AI 后端：`claude` 或 `codex` |
| `PDF` | 空 | PDF 文件路径或关键词 |
| `TEX` | `../output.tex` | LaTeX 文件路径 |
| `MANIFEST` | 空 | manifest.json 路径，设置后只攻击该批次定理 |
| `PROVE_DEPTH` | `deep` | `deep` = 生成 prove 目标；`shallow` = 跳过 |
| `PROVE_BUDGET` | `3600` | prove 时间预算（秒） |
| `MAX_PARALLEL` | `3` | 最大并行 prove agent 数 |

---

## 文件组织

```
Statlean/
  Gaussian/Basic.lean             # 标准高斯分布基础设施
  Gaussian/Poincare.lean          # Poincaré 不等式（已证 + sorry 共存）
  Variance/RaoBlackwell.lean      # Rao-Blackwell MSE 定理
  Sufficiency/Factorization.lean  # Fisher-Neyman 因子分解
  Estimator/Basic.lean            # 估计量基础（MSE、MLE、风险支配）
  LimitTheorems/CLT.lean          # CLT 相关（pipeline 按 topic 自动路由）
  Pipeline/Lecture9Handout.lean   # 未分类定理（每 PDF 一个文件，待整理）
  Verified.lean                   # 零 sorry 模块索引
  ...
```

- 路径反映数学对象：`Gaussian/Poincare.lean`，不是 `Concentration/GaussianPoincare.lean`
- 已证引理和 sorry gap **放同一文件**，用 `section` 隔离
- 定理名语义化：`cramer_rao`，不是 `theorem_007`
- Pipeline 未分类定理 → `Pipeline/<PDF名>.lean`，后续可手动搬迁

### `theorems.yaml` 格式

```yaml
version: v1
theorem_set: my-theorems
defaults:
  lean_namespace: Statlean
  layer: formalization
  allow_axiom: false
theorems:
- id: lec5.mse_bias_variance
  title: "MSE = Bias² + Variance"
  kind: theorem
  latex_statement: |
    For estimator $T$, $\mathrm{MSE} = \mathrm{Bias}^2 + \mathrm{Var}$.
  lean_name: "mse_eq_bias_sq_add_variance"
  lean_namespace: Statlean.Estimator
  lean_statement: |                  # 可选：直接写 Lean 签名
    theorem mse_eq_bias_sq_add_variance ...
  priority: 1
  dependencies: []
```

> 提供 `lean_statement` 则直接使用；否则生成 `True := by sorry` 占位符。

---

## 验收标准

提交 PR 前确保：

1. **`lake build` 零错误**
2. **sorry 数不增加**
3. **`Verified.lean` 一致**：零 sorry 文件加入 Verified.lean
4. **PIPELINE_ID 保留**：不要删除生成的 `PIPELINE_ID:` 注释

```bash
lake build                              # 零错误
lake build Statlean.Verified            # 零 sorry 警告
bash theme/scripts/gate.sh .            # 完整检查
```

---

## 提交流程

```bash
git checkout -b feat/my-theorem
lake build Statlean.MyModule
git add Statlean/
git commit -m "feat: prove my_theorem (zero sorry)"
git push origin feat/my-theorem
gh pr create --title "Prove my_theorem"
```

---

## Sorry 缺口清单

`theme/input/sorry_backlog.yaml` 记录所有待攻击 sorry：priority、blocker、dependencies、unlocks。

**选择目标**：优先选 `type: honest`（路线清晰）且 `dependencies: []`（无前置依赖）的叶节点。

当前主要 blocker：
- **Measure.pi Fubini**：阻塞 EfronStein (2) + Poincaré 纤维化 (2)
- **Gaussian hypercontractivity**：阻塞 LogSobolev (2) + Herbst (1)
- **Stieltjes inversion**：阻塞 Berry-Esseen 通用常数 (1)

---

## Codex CLI 详细用法

```bash
# 最小命令组（给定 PDF -> 定向 prove -> gate）
AGENT_BACKEND=codex make -C theme pdf-formalize PDF=lecture-6
MANIFEST=out/manifest.json AGENT_BACKEND=codex AUTO_AGENT=1 MAX_ITERS=10 MAX_PARALLEL=3 PROVE_BUDGET=3600 make -C theme prove-fallback
make -C theme gate

# 查看产物
test -f theme/out/manifest.json && echo "ok: manifest.json"
test -f theme/out/prove_targets.json && echo "ok: prove_targets.json"
tail -n 20 theme/out/logs/pipeline.jsonl

# 查看 manifest 状态
python3 -c "
import json; from collections import Counter
m = json.load(open('theme/out/manifest.json'))
c = Counter(e.get('status','unknown') for e in m.get('entries', {}).values())
print('status_count:', dict(c))
"
```

> Codex 读取 `AGENTS.md` 获取项目指令。`prove-fallback` 需传 `MANIFEST` 以限定攻击范围。

---

## FAQ

| 问题 | 回答 |
|------|------|
| 谁承担 token 费用？ | 你自己 — Claude Pro/Max 订阅或 API key |
| 最小贡献单位？ | 一个 sorry gap（一个子引理也算） |
| 部分进展可以 PR 吗？ | 可以 — 只要 sorry 数不增加 |
| 必须用 Claude 吗？ | 不必 — Codex CLI 或手写 Lean 均可 |
| Pipeline 是必须的吗？ | 不是 — 直接编辑 `.lean` 文件完全可以 |
| 怎么只形式化 PDF 某个定理？ | 会话内直接说；终端用 `claude -p` 或 `pdf_extract.py --theorem` |
| `Pipeline/*.lean` 是什么？ | 未分类定理的暂存文件，每 PDF 独立，可手动搬迁 |
| auto-shelve 何时触发？ | gate 阶段自动触发，也可手动 `make -C theme auto-shelve` |
| 多份 PDF "Theorem 1" 冲突？ | 不会，source_tag 前缀保证 ID 唯一 |
