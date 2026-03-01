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
- 指数族 MLE 存在唯一性

**10 个 sorry 缺口**正等待攻击（详见 `theme/input/sorry_backlog.yaml`）。

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

---

## 贡献方式

### 方式 A：从 PDF 到形式化（完整 pipeline）

适合有课程讲义 / 论文的场景。Pipeline 自动完成：PDF 提取 → LaTeX → YAML（含定理名识别）→ Lean 骨架 → 证明 → 验收。

```bash
# 一键完成（推荐）
make -C theme pdf-formalize PDF=lecture-9-handout.pdf
# 流程: PDF → LaTeX → YAML → 定理名识别 → Lean 骨架 → build → prove → gate（含 auto-shelve）

# 或分步操作：
# 1. 把 PDF 放入 theme/input/raw/
cp lecture-5-handout.pdf theme/input/raw/

# 2. 提取 + 识别
make -C theme from-pdf PDF=lecture-5-handout.pdf   # PDF → LaTeX
make -C theme from-tex                             # LaTeX → YAML（自动识别定理名）

# 3. 跑 pipeline（生成骨架 + 证明 + 验收）
make -C theme formalize

# 4. Pipeline 产物：
#    - Lean 骨架已写入 Statlean/ 对应文件（按数学主题分类）
#    - theme/out/manifest.json 记录每个定理的位置
#    - theme/out/prove_targets.json 列出待证目标
#    - gate 报告 sorry 计数
```

**定理名自动识别**（`from-tex` 阶段）：

Pipeline 自动将 "Theorem 1" → "central_limit_theorem" 等 canonical name。三级 fallback：

1. **Anthropic SDK**（需要 `ANTHROPIC_API_KEY`）→ Claude Haiku 批量识别
2. **Claude CLI**（需要 Max 订阅，非 Claude Code 内部）→ `claude -p`
3. **Heuristic 匹配**（零 API，始终可用）→ ~70 条关键词规则，覆盖 CLT、δ-method、Lindeberg、Slutsky、Scheffé、Berry-Esseen、Rao-Blackwell、Cramér-Rao、Fisher 信息、Hoeffding、Jensen 等常见定理

```bash
# 如果不想用 AI，可以强制只用 heuristic
python3 theme/scripts/from_tex.py paper.tex theme/input --no-ai
```

**每份 PDF 独立隔离**：

不同 PDF 的定理不会互相干扰。每份 PDF 的源标签（如 `lecture_9_handout`）会：
- 前缀到 theorem ID（避免 "Theorem 1" 冲突）：`lecture_9_handout.theorem.001.delta_method`
- 未分类定理路由到独立文件：`Pipeline/Lecture9Handout.lean`

**`theorems.yaml` 格式**：

```yaml
version: v1
theorem_set: my-theorems
defaults:
  lean_namespace: Statlean
  layer: formalization
  allow_axiom: false
theorems:
- id: lec5.mse_bias_variance        # 唯一 ID
  title: "MSE = Bias² + Variance"   # 人类可读标题
  kind: theorem                      # theorem / definition / lemma
  latex_statement: |                 # LaTeX 数学表述
    For estimator $T$, $\mathrm{MSE} = \mathrm{Bias}^2 + \mathrm{Var}$.
  lean_name: "mse_eq_bias_sq_add_variance"
  lean_namespace: Statlean.Estimator
  lean_statement: |                  # 可选：直接写 Lean 签名
    theorem mse_eq_bias_sq_add_variance
        {Ω : Type*} [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (T : Ω → ℝ) (θ : ℝ)
        (hT : Memℒp T 2 μ) :
        ∫ ω, (T ω - θ) ^ 2 ∂μ =
          (∫ ω, T ω ∂μ - θ) ^ 2 + ∫ ω, (T ω - ∫ ω', T ω' ∂μ) ^ 2 ∂μ
  priority: 1
  dependencies: []
  acceptance:
  - lake build passes
  - theorem contains no sorry
```

> **提示**：如果提供了 `lean_statement`，pipeline 会直接使用它生成骨架；否则生成 `True := by sorry` 占位符，需要手动替换。

### 方式 B：直接攻击已有 sorry

不走 pipeline，直接找一个 sorry 来证。

```bash
# 查看 sorry 缺口清单
cat theme/input/sorry_backlog.yaml

# 或直接 grep
grep -rn 'sorry' Statlean/ --include="*.lean" | grep -v '\-\-'

# 编辑文件、写证明
vim Statlean/Gaussian/Poincare.lean

# 增量编译验证
lake build Statlean.Gaussian.Poincare
```

### 方式 C：用 Claude Code 辅助证明

```bash
# 安装 Claude Code（需要 Claude Pro/Max 订阅）
npm install -g @anthropic-ai/claude-code

cd statlean4
claude
```

**Claude Code 交互命令（在 `claude` 会话内使用）**：

```bash
# 交互式攻击单个 sorry
> /prove Statlean/Gaussian/Poincare.lean condExp_eq_fiberAvg_pi

# 自动攻击所有叶节点 sorry（DAG 调度，3 并发 agent）
> /prove-deep all-leaves

# 从 PDF 到形式化（一站式）
> /pipeline theme/input/raw/lecture-5-handout.pdf

# 检查所有 sorry 状态
> /sorry-status

# 编译修复
> /build-fix

# 保存进度到 memory + commit
> /checkpoint
```

**Claude Code + Make 联合使用（终端直接执行）**：

```bash
# ── 完整 pipeline（从 PDF 到 gate）──
make -C theme pdf-formalize PDF=path/to/paper.pdf
# 流程: PDF → LaTeX → YAML → Lean 骨架 → build → prove → gate（含 auto-shelve）

# ── 从 LaTeX 开始 ──
make -C theme tex-formalize TEX=path/to/paper.tex

# ── 从已有 YAML 开始（跳过提取）──
make -C theme formalize

# ── 只跑 prove + gate（代码已有，只想攻 sorry）──
make -C theme prove-fallback   # prove 循环（调用 claude/codex agent）
make -C theme gate              # gate 验收（含 auto-shelve 自动入库）

# ── 单独跑 auto-shelve（更新 Verified.lean / Statlean.lean）──
make -C theme auto-shelve

# ── 常用参数 ──
make -C theme formalize AGENT_BACKEND=claude          # 指定后端
make -C theme formalize MAX_PARALLEL=3 PROVE_BUDGET=3600  # 并行度 + 时间预算
```

### 方式 C2：用 Codex CLI 辅助证明

```bash
# 安装 Codex CLI（需要 ChatGPT Plus/Pro 或 OPENAI_API_KEY）
npm install -g @openai/codex

cd statlean4

# 0) 初始化（首次或环境变更后建议执行）
codex --version
codex login
codex exec --full-auto "ping"
bash theme/mcp/register_codex.sh
codex mcp list --json
python3 theme/mcp/scripts/smoke_test_mcp.py

# 最小命令组（给定 PDF -> 定向 prove -> gate）
AGENT_BACKEND=codex make -C theme pdf-formalize PDF=lecture-6
MANIFEST=out/manifest.json AGENT_BACKEND=codex AUTO_AGENT=1 MAX_ITERS=10 MAX_PARALLEL=3 PROVE_BUDGET=3600 make -C theme prove-fallback
make -C theme gate

# 1) 输入给定 PDF，跑主 pipeline（PDF -> tex -> yaml -> lean -> gate）
#    支持路径或关键词模糊匹配（优先匹配 theme/input/raw/*.pdf）
AGENT_BACKEND=codex make -C theme pdf-formalize PDF=lecture-6

# 2) 只针对“本次 pipeline 产物”自动证明（避免退回全量 backlog）
#    关键是传 MANIFEST=out/manifest.json（相对 make -C theme 的工作目录）
MANIFEST=out/manifest.json AGENT_BACKEND=codex AUTO_AGENT=1 MAX_ITERS=10 MAX_PARALLEL=3 PROVE_BUDGET=3600 make -C theme prove-fallback

# 3) 最终验收
make -C theme gate

# 4) 按目录检查产物（参考 theme/out/）
test -f theme/out/manifest.json && echo "ok: manifest.json"
test -f theme/out/prove_targets.json && echo "ok: prove_targets.json"
test -f theme/out/logs/pipeline.jsonl && tail -n 20 theme/out/logs/pipeline.jsonl
test -f theme/out/logs/gate_build.log && tail -n 20 theme/out/logs/gate_build.log

# 5) 查看本次是否真的新增写入 Lean 文件
# 说明：如果 manifest entries 全是 status=existing，表示条目已存在，pipeline 会去重，不会重复写入。
python3 - <<'PY'
import json
from collections import Counter
m = json.load(open("theme/out/manifest.json"))
c = Counter(e.get("status","unknown") for e in m.get("entries", {}).values())
print("status_count:", dict(c))
print("theorem_count:", m.get("theorem_count"), "pipeline_id_count:", m.get("pipeline_id_count"))
PY

# 6)（可选）快速看本次 pipeline 涉及的 Lean 文件
python3 - <<'PY'
import json
m = json.load(open("theme/out/manifest.json"))
files = sorted({e.get("file","") for e in m.get("entries", {}).values() if e.get("file")})
print("files_from_manifest:")
for f in files:
    print(" -", f)
PY

# resolve 时用 Codex 生成 sketch
python3 theme/scripts/resolve_concepts.py \
  --concepts "basu" --force-ai --ai-backend codex
```

> Codex 读取 `AGENTS.md` 获取项目指令（等价于 Claude 的 `CLAUDE.md`）。
>
> 关键点：`make -C theme formalize` 里的 `prove` 阶段只做目标选择（生成 `theme/out/prove_targets.json`），真正自动证明是 `make -C theme prove-fallback`。
>
> 若你要“只处理这次给定 PDF”，不要直接跑不带 `MANIFEST` 的 `prove-fallback`，否则会按全量 backlog 选目标。当前脚本会按 `manifest` 的 `(file, lean_name)` 精确筛选目标。

### 方式 D：纯手写 Lean

不需要任何工具链，直接写 Lean 证明。

```bash
vim Statlean/Information/CramerRao.lean
lake build Statlean.Information.CramerRao
```

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
| `from-tex` | LaTeX → theorems.yaml + notation.yaml + scope.yaml。**自动识别定理名**（heuristic 零 API，或 AI fallback） | 零~少量 |
| `resolve` | 概念名 → YAML（可选，`CONCEPTS=` 时触发） | 零 API |
| `ingest` | 解析 YAML | 零 |
| `plan` | 生成 plan.md | 零 |
| `generate` | YAML → Lean 骨架。按 `topic` 字段路由到 `Statlean/<Topic>/` 对应文件。未分类 → `Pipeline/<SourceTag>.lean` | 零 |
| `build-check` | `lake build` 验证骨架编译 | 零 |
| `sync-backlog` | 同步 sorry_backlog.yaml | 零 |
| `prove` | 生成 prove_targets.json（目标选择）；自动证明由 `prove-fallback` 调用 `claude/codex` | Max 额度 |
| `gate` | 最终 build + sorry 计数 + PIPELINE_ID 检查 + **auto-shelve**（自动入库零 sorry 模块到 Verified.lean） | 零 |

**API 消耗策略**：Pipeline 默认**零 API credit 消耗**。证明阶段可用 Claude/Codex agent（走对应 CLI 账号额度，不走 API credit）。只有 `--backend claude-api` 的 PDF 图片提取才用 API credit。

**参数**：

| 变量 | 默认 | 说明 |
|------|------|------|
| `AGENT_BACKEND` | `claude` | AI 后端：`claude` 或 `codex` |
| `CONCEPTS` | 空 | 概念名列表，逗号分隔 |
| `PDF` | 空 | PDF 文件路径或关键词（用于 `from-pdf` 提取） |
| `TEX` | `../output.tex` | LaTeX 文件路径（用于 `from-tex` 提取） |
| `MANIFEST` | 空 | manifest.json 路径。设置后 `prove-fallback` 只攻击该批次定理，不走全量 backlog |
| `PROVE_DEPTH` | `deep` | `deep` = 生成 prove 目标；`shallow` = 跳过 |
| `PROVE_BUDGET` | `3600` | prove 时间预算（秒） |
| `MAX_PARALLEL` | `3` | 最大并行 prove agent 数 |
| `NO_DEPS` | 空 | 设置后不展开概念依赖链 |

---

## 文件组织规则

### 按数学对象组织

```
Statlean/
  Gaussian/Basic.lean             # 标准高斯分布基础设施
  Gaussian/Poincare.lean          # Poincaré 不等式（已证 + sorry 共存）
  Variance/RaoBlackwell.lean      # Rao-Blackwell MSE 定理
  Sufficiency/Factorization.lean  # Fisher-Neyman 因子分解
  Estimator/Basic.lean            # 估计量基础（MSE 分解、风险支配）
  LimitTheorems/CLT.lean          # CLT 相关（pipeline 按 topic 自动路由）
  Pipeline/Lecture9Handout.lean   # 未分类定理（每 PDF 一个文件，待人工整理）
  ...
```

- 文件路径反映数学对象：`Gaussian/Poincare.lean`，不是 `Concentration/GaussianPoincare.lean`
- 已证引理和 sorry gap **放同一文件**，用 `section` 隔离
- 定理名语义化：`cramer_rao`，不是 `theorem_007`
- **Pipeline 路由**：`generate` 阶段按 ontology + 关键词把定理路由到对应子目录。无法分类的 → `Pipeline/<SourceTag>.lean`（每份 PDF 独立文件），后续可手动搬迁到正确位置

### Verified.lean

`Statlean/Verified.lean` 是零 sorry 模块的**索引文件**。它只包含 import 语句，不含任何定义。

```bash
# 验证所有 import 的模块无 sorry
lake build Statlean.Verified
# 应该零 sorry 警告
```

当你的文件达到零 sorry，把它加入 `Verified.lean`。或者跑 `make -C theme auto-shelve`（gate 中也会自动执行），它会扫描所有零 sorry 模块并自动更新 import。

### Statlean.lean

`Statlean.lean` 是全量 import（包含有 sorry 的模块）。新增 `.lean` 文件后在此添加 import。

---

## 验收标准

提交 PR 前确保：

1. **`lake build` 零错误**
2. **sorry 数不增加**（可以不减，但不能增加）
3. **`Verified.lean` 一致**：如果你的文件零 sorry，加入 Verified.lean
4. **PIPELINE_ID 保留**：生成的骨架中有 `PIPELINE_ID:` 注释，不要删除

```bash
# 验证清单
lake build                              # 零错误
lake build Statlean.Verified            # 零 sorry 警告
bash theme/scripts/gate.sh .            # 完整检查
```

---

## 提交流程

```bash
# 创建分支
git checkout -b feat/my-theorem

# 编辑、编译验证
lake build Statlean.MyModule

# 提交
git add Statlean/
git commit -m "feat: prove my_theorem (zero sorry)"
git push origin feat/my-theorem

# 开 PR
gh pr create --title "Prove my_theorem"
```

---

## Sorry 缺口清单

`theme/input/sorry_backlog.yaml` 记录了所有待攻击的 sorry，包含：
- **priority**：优先级（数字越小越重要）
- **blocker**：卡住的原因（缺什么 Mathlib API / 前置引理）
- **dependencies**：依赖其他哪些 sorry
- **unlocks**：证完后解锁哪些下游 sorry

**选择目标**：优先选 `type: honest`（路线清晰）且 `dependencies: []`（无前置依赖）的叶节点。

当前主要 blocker：
- **Measure.pi Fubini**：阻塞 EfronStein (2) + Poincaré 纤维化 (2)
- **Gaussian hypercontractivity**：阻塞 LogSobolev (2) + Herbst (1)
- **Stieltjes inversion**：阻塞 Berry-Esseen 通用常数 (1)

---

## FAQ

| 问题 | 回答 |
|------|------|
| 谁承担 token 费用？ | 你自己 — Claude Pro/Max 订阅或 API key |
| 最小贡献单位？ | 一个 sorry gap（一个子引理也算） |
| 如何避免冲突？ | 开始前检查 `sorry_backlog.yaml` 是否有人在做 |
| 部分进展可以 PR 吗？ | 可以 — 只要 sorry 数不增加 |
| 必须用 Claude 吗？ | 不必 — 可以用 Codex CLI（`AGENT_BACKEND=codex`）或手写 Lean 证明 |
| Lean 版本？ | 4.28.0-rc1（elan 自动管理） |
| Pipeline 是必须的吗？ | 不是 — 直接编辑 `.lean` 文件完全可以 |
| `theorems.yaml` 需要写 Lean 签名吗？ | 建议写 `lean_statement`，否则生成占位符需手动替换 |
| 定理名识别需要 API 吗？ | 不需要。Heuristic 匹配覆盖 ~70 个常见统计定理（CLT、δ-method 等），零 API 消耗。AI 只是可选增强 |
| `Pipeline/Lecture9Handout.lean` 是什么？ | 未能按主题分类的定理会放在 `Pipeline/<PDF名>.lean`。每份 PDF 独立一个文件，不会互相冲突。可以后续手动搬到正确目录 |
| auto-shelve 什么时候触发？ | `gate` 阶段自动触发。也可以手动跑 `make -C theme auto-shelve`。它会扫描零 sorry 模块并更新 Verified.lean / Statlean.lean |
| 多份 PDF 的 "Theorem 1" 会冲突吗？ | 不会。每份 PDF 有 source_tag 前缀（如 `lecture_9_handout.theorem.001.delta_method`），ID 唯一 |
