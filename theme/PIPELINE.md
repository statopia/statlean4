# StatLean Pipeline：PDF → Lean 4 证明

## 总览

```
PDF ─→ LaTeX ─→ YAML ─→ Lean骨架 ─→ 证明 ─→ 验收
       extract   ingest   generate   prove    gate
```

---

## 阶段 1: Extract（PDF → LaTeX）

```bash
make from-pdf PDF=lecture.pdf
```

- 用 Claude 或 MinerU OCR 把 PDF 转成 `paper.tex`
- 输出到 `theme/input/` 目录

## 阶段 2: Ingest（LaTeX → 结构化 YAML）

```bash
make from-tex TEX=paper.tex
```

- 扫描 `\begin{theorem}...\end{theorem}` 等 LaTeX 环境
- 用 `notation.yaml` 标准化宏（`\mathbb{E}` → `𝔼`）
- 输出 `theorems.yaml`：每个定理有 ID、依赖、优先级、LaTeX 语句和证明提示

### 输入文件

| 文件 | 用途 |
|------|------|
| `theme/input/notation.yaml` | LaTeX 宏 → Lean 标识符映射（~50 条） |
| `theme/input/scope.yaml` | 项目边界：包含/排除哪些定理、质量约束 |
| `theme/input/theorems.schema.yaml` | theorems.yaml 的 JSON Schema 校验 |

### theorems.yaml 结构

```yaml
theorems:
  - id: imported.theorem.001.uslln_c
    title: USLLN, C
    kind: theorem          # theorem/lemma/corollary/proposition/definition
    latex_statement: '...'
    latex_proof_hint: '...'
    lean_name: theorem_001_uslln_c
    lean_namespace: Statlean.Concentration
    layer: formalization   # statlib（可复用）或 formalization（项目级）
    priority: 3            # 1-5，1 最高
    dependencies: [...]
```

## 阶段 3: Plan + Generate（YAML → Lean 骨架）

```bash
make formalize   # = ingest → plan → generate → sync-backlog → gate
```

### 3a. Plan

- 分析定理数量、依赖关系、检测重复 ID
- 输出 `theme/out/plan.md`

### 3b. Generate

- `classify.py` 按关键词路由定理到正确目录
  - Poincaré → `Statlean/Gaussian/Poincare.lean`
  - Rao-Blackwell → `Statlean/Variance/RaoBlackwell.lean`
  - ~50 条路由规则
- 生成 Lean 骨架：声明 + `sorry` 占位证明
- 空语句/证明标记 `PIPELINE_ID: <id>`（需人工补全）

### 3c. Sync Backlog

```bash
make sync-backlog
```

- `sync_sorry_backlog.py` 扫描所有 `.lean` 中的 sorry
- 与 `sorry_backlog.yaml` 对账：
  - 已有 sorry → 更新行号，保留人工标注（blocker、priority）
  - 新增 sorry → 加入，type=unknown, priority=99
  - 已消除 sorry → 从 backlog 删除
- 重建依赖 DAG

### sorry_backlog.yaml 结构

```yaml
version: v17
total_sorry: 11
sorry_items:
  - id: lsi.hypercontractivity
    file: Statlean/Gaussian/Poincare.lean
    theorem: memLp_four_of_W12_gaussian
    type: honest           # honest/blocked/proved_modulo
    priority: 3
    blocker: "Nelson hypercontractivity"
    dependencies: [...]
    unlocks: [...]
```

## 阶段 4: Gate（编译验收）

```bash
make gate
```

按顺序检查：

1. **`lake build`** — 必须通过（失败则中止）
2. **sorry 计数** — 统计 `\bsorry\b` 行数（信息性）
3. **PIPELINE_ID 标记** — 未解决的占位符数量
4. **axiom 计数** — 公理声明数量

输出：`theme/out/logs/gate_build.log` + `pipeline.jsonl`

## 阶段 5: Prove（攻击 sorry）

### 交互模式（Claude Code）

```
/prove-deep all-leaves
```

- 从 `sorry_backlog.yaml` 读取 DAG，从叶节点开始攻击
- 最多 **3 个并行 agent** 同时攻击独立 sorry
- 每个 agent **实时写文件**，完成后主会话检查续派
- 攻击顺序：B（路线清晰）> A（缺 Mathlib API）> C（依赖未解决 sorry）
- 上下文满时自动保存（sorry_backlog.yaml + MEMORY.md + commit）

### CI 模式（无人值守）

```bash
make prove-fallback
```

- `prove_loop.sh`：最多 3 轮迭代，每轮 ≤3 并行 agent，600s 超时
- 适用于 Docker/CI 环境

### 两种模式对比

| | 交互模式（Claude Code） | CI 模式 |
|---|---|---|
| 入口 | `/pipeline` 或 `/prove-deep` | `make prove-fallback` |
| 证明引擎 | Claude agent（≤3 并行） | Claude agent（≤3 并行，600s 超时） |
| 状态恢复 | `MEMORY.md` + `sorry_backlog.yaml` | `sorry_backlog.yaml` only |
| 灵活度 | 高（手动分解、调策略） | 低（固定 3 轮迭代） |

## 阶段 6: Verified（入库）

- 零 sorry 的文件加入 `Statlean/Verified.lean`
- `lake build Statlean.Verified` 零警告
- commit + push

---

## 快速命令

```bash
# 端到端：PDF → 证明
make pdf-formalize PDF=paper.pdf

# 端到端：LaTeX → 证明
make tex-formalize TEX=paper.tex

# 只生成骨架（不证明）
make formalize

# 只跑 gate 检查
make gate

# 刷新 Mathlib API 索引（Mathlib 升级后）
make refresh-index
```

## 目录结构

```
theme/
  Makefile                    # Pipeline 编排
  input/
    theorems.yaml             # 定理定义（核心输入）
    notation.yaml             # LaTeX 宏映射
    scope.yaml                # 项目边界约束
    sorry_backlog.yaml        # sorry 追踪（自动同步）
    theorems.schema.yaml      # YAML schema 校验
    raw/                      # PDF 提取的原始文本
  out/
    plan.md                   # 依赖分析报告
    input_snapshot/           # 输入快照（审计）
    logs/
      pipeline.jsonl          # 逐阶段状态日志
      gate_build.log          # lake build 完整输出
  scripts/
    ingest.sh                 # 阶段 1: 输入校验
    plan.sh                   # 阶段 3a: 依赖分析
    generate.sh               # 阶段 3b: 骨架生成
    generate_project.py       # generate.sh 的 Python 后端
    classify.py               # 定理 → 文件路由
    sync_sorry_backlog.py     # 阶段 3c: sorry 对账
    gate.sh                   # 阶段 4: 编译验收
    prove_loop.sh             # 阶段 5 (CI): 证明循环
  skills/
    latex-ingest/             # /pipeline 的 ingest 技能
    lean-skeleton/            # /pipeline 的 skeleton 技能
    proof-closure/            # /pipeline 的 prove 技能
    boundary-check/           # /pipeline 的 gate 技能
    statlib-promoter/         # 基础设施提升技能
```
