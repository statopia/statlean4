# Theme: LaTeX → Lean Formalization Pipeline

本目录包含 StatLean 的自动化 pipeline：从 PDF/LaTeX 到 Lean 4 形式化。

## 目录结构

```
theme/
  input/                     # 输入文件
    raw/                     # 原始 PDF + 提取的 markdown（gitignored）
    paper.tex                # from-pdf 提取的 LaTeX
    theorems.yaml            # from-tex 提取的定理列表
    notation.yaml            # 符号映射
    sorry_backlog.yaml       # sorry 缺口清单
  scripts/                   # Pipeline 脚本
    pdf_extract.py           # PDF → markdown (pymupdf)
    from_tex.py              # LaTeX → theorems.yaml（含定理名 heuristic 识别）
    generate_project.py      # YAML → Lean 骨架
    classify.py              # 定理分类路由（ontology + 关键词规则）
    gate.sh                  # 验收门（build + sorry count + PIPELINE_ID）
    auto_shelve.py           # 自动入库零 sorry 模块到 Verified.lean
    sync_sorry_backlog.py    # 同步 sorry_backlog.yaml
    prove_loop.sh            # prove 循环（调用 claude/codex agent）
    prove_select_targets.py  # 选择 prove 目标
    check_formalize_log.py   # 验证 formalize playbook checkpoint
  out/                       # Pipeline 输出（gitignored）
    manifest.json            # 生成清单
    prove_targets.json       # prove 目标列表
    logs/                    # 日志
  tests/                     # 测试脚本
  mcp/                       # Codex MCP 配置
  Makefile                   # 一键 pipeline 入口
  formalize_playbook.md      # 交互式形式化 SOP（7 步）
  prove_playbook.md          # 证明操作手册
  mathlib_api_index.md       # Mathlib API 索引（650+ 条）
  PIPELINE.md                # Pipeline 详细设计文档
```

## 一键 Pipeline

```bash
# 从 PDF 到 gate（最常用）
make -C theme pdf-formalize PDF=lecture-9-handout.pdf

# 从 LaTeX 开始
make -C theme tex-formalize TEX=./output.tex

# 从已有 YAML 开始
make -C theme formalize
```

## Pipeline 阶段

```
PDF → (from-pdf) → LaTeX → (from-tex) → theorems.yaml
  → generate → build-check → sync-backlog → prove → gate → auto-shelve
```

| 阶段 | 做什么 | 消耗 |
|------|--------|------|
| `from-pdf` | PDF → LaTeX（pymupdf 本地提取） | 零 |
| `from-tex` | LaTeX → theorems.yaml（heuristic 定理名识别，零 API） | 零 |
| `generate` | YAML → Lean 骨架，按 topic 路由到 `Statlean/<Topic>/` | 零 |
| `prove` | 生成 prove_targets.json；`prove-fallback` 调用 agent | Max 额度 |
| `gate` | build + sorry count + PIPELINE_ID + auto-shelve | 零 |

## Make Targets

| Target | 说明 |
|--------|------|
| `pdf-formalize` | PDF → gate 全流程 |
| `tex-formalize` | LaTeX → gate |
| `formalize` | YAML → gate |
| `from-pdf` | PDF → LaTeX |
| `from-tex` | LaTeX → YAML |
| `prove-fallback` | prove 循环 |
| `gate` | 验收门 |
| `auto-shelve` | 自动入库零 sorry 模块 |

## 参数

| 变量 | 默认 | 说明 |
|------|------|------|
| `AGENT_BACKEND` | `claude` | `claude` 或 `codex` |
| `PDF` | 空 | PDF 路径或关键词 |
| `TEX` | `../output.tex` | LaTeX 路径 |
| `MANIFEST` | 空 | 限定 prove 攻击范围 |
| `PROVE_BUDGET` | `3600` | prove 时间预算（秒） |
| `MAX_PARALLEL` | `3` | 最大并行 agent 数 |
| `AUTO_AGENT` | `1` | 是否自动调用 agent |

## 双后端对比

| 特性 | Claude Code | Codex CLI |
|------|------------|-----------|
| CLI | `claude -p "..."` | `codex exec --full-auto "..."` |
| 项目指令 | `CLAUDE.md` | `AGENTS.md` |
| 认证 | Max 订阅 | ChatGPT Plus/Pro 或 `OPENAI_API_KEY` |
| Playbook 遵循 | 隐式（CLAUDE.md 引用） | 显式（prompt 中要求读 playbook） |

## 验收门 (gate.sh)

```bash
make -C theme gate
```

检查项：
1. `lake build` 零错误
2. sorry 计数
3. PIPELINE_ID 覆盖率
4. auto-shelve（零 sorry 模块自动入库 Verified.lean）

## Troubleshooting

**Claude backend**:
- `claude --version` 确认安装
- 检查 Max 订阅状态

**Codex backend**:
- `codex exec "ping"` 确认连接
- `bash theme/mcp/register_codex.sh` 注册 MCP
- `codex mcp list --json` 验证
