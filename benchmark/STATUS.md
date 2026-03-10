# StatLean Benchmark 项目状态报告

**更新时间**: 2026-03-04
**阶段**: 第一阶段 — Benchmark + 数据闭环（2026-03-02 ~ 2026-04-30）
**状态**: 代码就绪，待首次实验运行

---

## 一、项目目标

系统比较闭源/开源 LLM 在 Lean 4 形式化证明任务上的效果、效率和成本，建立可复用的评测集与日志规范，为后续微调/蒸馏准备数据。

### 核心评估指标
| 指标 | 含义 |
|------|------|
| **Success rate** | `lake build` 通过 + sorry 消除的比例 |
| **Token / theorem** | 每个定理平均消耗 token |
| **Time / theorem** | 端到端平均耗时 |
| **Cost / theorem** | 按模型实际价格核算 |
| **Pass@k** | 同一目标 k 次尝试的成功率 |

---

## 二、架构概览

```
benchmark/
├── config/
│   ├── models.yaml                 # 10 个模型配置（5 家 provider）
│   ├── problems.yaml               # 18 道 benchmark 题目
│   └── skill_package/
│       ├── system_prompt.md         # Lean tactic 策略指南（61 行）
│       └── retry_template.md        # 编译错误重试模板（30 行）
├── harness/                         # 核心框架（6 个模块，~2,500 行）
│   ├── compiler.py                  # Lean 编译验证 + sorry 检测（437 行）
│   ├── runner.py                    # 实验编排 + 多轮重试逻辑（405 行）
│   ├── problem_extractor.py         # 题目提取：.lean → Problem 对象（349 行）
│   ├── model_adapter.py             # 多 provider 统一接口（338 行）
│   ├── metrics.py                   # 指标记录 + 聚合统计（333 行）
│   └── skill_builder.py             # tactic patterns + API 过滤注入（206 行）
├── scripts/                         # CLI 入口（3 个脚本，~810 行）
│   ├── run_benchmark.py             # 主 CLI：模型 × 题目 × 条件 × 重复
│   ├── extract_problems.py          # 题目提取与验证
│   └── generate_report.py           # Markdown / CSV 报告生成
├── tests/
│   └── test_regressions.py          # 回归测试（9 个 case，165 行）
└── results/
    ├── raw/                         # JSONL 原始结果（尚空）
    └── reports/                     # 生成的报告（尚空）
```

**总代码量**: ~3,500 行（harness 2,500 + scripts 810 + tests 165）

---

## 三、数据流

```
problems.yaml (18 题)
    │
    ▼
extract_problems.py ──► Problem 对象（statement + context + ground_truth）
    │
    ▼
run_benchmark.py (主 CLI)
    ├── for model in models
    ├── for problem in problems
    ├── for condition in [bare, skill]
    ├── for max_rounds in [1, 4]
    └── for repeat in [1..N]
        └── run_single_experiment()
            ├── build_prompt_for_problem()
            │   └── (if skill) build_skill_context() → patterns + APIs
            ├── adapter.generate(messages) → GenerateResult
            ├── extract_proof_from_response() → proof_body
            ├── compiler.check_proof() → CompileResult
            │   └── _target_uses_sorry() → 行号 + 名字双重检测
            ├── 记录 RoundMetrics
            └── if 失败 & round < max_rounds → append retry → 继续
        └── MetricsRecorder.record(RunResult) → JSONL
    │
    ▼
generate_report.py
    ├── 模型对比表（completion, cost, rounds）
    ├── 分轮次预算对比
    ├── 失败类型分布
    ├── 按难度成本分析
    ├── Skill 消融（bare vs skill）
    └── 重复实验置信区间
```

---

## 四、模型配置

### 闭源模型（7 个）

| 模型 | Provider | 输入价格 | 输出价格 | Max Tokens | 定位 |
|------|----------|----------|----------|------------|------|
| claude-opus-4.6 | Anthropic | $15.0/M | $75.0/M | 16384 | Anthropic 旗舰 |
| claude-sonnet-4.6 | Anthropic | $3.0/M | $15.0/M | 16384 | Anthropic 性价比 |
| claude-haiku-4.5 | Anthropic | $0.8/M | $4.0/M | 8192 | Anthropic 低成本 |
| gpt-5.2 | OpenAI | $1.75/M | $14.0/M | 16384 | OpenAI 旗舰 |
| o3 | OpenAI | $2.0/M | $8.0/M | 16384 | OpenAI 推理旗舰 |
| gemini-3.1-pro | Google | $2.0/M | $12.0/M | 16384 | Google 旗舰 |
| gemini-2.5-flash | Google | $0.15/M | $0.60/M | 16384 | Google 低成本 |

### 开源/API 模型（6 个）

| 模型 | Provider | 输入价格 | 输出价格 | Max Tokens | 定位 |
|------|----------|----------|----------|------------|------|
| deepseek-v3.2-chat | DeepSeek | $0.28/M | $0.42/M | 8192 | DeepSeek 通用 |
| deepseek-v3.2-reasoner | DeepSeek | $0.28/M | $0.42/M | 8192 | DeepSeek 推理 (CoT) |
| qwen3.5 | Alibaba | $0.40/M | $1.20/M | 8192 | Alibaba 旗舰 (397B MoE) |
| minimax-m2.5 | MiniMax | $0.30/M | $1.20/M | 8192 | MiniMax 旗舰 |
| llama-4-maverick | Meta/OpenRouter | $0.15/M | $0.60/M | 8192 | Meta 开源旗舰 |
| deepseek-prover-v2 | OpenRouter | $0.50/M | $2.18/M | 4096 | 证明专用 (Lean 4) |

---

## 五、题库（18 道）

### 按难度分布

| 难度 | 题数 | 平均证明行数 | 代表题目 |
|------|------|-------------|---------|
| Easy | 5 | ~22 | slutsky_div, gauss_markov, mse 分解, basu |
| Medium | 8 | ~56 | rao_blackwell, scheffe, delta_method, factorization |
| Hard | 4 | ~63 | uniform_slln, charfun_taylor, levy_continuity, lindeberg_feller |
| Open | 1 | — | esseen_concentration（Stieltjes 反演 blocker） |

### 完整题目清单

| # | Problem ID | Theorem | 难度 | 证明行数 | 数学领域 |
|---|-----------|---------|------|---------|---------|
| 1 | slutsky_div | slutsky_div | easy | 3 | 收敛性 |
| 2 | gauss_markov | gauss_markov | easy | 3 | 线性代数 |
| 3 | unbiased_risk_eq_variance | mse_eq_variance_of_unbiased | easy | 2 | 估计量 |
| 4 | mse_bias_variance | mse_eq_bias_sq_add_variance | easy | 2 | 估计量 |
| 5 | basu_theorem | basu_theorem | easy | 136 | 独立性 |
| 6 | rao_blackwell_mse | rb_mse_decomposition | medium | 5 | 条件期望 |
| 7 | scheffe | scheffe | medium | 63 | 收敛性 |
| 8 | delta_method | delta_method | medium | 119 | 收敛性 |
| 9 | levy_forward | levy_forward | medium | 2 | 收敛性 |
| 10 | condexp_reduces_mse | condExp_reduces_mse | medium | 108 | 条件期望 |
| 11 | factorization_backward | factorization_backward | medium | 89 | 可测性 |
| 12 | cramer_rao | cramer_rao | medium | 48 | 信息论 |
| 13 | minimal_sufficiency | minimalSufficient_of_densityRatio | medium | 38 | 充分性 |
| 14 | uniform_slln | uniform_slln | hard | 139 | 收敛性 |
| 15 | charfun_taylor | charfun_normalized_sum_bound | hard | 83 | 特征函数 |
| 16 | levy_continuity | levy_continuity | hard | 15 | 收敛性 |
| 17 | lindeberg_feller | lindeberg_feller_clt | hard | 16 | CLT |
| 18 | esseen_concentration | esseen_concentration_universal | open | 1 | Berry-Esseen |

---

## 六、实验设计

### 条件（Conditions）

| 条件 | 内容 | 目的 |
|------|------|------|
| **bare** | 仅给 theorem statement + imports + context | 纯模型能力基线 |
| **skill** | bare + tactic 策略表 + Mathlib API 索引 + 重试模板 | 测试知识注入增益 |

### 预算策略（Max Rounds）

| 策略 | Max Rounds | 含义 |
|------|-----------|------|
| single | 1 | 首轮命中率（first-pass rate） |
| multi | 4 | 允许 4 轮重试，测试错误恢复能力 |

### 实验矩阵

```
完整矩阵 = 13 models × 18 problems × 2 conditions × 2 budgets × N repeats
         = 936 × N 个实验单元

最小可行实验 = 3 models × 18 problems × 2 conditions × 1 budget × 3 repeats
             = 324 个实验单元
```

### 统计指标

| 指标 | 计算方式 | 含义 |
|------|---------|------|
| **completion_rate** | solved / total | 原始完成率 |
| **adjusted_completion_rate** | solved / (total - infra_failures) | 排除基础设施故障后的完成率 |
| **avg_cost_all_runs** | Σcost / total | 全量平均成本 |
| **avg_cost_solved_only** | Σcost(solved) / #solved | 成功样本平均成本（有幸存者偏差） |
| **expected_cost_per_success** | Σcost(all) / #solved | 每成功一次的期望成本（含失败尝试） |
| **first_pass_rate** | first_round_success / total | 首轮命中率 |
| **median_rounds** | median(rounds of solved) | 成功所需中位轮数 |

### 失败类型分类

| 类型 | 归因 | 从 adjusted 分母剔除？ |
|------|------|----------------------|
| SUCCESS | — | N/A |
| COMPILE_ERROR | 模型 | 否 |
| SORRY_REMAINING | 模型 | 否 |
| PARSER_ERROR | 模型（无法提取证明） | 否 |
| INFRA_ERROR | 基础设施（API 错误） | **是** |
| TIMEOUT | 基础设施（超时） | **是** |

---

## 七、代码质量审查记录

经过 4 轮代码审查（由独立 Claude 实例执行），所有发现的问题已修复：

### 已修复问题清单

| 轮次 | 严重度 | 问题 | 修复 |
|------|--------|------|------|
| v1 | 高 | `--single` 参数失效 | `extract_problems.py` 传入过滤列表 |
| v1 | 高 | snippet 模式默认导致假失败 | 默认改为 full lake build |
| v1 | 中高 | 其他 sorry 导致目标误判 | `_target_uses_sorry` 行号+名字双重检测 |
| v1 | 中 | 难度成本表占位 `"..."` | 改为真实数据生成 |
| v1 | 中 | run_id 秒级碰撞 | 时间戳 + uuid4[:8] |
| v1 | 低 | 0 值显示为 N/A | `is not None` 判断 |
| v1 | 低 | 行数硬编码窗口 | 扫描到下一声明 |
| v2 | 高 | repeat stats 漏 max_rounds | 分组键加 max_rounds |
| v2 | 中 | failure type 分类顺序冲突 | compile_success 最先判断 |
| v2 | 中 | 难度映射与运行时不一致 | 从 run 元数据读 config path |
| v2 | 低 | 注释数量 "OPEN (7)" 不准 | 更新为 "OPEN (3)" |
| v3 | 严重 | `adjusted_completion_rate` 高估 | parser_error 归为模型责任 |
| v3 | 高 | dry-run 多轮浪费 API | 单轮后 break |
| v3 | 中 | 单行证明 ground truth 丢失 | 提取 `:= by` 后 trailing proof |
| v3 | 中 | CSV difficulty 漏传 results | 传入 results 参数 |
| v4 | 高 | adjusted_completion 两表口径不一致 | 统一 infra_failures 定义 |
| v5 | 低 | `model_failures` 未使用变量 | 删除 |
| v5 | 低 | `(compilation skipped)` 死代码 | 删除 |

### 采样参数记录
所有 4 个 adapter（Claude、OpenAI、OpenAI-Compatible、Google）现在统一记录：
- `temperature`, `max_tokens`, `top_p`, `seed`, `provider`, `model_id`
- 不支持的参数记为 `None`

### 回归测试覆盖

| 测试类 | Case 数 | 覆盖内容 |
|--------|---------|---------|
| TestAdjustedCompletionConsistency | 3 | parser_error 不被剔除、infra_error 被剔除、混合场景 |
| TestClassifyFailure | 3 | 编译失败分类、成功分类、无编译结果分类 |
| TestSingleLineProofExtraction | 3 | `:= by trivial`、`:= by sorry`、多行证明 |
| **合计** | **9** | |

---

## 八、当前环境

| 项目 | 状态 |
|------|------|
| ANTHROPIC_API_KEY | ✅ 已设置 |
| OPENAI_API_KEY | ❌ 未设置 |
| GOOGLE_API_KEY | ❌ 未设置 |
| DEEPSEEK_API_KEY | ❌ 未设置 |
| DASHSCOPE_API_KEY | ❌ 未设置 |
| MINIMAX_API_KEY | ❌ 未设置 |
| OPENROUTER_API_KEY | ❌ 未设置 |
| `lake build` | ✅ 通过（7933 jobs） |
| `pytest` | ✅ 9/9 通过 |
| 实验结果 | ⬜ 尚未运行 |

---

## 九、下一步行动

### P0 — 立即（本周）
1. **Smoke test**: Haiku × 3 easy 题 × bare/skill × 2 rounds，验证全链路
2. **配置其他 API key**: OpenAI、Google、DeepSeek
3. **首批正式实验**: 3 闭源模型 × 18 题 × 2 条件 × 3 repeats

### P1 — 本月
4. **扩展到开源模型**: DeepSeek-v3、Qwen、本地小模型
5. **Token 优化实验**: prompt 压缩、检索裁剪、分阶段调用
6. **生成 benchmark 报告 v1**: 模型对比表 + 成本分析 + 难度校准

### P2 — 后续
7. **分层 ablation**: bare → +API index → +tactic patterns → full skill
8. **Holdout 题集**: 防止数据泄漏（改写/新编题目）
9. **数据 schema 定稿**: 为第二阶段（Web MVP）准备标准化输入输出格式

---

## 十、已知局限与风险

| 风险 | 影响 | 缓解措施 |
|------|------|---------|
| 题目来自公开仓库，可能被模型训练见过 | 测到记忆检索而非推理 | 后续加 holdout 题集 |
| 单次运行方差大 | 结论不稳定 | 默认 repeats ≥ 3 + 置信区间 |
| skill 条件注入维度过多 | 难以归因提升来源 | 分层 ablation |
| 难度标签为人工标注 | 可能与真实难度偏离 | 基于历史数据重标定 |
| 价格静态配置 | 跨期比较可能漂移 | 每 run 固化价格版本 |
| max_rounds 固定，token 预算未统一 | 长输出模型隐性获益 | 后续加 token budget 约束 |
