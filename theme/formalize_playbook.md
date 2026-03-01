# Formalize Playbook — 交互式形式化操作手册

本文件是「会话内自然语言 → Lean 4 形式化」的**单一事实来源**。
Claude Code 和 Codex CLI 均遵循此协议。

适用场景：用户在会话中说「形式化 XX.pdf 里的 YY 定理/定义」。

---

## Checkpoint Log（强制）

**每完成一个 Step，必须追加一行到 `theme/out/formalize_checkpoint.jsonl`**。
这是验证 agent 是否遵循 playbook 的唯一机制。

```bash
# 格式（每行一个 JSON）：
echo '{"step":0,"status":"done","target":"MLE","pdf":"lecture-5-handout.pdf","ts":"'$(date -Iseconds)'"}' >> theme/out/formalize_checkpoint.jsonl
echo '{"step":1,"status":"done","math_content":"ℓ(θ)=f_θ(X), θ̂=argmax ℓ, invariance g(θ̂)","ts":"'$(date -Iseconds)'"}' >> theme/out/formalize_checkpoint.jsonl
echo '{"step":2,"status":"done","existing":"none","ts":"'$(date -Iseconds)'"}' >> theme/out/formalize_checkpoint.jsonl
echo '{"step":3,"status":"done","declarations":["likelihood","IsMLE","isMLE_comp"],"file":"Statlean/Estimator/Basic.lean","ts":"'$(date -Iseconds)'"}' >> theme/out/formalize_checkpoint.jsonl
echo '{"step":4,"status":"done","sorry_count":0,"ts":"'$(date -Iseconds)'"}' >> theme/out/formalize_checkpoint.jsonl
echo '{"step":5,"status":"done","build":"pass","errors":0,"warnings":0,"ts":"'$(date -Iseconds)'"}' >> theme/out/formalize_checkpoint.jsonl
echo '{"step":6,"status":"done","honesty_check":"pass","trivial_wrappers":0,"hidden_sorry":0,"ts":"'$(date -Iseconds)'"}' >> theme/out/formalize_checkpoint.jsonl
echo '{"step":7,"status":"done","imports_updated":true,"verified_updated":true,"ts":"'$(date -Iseconds)'"}' >> theme/out/formalize_checkpoint.jsonl
```

**验证脚本**（用户跑完后检查）：

```bash
python3 theme/scripts/check_formalize_log.py theme/out/formalize_checkpoint.jsonl
```

---

## 0. 输入解析

用户请求可能是：
- `形式化 lecture-5-handout.pdf 里的 MLE 概念`
- `把 lecture-9.pdf 第 3 页的 Theorem 2 形式化到 Lean`
- `形式化 Fisher Information 的定义`（不指定 PDF）

**提取三要素**：

| 要素 | 必须 | 示例 |
|------|------|------|
| PDF 路径 | 否（可能已有源码） | `theme/input/raw/lecture-5-handout.pdf` |
| 目标名称 | 是 | `MLE`、`Scheffé 定理`、`Fisher Information` |
| 粒度 | 隐含 | `概念` = 定义+相关定理；`定理` = 单个定理；`定义` = 仅定义 |

---

## 1. 获取数学内容

### 1a. 有 PDF 的情况

```bash
# 提取目标附近内容
python3 theme/scripts/pdf_extract.py <pdf> --theorem "<目标名>" [--pages <范围>]
```

- 读提取出的 `.md` 文件，找到目标定义/定理的**精确数学表述**
- 如果 pymupdf 丢失了公式框（常见于 beamer handout），用 `fitz` 直接提取对应页面文本
- **关键**：必须拿到完整的数学陈述（变量、条件、结论），不能靠猜

### 1b. 没有 PDF 的情况

- 如果用户描述足够精确（如「形式化 Cramér-Rao 下界」），直接从数学知识构建
- 如果不确定具体表述，**问用户**要精确定义或参考来源

---

## 2. 检查已有代码

**跳过此步 = 重复造轮子。**

```
1. grep -r "<关键词>" Statlean/ --include="*.lean"    # 看是否已有相关声明
2. 读 Statlean/Verified.lean                           # 看哪些模块已零 sorry
3. 读目标文件（如果已存在）                              # 了解已有 import 和 namespace
```

判断：
- **已有且完整** → 告诉用户「已存在于 X 文件」
- **已有但 sorry** → 转为 `/prove` 攻击
- **不存在** → 继续

---

## 3. 设计 Lean 签名

这是最关键的一步。**必须做对，否则后面全白费。**

### 3a. 读 Mathlib API 索引

```
读 theme/mathlib_api_index.md — 查找相关类型和 API
```

目标：确定用什么 Mathlib 类型建模。常见映射：

| 数学概念 | Lean/Mathlib 类型 |
|----------|------------------|
| 概率测度族 {P_θ} | `ParametricFamily Θ Ω`（项目自定义） |
| 概率密度 dP/dν | `μ.rnDeriv ν`（Radon-Nikodym） |
| 期望 E[X] | `∫ ω, X ω ∂μ` |
| 方差 Var(X) | `∫ ω, (X ω - ∫ ω', X ω' ∂μ)² ∂μ` 或 `variance X μ` |
| L² 可积 | `MemLp X 2 μ` |
| 可测函数 | `Measurable f` |
| 几乎处处 | `∀ᵐ ω ∂μ, ...` |
| σ-代数 | `MeasurableSpace` |
| 充分统计量 | `IsSufficient` 或 `IsSufficient'`（项目自定义） |
| MLE | `IsMLE`（项目自定义，在 Estimator/Basic） |
| 特征函数 | `charFun μ` |

### 3b. 确定文件位置

按 CLAUDE.md / AGENTS.md 的模块组织原则：
- 路径反映数学对象
- 检查是否已有合适文件（如 `Estimator/Basic.lean`）
- 没有则创建新文件（Mathlib-style 命名 + module docstring）

### 3c. 写签名

**原则**：
1. 签名必须精确反映数学内容——不多不少
2. 假设条件（`[IsProbabilityMeasure μ]`、`(hT : MemLp T 2 μ)` 等）必须充分
3. 结论必须是数学上正确的 Lean 类型
4. 如果需要辅助定义（如 `likelihood`），先定义再写定理

**反例**（必须避免）：
- 写 `Measurable (g ∘ θ_hat)` 冒充 MLE 不变性 → 这只是可测性合成，不是真正的数学内容
- 写 `True := by sorry` 占位 → 没有签名信息，等于没做

---

## 4. 写证明

### 4a. 定义（def）

- 直接写 Lean 表达式，不需要 sorry
- 确认类型正确（`lake build` 通过）

### 4b. 定理（theorem）

**优先尝试直接证明**（非 sorry）：

1. 如果是从已有 API 组合（如 MSE = Bias² + Var 就是 `integral_sub_const_sq_eq` 的改写），直接 `rw` / `simp` / `exact`
2. 如果需要多步推理，用 `calc` 或 `have` 链
3. 如果 3 轮内无法关闭，用 sorry 并在 docstring 中注明 blocker

**留 sorry 的规则**：
- sorry 必须有结构化注释：`-- sorry: <原因>, blocker: <什么挡住了>, effort: <估计工作量>`
- 注册到 `theme/input/sorry_backlog.yaml`

---

## 5. 编译验证

```bash
# 增量编译目标模块
lake build Statlean.<Module>
```

**循环修复**（最多 5 轮）：
1. 读错误信息
2. 修复（通常是：缺 import、类型不匹配、`simp` 参数错误）
3. 重新编译

### 常见编译问题速查

| 错误 | 原因 | 修复 |
|------|------|------|
| `unknown identifier` | 缺 import | 添加对应 Mathlib import |
| `type mismatch ... ENNReal / ℝ` | 类型域不对 | 用 `ENNReal.toReal` 或改返回类型 |
| `failed to synthesize instance` | 缺 typeclass | 添加 `[MeasurableSpace Θ]` 等 |
| `simp made no progress` | simp 参数不匹配目标形式 | 用 `rw` 代替，或检查 `simp only` 参数 |
| `Exists.choose` 不被 simp 重写 | 表达式形式不匹配 | 用 `subst` 统一变量，或用 `conv` 精确定位 |

---

## 6. 诚实性检查（必须）

**在报告给用户之前，自问**：

- [ ] 每个 `theorem` 的证明是否有实质数学内容？（不是 trivial composition / `rfl` / `exact id`）
- [ ] 如果用了 sorry，是否如实标注？
- [ ] 定义是否准确反映了数学概念？（不是薄封装）

**红线**：
- 不允许用 `Measurable (g ∘ f)` 冒充不变性定理
- 不允许省略关键假设让定理变 trivial
- 不允许隐藏 sorry（如 `by assumption` 实际依赖了不存在的假设）

---

## 7. 收尾

1. **更新 import 链**
   - `Statlean.lean`：确认有 import
   - `Verified.lean`：如果整个文件零 sorry → 更新描述

2. **更新 PIPELINE_ID**（如果是 pipeline 定理）
   - 在 module docstring 中添加 `PIPELINE_ID: <id>`

3. **向用户报告**
   - 列出所有新增声明、每个是否 sorry、关键证明技巧
   - 如果有 sorry → 说明 blocker 和建议的攻击方向

---

## 完整示例：「形式化 lecture-5-handout.pdf 里的 MLE 概念」

```
Step 0: 解析 → PDF=lecture-5-handout.pdf, 目标=MLE, 粒度=概念（定义+相关定理）

Step 1: 提取 PDF
  → pdf_extract.py --theorem "MLE"
  → 读 .md 文件，找到 Definition (p.7): ℓ(θ)=f_θ(X), θ̂ = argmax ℓ, 不变性 g(θ̂)

Step 2: 检查已有代码
  → grep "MLE\|likelihood\|IsMLE" Statlean/ → 无
  → 已有 ParametricFamily (Statistic/Basic)、Estimator/Basic (MSE 相关)

Step 3: 设计签名
  → 读 mathlib_api_index → rnDeriv 在 RadonNikodym 模块
  → 文件位置: Estimator/Basic.lean（已有 MSE section，MLE 是 estimator 概念）
  → 三个声明:
    1. def likelihood = rnDeriv (ENNReal 值)
    2. def IsMLE = Measurable θ̂ ∧ ∀ θ₀, a.e. ℓ(θ̂(ω)) ≥ ℓ(θ₀,ω)
    3. theorem isMLE_comp = g 单射可测 → g∘θ̂ 是重参数化族的 MLE

Step 4: 写证明
  → likelihood: 直接定义
  → IsMLE: 直接定义
  → isMLE_comp: 构造 P' on Set.range g, 用 subst + filter_upwards + simp

Step 5: lake build Statlean.Estimator.Basic → PASS (0 error, 0 warning)

Step 6: 诚实性检查
  → isMLE_comp 确实证明了不变性（不是 trivial composition）✓
  → 零 sorry ✓

Step 7: 收尾
  → Statlean.lean 已有 import ✓
  → Verified.lean 更新描述 ✓
  → 报告: 3 声明，0 sorry
```
