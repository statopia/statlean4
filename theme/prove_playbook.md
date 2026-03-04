# Prove Playbook — Lean 4 定理证明操作手册

本文件是 pipeline prove agent 和交互式 `/prove-deep` 的**单一事实来源**。
按决策树顺序执行，不需要人类介入。

---

## 1. 启动流程（每个 sorry 必须执行）

```
0. 用 python3 scripts/extract_signatures.py <file> 读声明索引（不读全文件）
   → 定位 sorry 所在定理的签名和行号，再 Read 指定行范围
1. 读 theme/tactic_patterns.yaml — 匹配 goal 形态，有匹配则优先使用
2. 读 theme/mathlib_api_index.md — 搜索相关 API（80% 命中率）
   补充：grep theme/mathlib_full_type_index.tsv 查全量 Mathlib 声明
3. 读 .claude/projects/*/memory/MEMORY.md — 查已知 pattern
4. 如果 backlog 有 proof_sketch / blocker — 按其指引走
5. 选择证明策略（见策略选择表）
6. 如果证明需要 >3 步 — 先分拆子引理
```

### Phase 0 工具链（强制使用）

| 工具 | 用途 | 用法 |
|------|------|------|
| `scripts/extract_signatures.py` | 读声明索引代替全文件 | `python3 scripts/extract_signatures.py <file>` |
| `theme/tactic_patterns.yaml` | 已验证的 tactic 模式库 | 攻击 sorry 前先查匹配 goal 的 pattern |
| `theme/mathlib_full_type_index.tsv` | 51K 条 Mathlib 声明索引 | `grep -i '<keyword>' theme/mathlib_full_type_index.tsv` |
| `scripts/check_snippet.sh` | 单 declaration 增量编译 | `bash scripts/check_snippet.sh <file> <start> <end>` |

**规则**：
- 大文件（>200 行）必须先用 extract_signatures，不盲读
- tactic_patterns.yaml 有匹配 → 直接用，省去探索循环
- 增量编译用 check_snippet.sh，全模块验证用 `lake build Statlean.<Module>`
- 证明成功后，新 pattern 在经验报告环节追加到 tactic_patterns.yaml

---

## 2. 策略选择表

根据定理类型选择证明路线：

| 定理类型 | 识别特征 | 策略 | 关键 API |
|----------|---------|------|----------|
| 不等式 `≥` / `≤` | `Var ≥ ...`, `∫ ... ≤ ∫ ...` | 正交分解 / completing-the-square / Cauchy-Schwarz | `integral_nonneg`, `sq_nonneg`, `inner_mul_le_norm_mul_nnorm` |
| a.e. 等式 `=ᵐ` | `condExp ... =ᵐ ...` | `ae_eq_of_forall_setIntegral_eq` + setIntegral 验证 | `ae_eq_condExp_of_forall_setIntegral_eq`, `setIntegral_condExp` |
| 唯一性 | `f =ᵐ g` from unbiased | 差 = 0 → 完备性/零测集 | `integral_sub`, `sub_self`, completeness |
| 因子分解 | `f = g ∘ T` | Doob-Dynkin | `Measurable.exists_eq_measurable_comp` |
| 积分等式 | `∫ f = ∫ g` | `integral_congr_ae` + tower/pullout | `integral_condExp`, `condExp_mul_of_aestronglyMeasurable_left` |
| 可积性 | `Integrable f μ` / `MemLp f p μ` | L^p chain: L² → L¹ via mono_exponent | `MemLp.mono_exponent`, `memLp_two_iff_integrable_sq` |
| 测度相等 | `μ = ν` on σ-algebra | π-λ / 单调类 | `ext_of_generate_finite` |
| 非负性 | `0 ≤ ∫ f` | `integral_nonneg` + pointwise bound | `sq_nonneg`, `mul_self_nonneg` |

---

## 3. API 搜索（三级法 — 必须逐级）

### Level 1：静态索引（0 成本，必须最先做）
```bash
# 读索引文件
Read theme/mathlib_api_index.md
# 搜索关键词：定理中出现的核心概念
# 例如：condExp, variance, integral, Measure.map, MemLp
```

### Level 2：精确查询（索引没有时用）
```bash
# 知道名字 → 查签名
echo '#check @MeasureTheory.condExp_sub' | lake env lean --stdin
# 不知道名字 → 自动搜索
# 在目标 sorry 处写 exact? 或 apply?，然后 lake build 看建议
```

### Level 3：grep 源码（前两级都失败时用）
```bash
# 限定目录搜索
Grep "condExp.*indicator" --path .lake/packages/mathlib/Mathlib/MeasureTheory/
Grep "setIntegral_condExp" --path .lake/packages/mathlib/Mathlib/
```

---

## 4. 编译错误修复表

遇到 `lake build` 报错时，按错误类型查表修复：

### 4.1 类型/模式匹配错误

| 错误信息 | 原因 | 修复 |
|----------|------|------|
| `rewrite failed: pattern not found` | lambda `fun ω => f ω - c` vs Pi.sub `f - (fun _ => c)` 形式不同 | 加 `have h_eq : (fun ω => ...) = ... := rfl` 然后 `rw [h_eq]`；或用 `change`/`show` 切换目标形式 |
| `type mismatch: expected M, got M'` 涉及 MeasurableSpace | `set m_T := MeasurableSpace.comap T _` 创建了局部 instance 覆盖全局 | **不要 `set m_T`**，inline 写 `MeasurableSpace.comap T ‹MeasurableSpace α›` |
| `integral_add` rewrite 失败 | `integral_add` 结果用 Pi.add，目标用 lambda | 用 `have h := integral_add ...` 然后 `linarith`，不 `rw` |
| `function expected at f, term has type ℝ` | `(f ^ 2) x ≠ f x ^ 2` | `simp only [Pi.pow_apply]` 或 `simp only [Pi.mul_apply]` |

### 4.2 标识符/实例错误

| 错误信息 | 原因 | 修复 |
|----------|------|------|
| `unknown identifier 'X'` | API 改名或不存在 | `#check @X` 查真名；`div_le_iff` → `div_le_iff₀` |
| `failed to synthesize instance SigmaFinite` | 需要 trim 的 SigmaFinite | `haveI : SigmaFinite (μ.trim hm) := inferInstance`（IsFiniteMeasure 自动推导） |
| `failed to synthesize instance IsProbabilityMeasure` | parametric family 需要显式声明 | `haveI : IsProbabilityMeasure (P.measure θ) := P.isProbability θ` |
| `failed to synthesize instance StandardBorelSpace` | Doob-Dynkin 需要 | `import Mathlib.MeasureTheory.Function.FactorsThrough` |

### 4.3 tactic 错误

| 错误信息 | 原因 | 修复 |
|----------|------|------|
| `simp made no progress` | simp lemma 不适用 | 换 `simp only [具体lemma]` 或用 `rw` |
| `linarith failed` | 缺少关键不等式前提 | 把需要的不等式用 `have` 提前证好，然后 `linarith [h1, h2, h3]` |
| `ring failed` | 涉及条件分支或非交换运算 | 用 `field_simp` 清理分式后再 `ring` |
| `exact? found no match` | Mathlib 没有这个 API | 升级到 Level 3 搜索，或自建引理 |

---

## 5. condExp 专项模式（本项目高频）

condExp 是本项目最常用的 API，专门列出常见套路：

| 需求 | API | 用法 |
|------|-----|------|
| condExp 线性 | `condExp_sub`, `condExp_add` | 返回 `=ᵐ`，用 `filter_upwards` 处理 |
| condExp 常数 | `condExp_const hm c` | 返回 `=`（非 ae），可直接 `rw` |
| condExp 自身 | `condExp_of_aestronglyMeasurable'` | 需要 `hm`, `AEStronglyMeasurable[m]`, `Integrable` |
| 拉出 m-可测因子 | `condExp_mul_of_aestronglyMeasurable_left` | 需要 PullOut import |
| tower property | `integral_condExp hm` | `∫ E[f\|m] dμ = ∫ f dμ` |
| setIntegral | `setIntegral_condExp hm hs` | `∫_s E[f\|m] dμ = ∫_s f dμ` for m-measurable s |
| L² 收缩 | `eLpNorm_condExp_le` | `‖E[f\|m]‖_p ≤ ‖f‖_p` |
| ae 唯一确定 | `ae_eq_condExp_of_forall_setIntegral_eq` | 对所有 m-可测集积分相等 → ae 等于 condExp |

**lambda vs Pi 陷阱**：`condExp_sub` 返回的 ae 等式中，减法是 `Pi.sub` 形式 (`f - g`)，
而你的目标可能是 lambda 形式 (`fun ω => f ω - g ω`)。处理方法：
```lean
-- 方法 1: 用 rfl 桥接
have h_eq : (fun ω => f ω - g ω) = f - g := rfl
rw [h_eq]
-- 方法 2: 用 change 切换目标形式
change μ[f - g|m] ω = ...
-- 方法 3: 用 filter_upwards 逐点处理（最通用）
filter_upwards [condExp_sub hf hg m] with ω hω
simp only [Pi.sub_apply] at hω
```

---

## 6. 执行循环

```
repeat (最多 5 轮):
  1. 写/修改证明代码
  2. lake build Statlean.<Module>
  3. 如果通过 → 检查 sorry 是否消除 → 完成
  4. 如果报错 → 查错误修复表(§4) → 修复 → 继续
  5. 每证完一个子引理 → 立即写入文件并验证（不攒到最后）

5 轮后仍未完成:
  → 记录已完成的部分（sub-lemma 留在文件中）
  → 记录失败原因和已尝试策略到 sorry_backlog.yaml
  → 退出，不无限重试

早期终止规则（/prove-deep agent 强制）:
  - 如果 agent 连续 3 轮无文件修改 → 立即 TaskStop
  - 如果 agent 运行 >15 min 且无文件修改 → 立即 TaskStop
  - 如果 sorry_backlog 标记 type: stuck + blocker 描述明确 → 不重复派 agent 攻击同一 sorry
  - 停止后记录 partial progress 到 sorry_backlog.yaml
```

---

## 6.5 维度缩减 / 子σ-代数任务预检（强制）

攻击涉及**乘积空间降维**或**子 σ-代数上的 condExp** 的 sorry 前，必须额外检查：

```
预检清单:
1. 目标是否涉及 ae_eq_condExp / condExp_of_aestronglyMeasurable'?
   → 是: 识别需要的 AEStronglyMeasurable[m] (m = 子σ-代数)
   → 预先规划 m-ae-sm 的构造路径（Doob-Dynkin? σ-algebra 交集恒等式?）
   → 将 m-ae-sm 作为独立 sub-lemma 先行证明

2. 是否需要 σ-algebra 交集/包含关系（如 sigmaAlgExcept i ⊓ sigmaAlgExcept j）?
   → 是: 这类基础设施需要 comap_iSup + comap_comp + biSup 改写
   → 预估 ~100 行，建议拆出独立辅助引理

3. 是否涉及 Function.update / restrict 映射?
   → 是: 检查 measurePreserving 和 variance_map 可用性
   → 确保 integrable_map_measure / memLp_map_measure_iff 签名匹配
```

**经验教训**：EfronStein dimension reduction 中，agent 完成了 95% 的证明（314 行），
但最后卡在 `AEStronglyMeasurable[M'] htil P'` — 因为 ambient-sm ≠ sub-σ-algebra-sm。
如果在启动 agent 前预检此项，可以节省整轮 agent 的 debug 时间。

---

## 7. 子引理分拆规则

当证明需要 >3 个 Mathlib API 链式调用时，先分拆：

```lean
-- 不要直接写一个 100 行的 proof
-- 拆成独立 have：

-- Sub-lemma 1: 可积性
have h_int : Integrable f μ := by ...

-- Sub-lemma 2: ae 等式
have h_ae : f =ᵐ[μ] g := by ...

-- Sub-lemma 3: 积分等式
have h_eq : ∫ f dμ = ∫ g dμ := by ...

-- 组合
linarith [h_int, h_ae, h_eq]
```

每个 sub-lemma 独立可验证。如果一个子引理卡住，其他已证的部分仍然有效。

---

## 8. 退出条件与失败记录

**成功退出**：sorry 消除 + `lake build` 通过

**失败退出**（5 轮无进展）：
1. 保留所有已完成的 sub-lemma（它们是有价值的进展）
2. 把失败信息写回文件的 sorry 注释：
```lean
  sorry
  -- prove_attempt: strategy=orthogonal_decomposition, rounds=5
  -- stuck_at: cross term vanishing needs condExp_mul_of_aestronglyMeasurable_left
  -- missing_api: none identified
```

**绝对不做**：
- 删除别人的证明或修改其他定理
- 把 sorry 换成 `sorry` 的变体（如 `native_decide` hack）
- 修改定理签名来逃避证明
