# 基础设施判定与分类方案

## 问题

当前 `classify.py` 只做 **关键词 → 文件** 的一维映射，不区分：
- definition vs theorem（`kind` 字段被忽略）
- 基础定义 vs 具体定理（completeness 和 Basu 定理走同一条路由）
- 独立可复用 vs 定理私有（ANOVA 和 EfronStein 的关系）

导致：completeness（基础定义）被塞进 Factorization.lean（具体定理文件）。

## 方案：两阶段分类

### 阶段 1：判定 kind → layer

```
kind = definition / structure / class / abbrev
  → layer = infra（基础设施）

kind = theorem / lemma / corollary / proposition
  → layer = theorem（默认）
  → 但如果 dependencies 为空 且 被 ≥2 个其他条目引用 → 升级为 infra
```

**基础设施的判定标准**（满足任一即可）：
1. `kind` 是 definition / structure / class
2. 数学上是教科书级定义（不是为某个证明专造的辅助定义）
3. 被同一 YAML 中 ≥2 个不同定理引用（通过 `dependencies` 字段检测）

### 阶段 2：infra 和 theorem 走不同路由

```
infra → <Topic>/Basic.lean    （基础定义层）
theorem → <Topic>/<Specific>.lean  （具体定理层）
```

具体映射：

| 关键词 | infra 路由 | theorem 路由 |
|--------|-----------|-------------|
| completeness, sufficiency, ancillary | Statistic/Basic.lean | — |
| factorization | — | Sufficiency/Factorization.lean |
| basu | — | Sufficiency/Basu.lean |
| gaussian, normal | Gaussian/Basic.lean | Gaussian/<Specific>.lean |
| variance, condVar | Variance/Basic.lean | Variance/<Specific>.lean |
| entropy, KL | Entropy/Basic.lean | Entropy/<Specific>.lean |

### 新的目录结构变更

```diff
 Statlean/
+  Statistic/
+    Basic.lean    # IsComplete, IsBoundedlyComplete, IsAncillary, IsSufficient (定义)
   Sufficiency/
-    Factorization.lean  # 定义 + 定理混在一起
+    Factorization.lean  # import Statistic.Basic, 只有 factorization 定理
+    Basu.lean           # import Statistic.Basic, 只有 Basu 定理
```

**关键原则**：`<Topic>/Basic.lean` 放定义，`<Topic>/<Theorem>.lean` 放定理。定理文件 import 定义文件，反向禁止。

## classify.py 改动

```python
def classify_theorem(
    title: str = "",
    namespace: str = "",
    statement: str = "",
    kind: str = "theorem",          # 新增参数
) -> Tuple[str, str]:
```

1. 先判定 `is_infra = (kind in {"definition", "structure", "class", "abbrev"})`
2. 关键词匹配确定 `topic`（如 "completeness" → topic = "Statistic"）
3. 如果 `is_infra`：返回 `(topic, "Basic")`
4. 如果非 infra：走现有路由逻辑

新增规则表：

```python
# 基础概念 → 独立 topic 的 Basic.lean
_INFRA_RULES = [
    (["completeness", "complete statistic", "ancillary", "sufficiency",
      "sufficient statistic", "minimal sufficient"], "Statistic"),
    (["exponential family", "natural parameter"], "ExpFamily"),
]

# 定理级 → 具体文件
_THEOREM_RULES = [
    (["factorization", "fisher.neyman"], "Sufficiency", "Factorization"),
    (["basu"], "Sufficiency", "Basu"),
    (["lehmann.scheff", "umvue"], "Sufficiency", "LehmannScheffe"),
    # ... 现有规则不变
]
```

## generate_project.py 改动

`theorem_block()` 当 `kind = definition` 时：
- 生成 `def` 而不是 `theorem`
- 不标 `PIPELINE_ID`（定义本身不需要证明）
- 但仍然标 `PIPELINE_ID` 如果 `lean_statement` 为空（需要人工填 Lean 签名）

```python
if kind == "definition":
    lines.append(f"def {lean_name} : Sorry := sorry  -- PIPELINE_ID: {tid}")
else:
    lines.append(f"theorem {lean_name} : {stmt} := by")
```

## theorems.yaml 改动

新增 `infra: true` 字段（可选，手动标记覆盖自动判定）：

```yaml
- id: lec4.completeness
  title: "Completeness of a Statistic"
  kind: definition         # ← 这是关键
  infra: true              # ← 可选，强制标记为基础设施
  lean_namespace: "Statlean.Statistic"  # ← 独立 topic，不是 Sufficiency
  lean_name: "IsComplete"
  keywords: ["completeness", "bounded completeness"]
  layer: statlib
```

## Pipeline 新增步骤：infra-audit

在 `generate` 之后、`gate` 之前新增：

```
make formalize  =  ingest → plan → generate → infra-audit → sync-backlog → gate
```

`infra-audit` 做的事：
1. 扫描生成的 skeleton，检查是否有 `kind: definition` 被路由到了非 `Basic.lean` 文件
2. 检查是否有 `Basic.lean` 中的定义没被任何 theorem 文件 import
3. 检查 import 方向：theorem 文件不应被 definition 文件 import
4. 输出警告，不阻塞（人工审查）

## 回到 completeness 的正确处理

```yaml
# theorems_lec4.yaml
- id: lec4.completeness
  title: "Completeness of a Statistic"
  kind: definition
  lean_namespace: "Statlean.Statistic"
  lean_name: "Statistic.IsComplete"
  lean_statement: |
    def Statistic.IsComplete {Ω β} [MeasurableSpace Ω] [MeasurableSpace β]
      (T : Ω → β) (P : Set (Measure Ω)) : Prop :=
    ∀ f : β → ℝ, Measurable f →
      (∀ μ ∈ P, ∫ x, f (T x) ∂μ = 0) →
        ∀ μ ∈ P, f ∘ T =ᵐ[μ] 0
  keywords: ["completeness"]
  layer: statlib
  dependencies: []

- id: lec4.bounded_completeness
  title: "Bounded Completeness of a Statistic"
  kind: definition
  lean_namespace: "Statlean.Statistic"
  lean_name: "Statistic.IsBoundedlyComplete"
  keywords: ["bounded completeness"]
  layer: statlib
  dependencies: []

- id: lec4.basu
  title: "Basu's Theorem"
  kind: theorem
  lean_namespace: "Statlean.Sufficiency"
  lean_name: "basu_theorem"
  keywords: ["basu", "ancillary", "complete sufficient"]
  layer: statlib
  dependencies: [lec4.completeness, lec4.bounded_completeness]
```

Pipeline 会：
- completeness → `Statistic/Basic.lean`（infra，kind=definition）
- Basu → `Sufficiency/Basu.lean`（theorem，import Statistic.Basic）
