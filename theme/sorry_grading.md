# Sorry 等级分类 & 花费参考表

本文件记录 sorry 攻击的等级分类、预计时间、token 消耗。
**数据来源**：StatLean 项目实际攻击记录 + 经验估计。每次攻击后根据实际数据校准。

---

## 等级定义

| 等级 | 名称 | 典型特征 | 预计行数 | 预计时间 | 预计 Token |
|------|------|----------|---------|---------|-----------|
| **S** | 薄包装 | Mathlib 有现成 API，1-5 行桥接 | 1-5 | 2-5 min | 5K-20K |
| **A** | 组合式 | 需组合 2-3 个 Mathlib API，10-30 行 | 10-30 | 5-15 min | 20K-50K |
| **B** | 算术密集 | 数学清晰但 Lean 算术繁琐，30-80 行 | 30-80 | 15-40 min | 50K-100K |
| **C** | 结构性 | 需构造新抽象/分解证明结构，80-200 行 | 80-200 | 30-90 min | 100K-160K |
| **D** | 基础设施缺失 | Mathlib 缺关键 API，需自建 50-150 行 | 150-400 | 1-3 hr | 150K-300K |
| **E** | 研究级 | 数学本身有难度，路线不确定 | 200-700+ | 3-10+ hr | 300K-500K+ |

---

## 等级判定规则

### 快速判定流程（2 分钟内完成）

```
1. grep sorry 所在定理的 goal type
2. 在 theme/mathlib_api_index.md 搜关键词
3. 判定：
   - 搜到完全匹配的 API → S
   - 搜到 2-3 个可组合的 API → A
   - API 存在但需要 rpow/integral/sum 代数变换 → B
   - API 存在但需要新的中间引理结构 → C
   - 核心 API 不存在，需自建 → D
   - 数学路线本身不确定 → E
```

### 辅助指标

| 指标 | S | A | B | C | D | E |
|------|---|---|---|---|---|---|
| Mathlib API 覆盖 | 100% | 80-100% | 60-80% | 40-60% | <40% | <20% |
| 新引理数 | 0 | 0-1 | 1-3 | 3-8 | 5-15 | 10+ |
| 子 sorry 预期 | 0 | 0 | 0-1 | 1-3 | 2-5 | 5+ |
| 编译循环 | 1 | 1-2 | 2-4 | 3-5 | 5+ | 5-20+ |

---

## 实际攻击记录

### 2026-03-08 Convergence.lean 攻击

| 定理 | 等级 | 实际 Token | 实际时间 | 结果 | 备注 |
|------|------|-----------|---------|------|------|
| `kolmogorov_zero_one` | S | 95K | 16 min | ✅ 零 sorry | Mathlib ZeroOne.lean 直接调用；token 偏高因 agent 探索了等价性证明 |
| `multivariate_clt` | A | 141K | 20 min | ✅ 零 sorry | 修正了错误声明 + 3 helper + CLT 调用 |
| `lyapunov_implies_lindeberg` step2 | B | 157K | 22 min | ✅ 零 sorry | rpow 代数 + integral_mono；需添加 2 假设 |
| `kolmogorov_maximal_inequality` | C | 164K | 27 min | 1→1 sorry | first-crossing 结构完成，剩 cross-term 独立性 |
| `glivenko_cantelli` | C | 156K | 21 min | 1→1 sorry | SLLN 分解完成，剩 Dini 单调性 bootstrap |

### 历史记录

| 定理 | 等级 | 实际 Token | 实际时间 | 结果 |
|------|------|-----------|---------|------|
| `central_limit_theorem` (v24) | D | ~200K est. | ~2 hr | ✅ 零 sorry, 100 行 |
| `lindeberg_feller_clt` (v25) | D | ~300K est. | ~4 hr | ✅ 零 sorry, 690 行 |
| `levy_continuity` (v23) | D | ~250K est. | ~3 hr | ✅ 零 sorry, 260 行 |
| `factorization_forward` (v17) | C | ~150K est. | ~1.5 hr | ✅ 零 sorry |
| `condVar_le_condExp_gradf_sq_ae` (v19) | C | ~120K est. | ~1 hr | 1→2 sorry (Fubini) |
| Gaussian hypercontractivity | E | ~400K spent | ~6 hr | ❌ 未解决 (Nelson '73) |
| Stieltjes inversion | E | ~300K spent | ~4 hr | ❌ 未解决 (~150 行桥接) |

---

## 当前 Sorry 等级评估

| Sorry | 文件 | 等级 | 预计时间 | 预计 Token | Blocker |
|-------|------|------|---------|-----------|---------|
| `uniform_of_pointwise_on_rationals` | Convergence:433 | B-C | 30-60 min | 80-150K | CDF 右连续 + Dini |
| Kolmogorov cross-term independence | Convergence:689 | B | 20-40 min | 50-100K | iIndepFun.indepFun_finset |
| `levy_cdf_diff_fourier_bound` | BerryEsseen:693 | E | 5-10 hr | 300-500K | Stieltjes inversion |
| Gaussian LSI core | LogSobolev:339 | E | 5-10 hr | 300-500K | hypercontractivity |
| normalized LSI | LogSobolev:439 | C (blocked) | 30-60 min | 100-150K | 依赖 LSI core |
| 条件熵可积性 | LogSobolev:862 | C | 30-60 min | 80-120K | Fubini for Measure.pi |
| 张量化 | LogSobolev:1124 | D | 2-4 hr | 200-350K | entropy subadditivity |
| Herbst LSI | Herbst:77 | S (blocked) | 5 min | 10K | 等 LSI core |

---

## 校准说明

- Token 消耗包含 agent 的搜索、试错、编译循环（不只是最终证明代码）
- S 级理论上 5-10K，但 agent 探索路线会消耗额外 token
- 时间 = agent wall-clock time（含 lake build 等待）
- 每次攻击后，根据实际数据更新本表的预计值
- 如果某等级的实际数据连续 3 次偏离预计 >50%，调整该等级的预计范围
