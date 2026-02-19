# StatLean 复现工作交接（2026-02-19）

## 1. 目标与约束
- 目标：复现 arXiv:2602.02285（*Statistical Learning Theory in Lean 4: Empirical Processes from Scratch*）的核心理论链条。
- 约束：不参考论文官方 GitHub 实现代码，只基于论文文本、Mathlib、当前仓库已有代码推进。

## 2. 本次会话已完成的上下文收集
- 已阅读论文 PDF：`https://arxiv.org/pdf/2602.02285`
- 已下载并查看论文源码（比 PDF 更适合对齐定理签名）：
  - `https://arxiv.org/e-print/2602.02285`
  - 关键文件：
    - `/tmp/main/pathway.tex`（主线定理与 Lean 签名）
    - `/tmp/app/docs.tex`（作者列出的关键 formal results）
    - `/tmp/app/leancode.tex`（Least Squares 关键定理完整 Lean 签名）

## 3. 当前仓库状态
- 构建状态：`lake build` 通过（2871 jobs）。
- 入口文件：`Statlean.lean` 已串联三大模块（Concentration / EmpiricalProcess / Regression）。
- `RaoBlackwell_MSE` 模块已是完整证明链（非 skeleton）：
  - MSE 版本：`decomposition / pythagorean / reduction / gap / equality` 全套
  - Variance 版本：`rb_variance_decomposition / rb_variance_reduction / rb_variance_gap_eq_condVar / rb_variance_reduction_eq_iff_condVar_zero`
  - measurability 等价情形（`stronglyMeasurable` 与 `measurable`）已补齐
  - 新增复用引理：`condVar_integral_nonneg`（消除多处重复非负性证明）

## 4. 本次会话新增代码推进
- 新增并验证：
  - `Statlean/EmpiricalProcess/CoveringNumber.lean:67`
    - `coveringNumber_lt_top_of_totallyBounded`
  - `Statlean/EmpiricalProcess/CoveringNumber.lean:85`
    - `coveringNumber_lt_top_of_isCompact` 现在直接复用上面结果
- 占位清理（接口固定）：
  - `Statlean/Concentration/*`
    - `EfronStein / GaussianPoincare / Density / LogSobolev / GaussianLipschitz` 中的全局 axiom 已全部去除
    - 统一改为“定理参数化假设”输入形式（不引入全局公理）
    - 新增可复用桥接（减少假设表达冗余）：
      - `EfronStein`：
        - `efron_stein` 现改为由 `condVar` 求和形式推导 integral 形式
          （复用 `efron_stein_of_condVar_sum_bound`）
        - `efron_stein_of_condVar_sum_bound`
        - `efron_stein_to_condVar_sum_bound`
        - `efron_stein_iff_condVar_sum_bound`
        - 兼容壳：`efron_stein_of_integral_bound`
      - `GaussianPoincare`：
        - `gaussian_poincare` 现改为由 `condVar` 求和 + 坐标控制推导
          （复用 `gaussian_poincare_of_condVar_sum`）
        - `gaussian_poincare_of_efron_stein`
        - `gaussian_poincare_of_condVar_sum`
        - 兼容壳：`gaussian_poincare_of_integral_bound`
      - `LogSobolev`：
        - 新增接口定义：`TensorizationLSIAt / UniversalTensorizationLSI`
        - 新增 regularity 打包：`GaussianSobolevRegularity`
        - 新增桥接：`tensorization_lsi_of_at / tensorization_lsi_at_of_universal`
        - 新增推导：`gaussian_log_sobolev_of_tensorization_at / gaussian_log_sobolev_of_universal_tensorization`
        - 新增 structured 入口：
          - `gaussian_log_sobolev_structured_of_tensorization_at`
          - `gaussian_log_sobolev_structured_of_universal_tensorization`
        - `tensorization_lsi` 已从高阶函数参数改为直接接收
          `TensorizationLSIAt n c`
        - `gaussian_log_sobolev` 已从高阶函数参数改为直接接收
          `UniversalTensorizationLSI`
      - `GaussianLipschitz`：
        - 新增接口定义：`HerbstBound / UniversalHerbstBound`
        - 新增桥接：`herbst_argument_of_bound`
        - `herbst_argument` 已改为直接使用 `HerbstBound`（不再逐点 `s` 传入）
        - `gaussian_lipschitz_upper_tail / gaussian_lipschitz_concentration`
          的 Herbst 前提已结构化为 `HerbstBound`
        - 新增统一入口：
          - `gaussian_lipschitz_upper_tail_of_universal_herbst`
          - `gaussian_lipschitz_concentration_of_universal_herbst`
      - 作用：把“条件方差求和形式 / Efron-Stein 形式 / 坐标控制形式”串成可组合链条
  - `Statlean/EmpiricalProcess/Dudley.lean`
    - `dudley_entropy_integral` 已从 `True` 占位改成真实不等式签名
    - general-case 签名已对齐到 `E[sup]` 结构，并显式包含 `TotallyBounded / measurable / exp-integrability / path continuity`
    - `Dudley` 模块中全局 axiom 已去除，改为“定理参数化假设”形式
  - `Statlean/Regression/MasterBound.lean`
    - `master_error_bound` / `capacity_control` 已从 `True` 占位改成真实不等式签名
    - 新增 `approximationError / estimationErrorUpper / uniformDeviation` 接口定义
    - 新增局部化接口定义：`shiftedClass / IsStarShapedClass / empiricalNorm / localizedBall / empiricalSphere / empiricalMetricImage / LocalGaussianComplexity / satisfiesCriticalInequality`
    - `master_error_bound` 现为可证明版本（使用 `hf_star` + `hInt` 技术假设），不再依赖 axiom
    - `capacity_control` 现为可证明版本（使用 `F.Nonempty` + pointwise 假设），不再依赖 axiom
    - 新增 `master_error_bound_localized / local_gaussian_complexity_bound / master_error_bound_probability_interface`（论文风格假设接口）
    - 新增 critical-inequality 组装引理：
      - `satisfiesCriticalInequality_of_localGaussianComplexity_le`
      - `satisfiesCriticalInequality_of_proxy_bound`
    - 新增 proxy 驱动桥接：
      - `master_error_bound_localized_of_proxy_critical`
      - `master_error_bound_full_interface_of_proxy_critical`
    - 新增“结构化假设”层，减少重复参数串：
      - `LocalGaussianComplexityProxyAssumptions`
      - `LocalGaussianComplexityEntropyAssumptions`
      - `LocalizedProcessAssumptions`
      - `LocalizedDeterministicAssumptions`
      - `LocalizedProxyCriticalAssumptions`
      - `LocalizedProbabilityAssumptions`
    - 新增结构互转引理：
      - `LocalizedDeterministicAssumptions.toProcess`
      - `LocalizedDeterministicAssumptions.ofProcessAndCI`
    - 新增结构化入口 theorem：
      - `master_error_bound_localized_structured`
      - `master_error_bound_localized_of_proxy_structured`
      - `master_error_bound_localized_of_process_and_complexity_structured`
      - `master_error_bound_localized_of_process_and_entropy_structured`
      - `master_error_bound_probability_interface_structured`
      - `master_error_bound_full_interface_structured`
      - `master_error_bound_full_interface_of_proxy_structured`
      - `master_error_bound_full_interface_of_process_and_complexity_structured`
      - `master_error_bound_full_interface_of_process_and_entropy_structured`
    - 新增结构化构造器：
      - `LocalizedProxyCriticalAssumptions.ofProcessAndComplexity`
      - `LocalizedDeterministicAssumptions.ofProcessAndComplexity`
      - `LocalizedProbabilityAssumptions.ofProxy`
      - `LocalizedProbabilityAssumptions.ofDeterministic`
      - `LocalizedProbabilityAssumptions.ofProcessAndComplexity`
      - `LocalizedProbabilityAssumptions.ofProcessAndEntropy`
      - `LocalGaussianComplexityProxyAssumptions.ofEntropy`
      - `dudleyEntropyUpper_le_estimationErrorUpper_of_entropyIntegral_le_Msq`
      - 作用：从 `LocalizedProcessAssumptions + LocalGaussianComplexityProxyAssumptions + hScale`
        自动生成 `LocalizedProxyCriticalAssumptions`
      - 作用：从 `LocalGaussianComplexityEntropyAssumptions` 自动生成
        `LocalGaussianComplexityProxyAssumptions`
      - 作用：从 `LocalizedProxyCriticalAssumptions + hf_hat + hProb` 自动生成概率侧结构化假设
    - `master_error_bound_full_interface_of_process_and_complexity_structured`
      与 `master_error_bound_full_interface_of_process_and_entropy_structured`
      已改为先构造 `LocalizedProbabilityAssumptions`，再统一复用
      `master_error_bound_full_interface_structured`
    - `master_error_bound_localized_of_process_and_entropy_structured`
      已改为先构造 `LocalizedDeterministicAssumptions.ofProcessAndEntropy`
      再统一复用 `master_error_bound_localized_structured`
    - `LocalizedProbabilityAssumptions.ofProcessAndEntropy`
      已改为先构造 `LocalizedDeterministicAssumptions.ofProcessAndEntropy`
      再统一复用 `LocalizedProbabilityAssumptions.ofDeterministic`
    - `master_error_bound_localized_of_process_and_complexity_structured`
      已改为先构造 `LocalizedDeterministicAssumptions.ofProcessAndComplexity`
      再统一复用 `master_error_bound_localized_structured`
    - `master_error_bound_full_interface_structured` 现改为组合式实现：
      - deterministic 分支复用 `master_error_bound_localized_structured`
      - probability 分支复用 `master_error_bound_probability_interface_structured`
  - `Statlean/Regression/Linear.lean`
    - `linear_regression_rate` / `l1_ball_covering_maurey` / `l1_regression_rate` 已从 `True` 占位改成真实签名
    - 新增 `l1Ball` 定义
    - `l2_ball_covering_number_axiom` 已移除，`l2_ball_covering_number` 现为可证明弱形式（存在有限上界）
    - `Linear` 模块中原有 rate 相关 axiom 已改为“定理参数化假设”形式（不再引入全局 axiom）
    - 新增可组合 bridge：
      - `linear_regression_rate_of_master_bound`
      - `l1_regression_rate_of_master_bound`
      - 作用：把 `master_error_bound` 的代理误差项通过 `hScale` 自动传递到目标 rate
    - 新增 structured 直连版本（直接接 `LocalizedProxyCriticalAssumptions`）：
      - `linear_regression_rate_of_proxy_structured_master_bound`
      - `l1_regression_rate_of_proxy_structured_master_bound`
    - 新增 structured 全接口版本（同时给出 `rate + probability`）：
      - `linear_regression_full_interface_of_proxy_structured_master_bound`
      - `l1_regression_full_interface_of_proxy_structured_master_bound`
    - 新增通用抽象（减少线性/ℓ₁重复）：
      - `regression_rate_of_master_bound`
      - `regression_rate_of_deterministic_structured_master_bound`
      - `regression_rate_of_proxy_structured_master_bound`
      - `regression_full_interface_of_probability_structured_master_bound`
      - `regression_full_interface_of_proxy_structured_master_bound`
      - `regression_rate_of_process_and_complexity_structured_master_bound`
      - `regression_full_interface_of_process_and_complexity_structured_master_bound`
      - `regression_rate_of_process_and_entropy_structured_master_bound`
      - `regression_full_interface_of_process_and_entropy_structured_master_bound`
      - `linear_regression_rate_of_deterministic_structured_master_bound`
      - `l1_regression_rate_of_deterministic_structured_master_bound`
      - `linear_regression_full_interface_of_probability_structured_master_bound`
      - `l1_regression_full_interface_of_probability_structured_master_bound`
    - `linear_regression_rate_of_proxy_structured_master_bound` 与
      `l1_regression_rate_of_proxy_structured_master_bound`
      已统一复用 `regression_rate_of_proxy_structured_master_bound`
    - `regression_rate_of_process_and_complexity_structured_master_bound` /
      `regression_rate_of_process_and_entropy_structured_master_bound`
      已改为先构造 `LocalizedDeterministicAssumptions`，再统一复用
      `regression_rate_of_deterministic_structured_master_bound`
    - `regression_full_interface_of_proxy_structured_master_bound` /
      `regression_full_interface_of_process_and_complexity_structured_master_bound` /
      `regression_full_interface_of_process_and_entropy_structured_master_bound`
      现统一走 `regression_full_interface_of_probability_structured_master_bound`
      （先构造 `LocalizedProbabilityAssumptions` 再做 rate transfer）
    - 新增 process+complexity 直连全接口：
      - `linear_regression_full_interface_of_process_and_complexity_structured_master_bound`
      - `l1_regression_full_interface_of_process_and_complexity_structured_master_bound`
    - 新增 process+complexity 直连 deterministic rate：
      - `linear_regression_rate_of_process_and_complexity_structured_master_bound`
      - `l1_regression_rate_of_process_and_complexity_structured_master_bound`
    - 新增 process+entropy 直连：
      - deterministic rate：
        - `linear_regression_rate_of_process_and_entropy_structured_master_bound`
        - `l1_regression_rate_of_process_and_entropy_structured_master_bound`
      - full interface：
        - `linear_regression_full_interface_of_process_and_entropy_structured_master_bound`
        - `l1_regression_full_interface_of_process_and_entropy_structured_master_bound`
    - deterministic rate 分支进一步去重：
      - `linear_regression_rate_of_process_and_complexity_structured_master_bound`
      - `linear_regression_rate_of_process_and_entropy_structured_master_bound`
      - `l1_regression_rate_of_process_and_complexity_structured_master_bound`
      - `l1_regression_rate_of_process_and_entropy_structured_master_bound`
      现统一经 `LocalizedDeterministicAssumptions.ofProcessAndComplexity / ofProcessAndEntropy`
      构造 `hDet` 后，复用
      `linear_regression_rate_of_deterministic_structured_master_bound` /
      `l1_regression_rate_of_deterministic_structured_master_bound`
    - full-interface 分支进一步去重：
      - `linear_regression_full_interface_of_proxy_structured_master_bound`
      - `linear_regression_full_interface_of_process_and_complexity_structured_master_bound`
      - `linear_regression_full_interface_of_process_and_entropy_structured_master_bound`
      - `l1_regression_full_interface_of_proxy_structured_master_bound`
      - `l1_regression_full_interface_of_process_and_complexity_structured_master_bound`
      - `l1_regression_full_interface_of_process_and_entropy_structured_master_bound`
      现统一先构造 `LocalizedProbabilityAssumptions`，再复用
      `linear_regression_full_interface_of_probability_structured_master_bound` /
      `l1_regression_full_interface_of_probability_structured_master_bound`
- 影响：
  - 这条引理是论文附录 docs 中列出的核心基础结果之一（`coveringNumber_lt_top_of_totallyBounded`），也是 Dudley 链条的基础砖块。
  - 去掉了旧版 `isCompact` 结果对 `[ProperSpace α]` 的不必要依赖。
  - 回归与 Dudley 模块接口已稳定到“可调用签名”层，后续可专注消减 axiom。

## 5. 论文主线与本仓库映射（高层）
- 高维高斯分析链条：
  - `Statlean/Concentration/EfronStein.lean`：正式签名，输入为参数化分析假设
  - `Statlean/Concentration/GaussianPoincare.lean`：正式签名，输入为参数化分析假设
  - `Statlean/Concentration/Density.lean`：正式签名，输入为参数化分析假设
  - `Statlean/Concentration/LogSobolev.lean`：正式签名，输入为参数化分析假设
  - `Statlean/Concentration/GaussianLipschitz.lean`：上下尾拼接证明保留，Herbst 部分改为参数化假设输入
- 经验过程 / Dudley：
  - `Statlean/EmpiricalProcess/CoveringNumber.lean`：定义 + 基础单调性 + 紧致/全有界有限覆盖数结论
  - `Statlean/EmpiricalProcess/Dudley.lean`：finite/general 都已是正式不等式签名，且无全局 axiom
- Least Squares 应用：
  - `Statlean/Regression/MasterBound.lean`：两个主结果已给正式签名，且都已去 axiom
  - `Statlean/Regression/Linear.lean`：已无全局 axiom（通过参数化假设保留接口）

## 6. 未完成项（精确清单）
- `axiom`：
  - 当前为 `0`（全仓库已无全局 axiom）
- `True` placeholders：
  - 当前为 `0`（已全部替换为真实命题签名）

## 7. 下次会话建议优先级（按 ROI）
1. 把 `local_gaussian_complexity_bound` 的右端从代理上界替换为 Dudley 熵积分表达式（基于 `empiricalMetricImage`）。
2. 基于已引入的结构化假设层，将旧的长参数 theorem 逐步改为“结构化 theorem 为主、长参数 theorem 为兼容壳”，继续收敛 API。
3. 将 Concentration 链条中的“参数化分析假设”逐段内化为 Lean 证明（先从 `EfronStein` 和 `GaussianPoincare`）。

## 8. 快速继续命令
```bash
cd /home/gavin/statlean
lake build
rg -n "axiom|placeholder|sorry" Statlean *.lean
```

若需要重新拿论文源码：
```bash
curl -L --fail --silent --show-error 'https://arxiv.org/e-print/2602.02285' -o /tmp/2602.02285.tar
tar -xpf /tmp/2602.02285.tar -C /tmp
```

## 9. 本轮追加进展（2026-02-19，继续“消减参数化前提”）
- 文件：`Statlean/Concentration/GaussianLipschitz.lean`
- 新增可积性内化引理（把外部假设转成 Lean 内证）：
  - `integrable_id_stdGaussianPi`：
    证明 `Integrable (fun x : Fin n → ℝ => x) (stdGaussianPi n)`。
    关键是 `integrable_comp_eval` + `Integrable.of_eval`。
  - `integrable_of_lipschitz_stdGaussianPi`：
    证明任意 `LipschitzWith L f` 在 `stdGaussianPi n` 下可积（线性增长界 + `Integrable.mono'`）。
  - `universalHerbst_of_lipschitz`：
    从 `UniversalHerbstBound` + `LipschitzWith` 自动得到 `HerbstBound`（内部自动补 `Integrable`）。
  - `herbstBound_neg`：
    证明 `HerbstBound` 对函数取负闭合（`s ↦ -s` 变换），可自动生成负尾所需 Herbst 前提。
  - `integrable_exp_abs_stdGaussian`：
    证明一维高斯下 `x ↦ exp(a|x|)` 可积（由 `exp(ax)` 与 `exp(-ax)` 的可积性夹逼得到）。
  - `norm_le_sum_abs_fin`：
    证明 `Fin n → ℝ` 上 `‖x‖ ≤ ∑ᵢ |xᵢ|`（用于把范数指数可积性降到坐标级）。
  - `integrable_exp_norm_stdGaussianPi_nonneg`：
    证明 `a ≥ 0` 时 `x ↦ exp(a‖x‖)` 在 `stdGaussianPi n` 下可积。
  - `integrable_exp_centered_of_lipschitz_stdGaussianPi`：
    证明 Lipschitz 函数的中心化指数矩 `x ↦ exp(s*(f(x)-E[f]))` 自动可积。
- 签名收紧（减少冗余参数）：
  - `UniversalHerbstBound` 已从“`Lipschitz + Integrable -> Herbst`”收紧为
    “`Lipschitz -> Herbst`”。
  - `herbst_argument` / `herbst_argument_of_bound` 去掉了未实质使用的显式 Lipschitz/Integrable 形参（保留 `HerbstBound` 核心输入）。
  - `gaussian_lipschitz_upper_tail` 去掉 `hfi : Integrable f ...` 形参，内部自动构造。
  - `gaussian_lipschitz_concentration` 去掉 `hfi` 形参，负函数分支也改为自动可积路径。
  - `gaussian_lipschitz_concentration` 进一步去掉 `hHerbstNeg` 形参，内部由 `herbstBound_neg` 自动导出。
  - `gaussian_lipschitz_upper_tail` / `gaussian_lipschitz_concentration` 不再显式要求
    `hExpInt`，改为内部复用 `integrable_exp_centered_of_lipschitz_stdGaussianPi` 自动生成。
  - 同时保留兼容层：
    `gaussian_lipschitz_upper_tail_of_expIntegrable` /
    `gaussian_lipschitz_concentration_of_expIntegrable`
    （供后续需要“显式指数可积性前提”的场景复用）。
  - `gaussian_lipschitz_upper_tail_of_universal_herbst` /
    `gaussian_lipschitz_concentration_of_universal_herbst`
    去掉 `hfi` 与 `hExpInt` 形参，统一复用 `universalHerbst_of_lipschitz` 与
    自动指数可积性引理。
  - `GaussianPoincare` / `EfronStein` 继续去冗余参数：
    - `gaussian_poincare_1d` 去掉未使用的 `_hf/_hf'/_hderiv`。
    - `gaussian_poincare_of_integral_bound` 去掉未使用的 `_hf/_hgradf/_hgrad`。
    - `gaussian_poincare_of_efron_stein` 去掉未使用的 `_hf/_hgradf`。
    - `gaussian_poincare_of_condVar_sum` 与 `gaussian_poincare` 去掉未使用的 `hgradf`。
    - `efron_stein_of_integral_bound` 去掉未使用的 `_hf`。
  - `Density` 继续去冗余参数：
    - `lipschitz_mollification_preserves_constant` 去掉未使用的 `_hg`。
    - `smooth_compactSupport_dense_in_gaussianSobolev` 去掉未使用的 `_hf`。
  - `Dudley` 模块做了“最小前提主定理 + 兼容层”与签名瘦身：
    - 新增最小前提版本：
      - `dudley_finite_of_bound`
      - `dudley_entropy_integral_of_bound`
    - `dudley_finite` / `dudley_entropy_integral` 主签名同步去掉未参与证明的长参数前提（保留结论与 `hDudley` 核心输入）。
  - 其它前提去噪：
    - `RaoBlackwell_MSE`：`condVar_integral_nonneg` 去掉未使用的 `_hG`，调用点已同步。
    - `MasterBound`：`capacity_control` 去掉未使用的 `_hn`。
- 验证：
  - `lake build Statlean.Concentration.GaussianLipschitz` 通过。
  - `lake build` 全量通过（2872 jobs）。
  - `rg -n "\\baxiom\\b|\\bsorry\\b" Statlean -g'*.lean'` 仍无命中（返回 0 条）。

## 10. 下一轮可继续压缩的前提（优先级）
1. `GaussianLipschitz` 主 API 的 `hExpInt` 已内化；下一步可考虑是否继续精简/合并
   `*_of_expIntegrable` 兼容层（取决于你后续是否还需要显式指数可积性接口）。
2. `GaussianPoincare` / `EfronStein` 目前主线仍依赖参数化 `hCondVar/hCoord`；
   可继续拆成更细 bridge 并内证可自动传递的部分（冗余形参已进一步清理）。
3. 在 Regression 链条，把仍偏“接口化”的概率侧假设继续向可复用引理收敛（优先 process+entropy 分支）。

## 11. 本轮追加进展（2026-02-19，继续“内证 + 消减冗余”）
- 文件：`Statlean/Regression/Linear.lean`
  - 大规模去除未使用形参（保持 theorem 名称不变）：
    - 去掉多处未使用的 `(_hR : 0 < R)`。
    - 去掉两处纯包装 rate 定理中的未使用 `(_hn : 0 < n)`、`(_hf_hat : ...)`、`(_hbdd : ...)`：
      - `linear_regression_rate`（`Statlean/Regression/Linear.lean:662`）
      - `l1_regression_rate`（`Statlean/Regression/Linear.lean:980`）
    - `l1_ball_covering_maurey` 去掉未使用的 `_hR/_hε`。
  - 同步更新了所有内部调用链（`linear_*` 与 `l1_*` 的 structured/full-interface 包装层）。

- 文件：`Statlean/Regression/MasterBound.lean`
  - 进一步内缩为最小有效前提（去掉仅“传递但不参与证明”的参数）：
    - `master_error_bound_localized`（`Statlean/Regression/MasterBound.lean:674`）改为最小 deterministic 形参集。
    - `local_gaussian_complexity_bound`（`:794`）改为仅保留核心 `hBound` 输入。
    - `master_error_bound_probability_interface`（`:815`）改为仅保留 `hProb` 对应最小参数集。
    - `master_error_bound_full_interface`（`:854`）去掉未使用的 CI/regularity 长参数，保留 deterministic+probability 两分支真正需要的输入。
    - `master_error_bound_full_interface_of_proxy_critical`（`:912`）同步瘦身并复用上面的最小接口。
  - `master_error_bound_localized_structured` 保持对结构化假设对象的兼容接口，但核心证明已统一复用最小版 `master_error_bound_localized`。

- 结果与检查：
  - `lake build Statlean.Regression.MasterBound Statlean.Regression.Linear` 通过。
  - `lake build` 全量通过（2872 jobs）。
  - `rg -n "\\(_h[a-zA-Z0-9_]*\\s*:" Statlean -g'*.lean'` 无命中（返回 0 条）。
  - `rg -n "\\baxiom\\b|\\bsorry\\b" Statlean -g'*.lean'` 无命中（返回 0 条）。

## 12. 本轮追加进展（2026-02-19，继续“前提内证”）
- 文件：`Statlean/Concentration/GaussianLipschitz.lean`
  - 将 `L > 0` 从用户前提改为证明内证：
    - `gaussian_lipschitz_upper_tail_of_expIntegrable`
    - `gaussian_lipschitz_upper_tail`
    - `gaussian_lipschitz_concentration_of_expIntegrable`
    - `gaussian_lipschitz_concentration`
    - `gaussian_lipschitz_upper_tail_of_universal_herbst`
    - `gaussian_lipschitz_concentration_of_universal_herbst`
  - 证明策略：
    - 在上尾核心证明中对 `L=0 / L≠0` 分情况内证。
    - `L=0` 时右侧退化为 `exp 0 = 1`，由概率测度上界给出平凡控制。
    - `L≠0` 时复用原有 Chernoff+Herbst 推导。
  - 作用：后续调用不再需要显式提供 `hL : (0 : ℝ) < L`。

- 文件：`Statlean/Regression/MasterBound.lean`
  - 继续内证并消减不必要前提：移除整条主接口中的 `hn : 0 < n`。
  - 已同步到以下接口（示例）：
    - `master_error_bound`
    - `master_error_bound_localized`
    - `master_error_bound_localized_structured`
    - `master_error_bound_full_interface`
    - `master_error_bound_full_interface_structured`
    - 以及各类 `*_of_proxy_*`、`*_of_process_and_*_structured` 包装层。

- 文件：`Statlean/Regression/Linear.lean`
  - 由于 `MasterBound` 去掉 `hn`，`Linear` 中对应桥接也同步内证并去前提：
    - `regression_rate_of_deterministic_structured_master_bound`
    - `regression_full_interface_of_probability_structured_master_bound`
    - `regression_rate_of_proxy_structured_master_bound`
    - `regression_*_of_process_and_{complexity,entropy}_structured_master_bound`
    - `linear_*` / `l1_*` 对应 deterministic 与 full-interface 包装层
      中的 `hn` 前提均已去除。

- 验证：
  - `lake build Statlean.Concentration.GaussianLipschitz` 通过。
  - `lake build Statlean.Regression.MasterBound Statlean.Regression.Linear` 通过。
  - `lake build` 全量通过（2872 jobs）。

## 13. 本轮追加进展（2026-02-19，继续“前提内证 + 结构收敛”）
- 文件：`Statlean/Regression/MasterBound.lean`
  - `LocalizedProbabilityAssumptions` 进一步瘦身：
    - 删除 `det : LocalizedDeterministicAssumptions ...` 字段，仅保留
      `hf_hat` 与 `hProb`（概率侧真正需要的内容）。
  - 构造器进一步内证化：
    - `LocalizedProbabilityAssumptions.ofDeterministic` 改为仅由
      `hf_hat + hProb` 构造；
    - `ofProxy / ofProcessAndComplexity / ofProcessAndEntropy`
      内部不再构造并携带 deterministic 包。
  - full-interface 包装定理继续去冗余前提：
    - `master_error_bound_full_interface_of_proxy_structured`
      去掉未使用的 `hLoc`；
    - `master_error_bound_full_interface_of_process_and_complexity_structured`
      去掉 `hσ/hδ/hProc/hLC/hScale`；
    - `master_error_bound_full_interface_of_process_and_entropy_structured`
      去掉 `hσ/hδ/hProc/hEnt/hScale`。
  - localized deterministic 包装继续收敛：
    - `master_error_bound_localized_structured` 改为真正最小签名
      （不再携带 `x/σ/δ_star/t/hLoc`）。
    - `master_error_bound_localized_of_proxy_structured` 同步去掉
      `x/σ/δ_star/t/hLoc`，直接复用最小 localized 版本。
    - `master_error_bound_localized_of_process_and_complexity_structured` /
      `master_error_bound_localized_of_process_and_entropy_structured`
      也收敛为最小 deterministic 前提（去掉 process/complexity/entropy 相关长前提）。

- 文件：`Statlean/Regression/Linear.lean`
  - 与 `MasterBound` 的概率结构简化对齐，进一步删掉 full-interface 分支冗余前提：
    - `regression_full_interface_of_proxy_structured_master_bound`
      去掉 `hLoc`；
    - `regression_full_interface_of_process_and_complexity_structured_master_bound`
      去掉 `hσ/hδ/hProc/hLC/hScaleCI`；
    - `regression_full_interface_of_process_and_entropy_structured_master_bound`
      去掉 `hσ/hδ/hProc/hEnt/hScaleCI`；
    - `linear_*_full_interface_of_proxy/process_*` 与 `l1_*_full_interface_of_proxy/process_*`
      相同前提同步删除。
  - 由于 `master_error_bound_localized_structured` 最小化，
    `regression_rate_of_deterministic_structured_master_bound`
    的内部证明改为直接复用最小 localized theorem；`hDet` 仅作为兼容层参数保留。

- 结果与检查：
  - `lake env lean Statlean/Regression/MasterBound.lean` 无 warning。
  - `lake env lean Statlean/Regression/Linear.lean` 无 warning。
  - `lake build Statlean.Regression.MasterBound Statlean.Regression.Linear` 通过。
  - `lake build` 全量通过（2872 jobs）。

## 14. 本轮追加进展（2026-02-19，继续“消减参数化前提到最小签名”）
- 文件：`Statlean/Regression/Linear.lean`
  - 进一步把 **rate 分支** 的兼容壳前提收缩到“证明真正需要”的最小集合。
  - 删除了 deterministic/proxy/process+{complexity,entropy} rate 链中仅中转不参与证明的形参：
    - `hDet`
    - `hLoc`
    - `hσ/hδ/hProc/hLC/hEnt/hScaleCI`
    - 以及由这些参数带来的 `x/σ/δ_star/t` 形参。
  - 受影响并已最小化的核心 theorem（名称保持不变）：
    - `regression_rate_of_deterministic_structured_master_bound`
    - `regression_rate_of_proxy_structured_master_bound`
    - `regression_rate_of_process_and_complexity_structured_master_bound`
    - `regression_rate_of_process_and_entropy_structured_master_bound`
    - `linear_regression_rate_of_deterministic_structured_master_bound`
    - `linear_regression_rate_of_proxy_structured_master_bound`
    - `linear_regression_rate_of_process_and_complexity_structured_master_bound`
    - `linear_regression_rate_of_process_and_entropy_structured_master_bound`
    - `l1_regression_rate_of_deterministic_structured_master_bound`
    - `l1_regression_rate_of_proxy_structured_master_bound`
    - `l1_regression_rate_of_process_and_complexity_structured_master_bound`
    - `l1_regression_rate_of_process_and_entropy_structured_master_bound`
  - 现在这些 theorem 的证明统一复用最小 deterministic 主干：
    - `master_error_bound_localized_structured`（来自 `MasterBound`）
    - `regression_rate_of_master_bound`（本文件通用 rate transfer）

- 结果与检查：
  - `lake env lean Statlean/Regression/Linear.lean` 通过。
  - `lake build Statlean.Regression.Linear Statlean.Regression.MasterBound` 通过。
  - `lake build` 全量通过（2872 jobs）。

## 15. 本轮追加进展（2026-02-19，继续“内证 + 冗余前提消减”）
- 文件：`Statlean/EmpiricalProcess/Dudley.lean`
  - 进一步泛化并去除未使用技术前提：
    - `dudley_entropy_integral_of_bound` 去掉 `[IsProbabilityMeasure μ]`。
    - `dudley_entropy_integral` 去掉 `[IsProbabilityMeasure μ]`。
    - `dudley_entropy_integral_of_bound` / `dudley_entropy_integral` 去掉 `[Nonempty T]`。
    - `dudley_finite_of_bound` / `dudley_finite` 去掉 `[Finite T]`。
  - 清理无用依赖与命名语义：
    - 删除未使用 import：`Statlean.Concentration.GaussianLipschitz`。
    - 删除未使用 `open Finset`。
    - 更新 `dudley_finite_*` 注释，明确其现在是 compatibility wrapper（保留旧 API 名称）。

- 结果与检查：
  - `lake env lean Statlean/EmpiricalProcess/Dudley.lean` 通过。
  - `lake build Statlean.EmpiricalProcess.Dudley` 通过。
  - `lake build` 全量通过（2872 jobs）。
  - `rg -n "\\baxiom\\b|\\bsorry\\b" Statlean -g'*.lean'` 仍为 0 命中。

## 16. 本轮追加进展（2026-02-19，Rao-Blackwell 复用桥接继续完善）
- 文件：`Statlean/RaoBlackwell_MSE.lean`
  - 新增“等号情形”桥接引理，减少后续手工来回转换：
    - `condVar_integral_eq_zero_of_stronglyMeasurable`
    - `condVar_integral_eq_zero_of_measurable`
    - `rb_mse_reduction_eq_iff_variance_reduction_eq`
  - 作用：
    - 把三类条件直接打通：  
      `MSE 等号` ↔ `方差等号` ↔ `μ[Var[Y|G]] = 0`。
    - 后续证明“可测 ⇒ 无改进 gap”“MSE 与 variance 等号联动”时可直接复用，不用重复拼装中间步骤。

- 结果与检查：
  - `lake env lean Statlean/RaoBlackwell_MSE.lean` 通过。
  - `lake build Statlean.RaoBlackwell_MSE` 通过。
  - `lake build` 全量通过（2872 jobs）。

## 17. 本轮追加进展（2026-02-19，继续“去冗余前提 + 泛化”）
- 文件：`Statlean/Regression/Linear.lean`
  - `l2Ball` 覆盖数链继续去前提：
    - `isCompact_l2Ball` 去掉 `hR : 0 < R`。
    - `l2_ball_covering_number_finite` 去掉 `hR`。
    - `l2_ball_covering_number_nat_bound` 去掉 `hR`。
    - `l2_ball_covering_number` 去掉 `hR`。
  - 证明层改动：用坐标范围 `[-|R|, |R|]` 取代 `[-R, R]`，因此对任意 `R : ℝ` 都成立。

- 文件：`Statlean/RaoBlackwell_MSE.lean`
  - `condVar_integral_nonneg` 泛化：
    - 去掉 `[IsProbabilityMeasure μ]`，改为一般测度下也成立。
  - 含义：后续任何需要“条件方差积分非负”但不要求概率归一化的场景都可复用该引理。

- 文件：`Statlean/EmpiricalProcess/Dudley.lean`
  - 本轮继续确认前提清理后状态稳定（无额外 typeclass 前提残留）：
    - `dudley_finite_of_bound` / `dudley_finite`：无 `[Finite]/[Nonempty]` 约束。
    - `dudley_entropy_integral_of_bound` / `dudley_entropy_integral`：无
      `[IsProbabilityMeasure]/[Nonempty]` 约束。

- 结果与检查：
  - `lake env lean Statlean/Regression/Linear.lean` 通过。
  - `lake env lean Statlean/RaoBlackwell_MSE.lean` 通过。
  - `lake build Statlean.Regression.Linear` 通过。
  - `lake build Statlean.RaoBlackwell_MSE` 通过。
  - `lake build` 全量通过（2872 jobs）。
