# Claude Code 项目配置

## 操作授权

本项目已预授权所有操作，包括：
- git 操作（commit、push、branch 等）
- 文件读写、创建、删除
- 脚本执行（make、python、bash 等）
- Lean 编译（lake build 等）

**无需逐次确认，直接执行。**

## Git 远程仓库

- **仓库地址**: `git@github.com:mockingbird-gan/statlean4.git`（SSH）
- **SSH 公钥**: `ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIIYGAXq8NzQtFRG4YobuSL7jEOl+FuiAInKBHgvqKv4O mockingbird-gan`
- **push 时必须使用 SSH**，不要用 HTTPS。如果发现 remote URL 是 HTTPS，先执行：
  ```
  git remote set-url origin git@github.com:mockingbird-gan/statlean4.git
  ```

## 沟通语言

- **用中文回答用户问题**（除非用户用英文提问）
- Lean 代码中的注释和 docstring 用英文
- commit message 用中英文均可

---

## 模块组织原则

### 按数学对象组织，不按证明项目
- 文件路径反映数学对象：`Gaussian/Poincare.lean`，不是 `Concentration/GaussianPoincare.lean`
- 一个数学对象的所有内容（定义、已证定理、sorry gap）放同一文件，用 section 隔离
- 定理名必须语义化：`frechet_mean_existence_transfer`，不是 `proposition_008_proposition_9`

### 同一文件内 sorry 和已证引理共存
- 已证引理和 sorry gap 可以放在同一文件中，用 `section` 隔离
- **不需要**拆分为 `FooBase.lean` + `Foo.lean`
- `Statlean/Verified.lean` 是附加验收工具（只 import 整文件零 sorry 的模块），**不驱动文件拆分**

### Mathlib 文件组织规则（强制）
- **中间引理和主定理放同一文件**，用 section/namespace 隔离（Mathlib 标准：Taylor、Hahn-Banach 等）
- **只有「独立可复用」的基础设施才拆出单独文件**（如 ANOVA 方差分解可被 Poincaré、LSI 复用）
- **没有 `*Base.lean` 模式**：不按证明状态（已证/未证）拆分文件
- **500-900 行的单文件完全正常**：不必因为行数多就拆分
- **按数学对象/抽象层级组织**：文件路径反映数学概念，不反映证明项目或状态

### 薄封装必须删除
- 如果 `f x` 只是 Mathlib `g x` 的别名，不保留 wrapper，直接内联替换调用点
- 例：`memLp_three_to_two hLp` → `hLp.mono_exponent (by norm_num : (2 : ENNReal) ≤ 3)`

### 空壳必须清理
- 空目录、只含 `namespace ... end` 的空文件、不被 import 的孤立文件 → 删除
- `Statlean.lean` 的 import 列表应与实际文件一一对应

---

## Import 迁移规则

- 删/移模块前**必须 grep 全仓库**：`grep -r "旧模块名" --include="*.lean"`
- 替换 import 时分析实际依赖，只 import 真正用到的模块
- 同时更新非 Lean 文件中的路径引用（`scripts/`、`theme/` 等）
- Lean 4 硬性规则：`import` 必须在文件最前，module docstring `/-! ... -/` 在所有 import 之后

---

## 形式化策略

**交互式形式化手册见 `theme/formalize_playbook.md`**（输入解析 → 内容获取 → 签名设计 → 证明 → 诚实性检查）。
用户在会话中说「形式化 XX 里的 YY」时，**必须遵循该 playbook 的 Step 0-7**。

## 证明策略

**证明操作手册见 `theme/prove_playbook.md`**（决策树 + 错误修复表 + 策略选择表）。
交互式会话和 pipeline prove agent 都遵循该 playbook。

### 攻击顺序
- sorry 形成依赖 DAG，从叶节点开始攻击
- 分类：(A) Mathlib 缺前置 API → 等待或自建基础设施；(B) 路线清晰 → 直接攻击；(C) 依赖未解决的 sorry → 排后
- 优先级 B > A > C

### 关键模式
- **强归纳**优于普通归纳：需要 `∀ m < n` 时用 `Nat.strongRecOn`
- **Case split**：对连续参数（如 `|t|`）分大小情形，小值用精细链，大值用粗糙界
- **Telescope**：乘积/求和望远镜展开 Mathlib 未必有现成的，准备手搓
- **IBP 路线**：`integral_mul_deriv_eq_deriv_mul_of_integrable` + density chain rule
- **L^p 降级**：`MemLp.mono_exponent` + `integrable_withDensity_iff` 处理 Gaussian 可积性

### Sorry 等级判定与校准（强制）

**参考表**：`theme/sorry_grading.md`（等级定义 + 实际攻击记录 + 当前评估）

**攻击前**：对目标 sorry 进行 S/A/B/C/D/E 等级判定，输出预计时间和 token。
**攻击后**：记录实际数据到 `theme/sorry_grading.md` 的「实际攻击记录」表，校准等级范围。

校准规则：
- 实际偏离预计 >50% → 标注异常原因
- 同等级连续 3 次偏离 → 调整该等级的预计范围
- 新产生的 sorry → 判定等级并加入「当前评估」表
- 已关闭的 sorry → 从「当前评估」移到「实际记录」

详见 `theme/prove_playbook.md` §1（启动流程步骤 5）和 §9（攻击后校准）。

### 验收标准
- `lake build` 零错误
- sorry 数只减不增
- `lake build Statlean.Verified` 零 sorry 警告

---

## 证明路线搜索 — 五级 Fallback 协议（强制）

**本节是硬性规则，所有证明流程（`/prove`、`/prove-deep`、`/prove-out`、`/pipeline` prove 阶段）必须遵循。**

攻击 sorry 前，按成本递增依次执行路线搜索。获得完整路线后跳过后续级别：

```
R1: 人类显式输入（0-5K token）→ parse_proof_roadmap.py 解析
R2: 输入上下文证明体（2-10K token）→ PDF/LaTeX proof 块解析
R3: 本地知识库（0-2K token）→ proof_knowledge.yaml L3/L2/L1 匹配
R4: Web 快速探测 + 深入获取（3-50K token）→ WebSearch + WebFetch
R5: LLM 自主探索（50-300K token）→ 当前流程
```

**关键原则**：R1-R4 都是为了避免 R5（最贵且最不可靠的阶段）。
**S-B 级 sorry → 跳过 R4，直接 R5**（简单 sorry 不值得 Web 搜索 token）。
**路线解析脚本**：`python3 scripts/parse_proof_roadmap.py`（多格式：纯文字/LaTeX/PDF/YAML）。

详细执行/升级条件见各 prove 命令的 Phase 0.5 和 `theme/prove_playbook.md` §3。

---

## Mathlib / StatLib 搜索策略（省 token 三级法）— 强制执行

**本节是硬性规则，所有证明流程（`/prove`、`/prove-deep`、subagent）必须遵循。**
**违反本节 = 浪费 token + 搜索结果不可靠，用户有权拒绝。**

搜索 Mathlib 或 StatLib API 时按以下顺序，**逐级升级**，不要跳级：

### 第零级：路线 key_api + 证明知识库 — 匹配到则跳过后续
- **如果 Phase 0.5 路线搜索获得了 key_api** → 按列表定向查签名，跳过全文读取
- **如果** `theme/proof_knowledge.yaml` 的 L3/L2 已匹配 → 同上
- key_api 中的名字按来源查签名：
  - **StatLean API** → `grep -i '<name>' theme/statlean_api_index.tsv`（614 条，毫秒级）
  - **Mathlib API** → `grep -i '<name>' theme/mathlib_full_type_index.tsv`（51K 条，毫秒级）
- 仅当路线和知识库均未覆盖当前 goal 时才进入第一级

### 第一级：查静态索引（~8.5K token）— 知识库未匹配时执行
- 读 `theme/mathlib_api_index.md`（~650+ 条，按 namespace 分 section）
- `grep -i '<keyword>' theme/statlean_api_index.tsv`（614 条 StatLean 自建 API）
- `grep -i '<keyword>' theme/mathlib_full_type_index.tsv`（51K 条全量 Mathlib 索引）
- 同时读 `Statlean/Verified.lean` 获取已入库模块列表

### 第二级：`#check` / `exact?`（精确但慢）
- 已知名字查签名：`echo '#check @ProbabilityTheory.foo' | lake env lean --stdin`
- 不知道名字但知道目标类型：写 `exact?` 或 `apply?`（~30-60 秒）
- 适用场景：索引没有、但怀疑 Mathlib 有

### 第三级：grep Mathlib 源码（最后手段）
- 只在前两级都失败时才用
- **使用前必须注明**："索引无此条目，第二级 #check 也未找到，升级到 grep"
- 限定目录：`Mathlib/Probability/`、`Mathlib/MeasureTheory/`、`Mathlib/Analysis/`
- 用 `Grep` 工具搜关键词，不要全目录扫描

### 索引维护
- 生成脚本：`scripts/gen_mathlib_index.lean`
- 重新生成：`lake env lean scripts/gen_mathlib_index.lean > theme/mathlib_api_index.md`
- Mathlib 升级后重跑一次（~30 秒）

---

## Phase 0 工具链（强制）

### 攻击 sorry 前必查路线 + 知识库
- **Phase 0.5 路线搜索**：按 R1→R2→R3→R4→R5 五级 fallback 获取证明路线
- 有路线 → 按路线 key_api 定向查签名，**跳过 mathlib_api_index.md 全文读取**
- 无路线 → 读 `theme/proof_knowledge.yaml` 按 trigger 匹配 goal 形态
  - **匹配到 L3/L2** → 优先使用已记录的 strategy/chain（一轮验证即可），**跳过 mathlib_api_index.md**
  - **未匹配** → 升级到 mathlib_api_index.md 搜索（三级法第一级）
- **给 subagent 的 prompt 必须包含**：Phase 0.5 路线搜索指令 + "先读 `theme/proof_knowledge.yaml` 查找匹配的 pattern，匹配到则跳过 mathlib_api_index"

### proof_knowledge.yaml 维护规则
- **自动入库**：证明成功后 agent 输出 `new_knowledge` YAML 块，由 `scripts/ingest_knowledge.py` 自动入库
- **入库标准**：L1 frequency≥2（脚本累计）、L2 chain≥2 API、L3 confidence≥3
- **去重**：trigger 关键词 Jaccard>0.8 视为同条目（更新 frequency/source）
- **Mathlib 升级后验证** — 版本升级后抽查 pattern 是否仍有效，删除失效条目

### 签名提取代替全文件读取
- 读大文件（>200 行）前，**优先**用 `python3 scripts/extract_signatures.py <file>` 获取声明索引
- 只有需要修改具体证明体时才 Read 完整文件
- **给 subagent 的 prompt 必须包含**：用 `extract_signatures.py` 先读声明索引，定位目标行号后再 Read 指定范围

### API 命名坑速查表
- `theme/api_gotchas.tsv`：~12 条高频 API 命名错误（wrong_guess → correct_api）
- 用法：`grep -i '<name>' theme/api_gotchas.tsv`
- **build 报 `unknown identifier` / `unknown constant` 时必须先查此表**，再查 full_type_index
- 维护：发现新命名坑时追加行（TSV 格式：wrong_guess\tcorrect_api\tnote）

### Mathlib 离线索引查询
- `theme/mathlib_full_type_index.tsv`：51K 条声明名+类型，grep 毫秒级
- 与 `theme/mathlib_api_index.md` 配合使用：先查 api_index（有注释），再查 full_type_index（全量）
- 用法：`grep -i 'condexp' theme/mathlib_full_type_index.tsv`
- Mathlib 升级后重新生成：`lake env lean scripts/gen_full_type_index.lean > theme/mathlib_full_type_index.tsv`

### 增量编译
- 验证单个 declaration 时用 `bash scripts/check_snippet.sh <file> <start_line> <end_line>`
- 比 `lake build Statlean.Foo` 快 3-5x，适合 tactic 试错循环
- 全模块验证仍用 `lake build Statlean.<Module>`

---

## 效率规则

- **并行 subagent（强制，上限 3 个）**：`/prove-deep` 和多 sorry 攻击时，启动独立 agent 并行，**同时运行的 agent 不超过 3 个**
  - 不同模块的 sorry（如 Poincaré vs LSI vs BerryEsseen）→ 同时启动多个 Task agent
  - 同一定理的 sub-lemma 如果互不依赖 → 也可以并行
  - 仅当有数据依赖时才串行（如 A 的输出是 B 的输入）
  - **硬性上限 3 并发**：待攻击任务超过 3 个时，按优先级选前 3 个并行，剩余排队等空位
  - 纯研究/搜索型 agent → `model: haiku`；需要写代码的 agent → `model: sonnet` 或默认
- **subagent 用 haiku**：纯搜索、grep、读文件指定 `model: haiku`
- **增量编译**：`lake build Statlean.Gaussian.Poincare` 只编目标，不要每次全量 build
- **grep 先于 read**：用 Grep 定位行号再 Read 指定范围，不盲读大文件
- **不重复搜索**：委派给 subagent 的搜索不要自己再做一遍
- **深度预算**：`/prove` 模式 3 轮发散即 triage；`/prove-deep` 模式不设轮数限制，可以运行数小时
- **上下文保护**：大量搜索结果放 subagent 消化，只返回结论到主会话
- **上下文满自动续接（强制）**：
  - 当检测到上下文接近容量限制时，**立即**执行以下保存动作，不要等到最后：
    1. 更新 `sorry_backlog.yaml`：所有已完成/新增 sorry 的状态变更
    2. 更新 `MEMORY.md`：新学到的 Mathlib patterns、已完成的证明
    3. Commit 所有已完成的工作（即使部分完成也 commit 已验证通过的部分）
  - 新会话开始时，用户只需发 `/prove-deep all-leaves` 或 `/prove-deep next`
  - Claude 会自动读取 `sorry_backlog.yaml` + `MEMORY.md` 恢复状态并继续
  - **不要在中间轮次停下来写总结报告** — 持续推进直到上下文真正用完
  - 用户可以用 `claude --continue` 在同一会话续接，或新会话中靠 backlog 恢复
- **subagent 实时落盘（强制）**：
  - subagent 证明过程中，每完成一个 sub-lemma 或发现关键 pattern，**立即写入目标 .lean 文件**（即使主定理还有 sorry）
  - 这样 subagent 上下文耗尽时，已完成的部分已经落盘，新 agent 可以从文件当前状态续接
  - 给 subagent 的 prompt 必须包含："每证完一个子引理立即写入 .lean 文件并 lake build 验证，不要攒到最后一起写"
- **subagent 返回后自动检查续派**：
  - subagent 返回后，主会话检查目标 sorry 是否已关闭（grep sorry 或 lake build）
  - 若未关闭且 subagent 有实质进展（文件已修改），立即派新 agent 续接，prompt 注明"从文件当前状态继续，前任已完成 X"
  - 若无进展（策略耗尽），记录到 sorry_backlog.yaml 并转攻下一个目标，不无限重试
- **基础设施增量入库（强制 — 证明过程中实时执行，不等主定理完成）**：
  证明过程中产生的内容分两类处理：

  **A. 零 sorry 基础设施**（自身无 sorry，且依赖链也无 sorry 的引理/定义）→ **立即入库**：
  1. **确定归属模块**：按数学对象确定属于哪个 `Statlean/` 子目录
     - 例：Gaussian 相关 → `Statlean/Gaussian/`，熵相关 → `Statlean/Entropy/`
     - 如果目标目录或文件不存在，**创建之**（Mathlib-style 命名 + module docstring）
  2. **放入正确文件**：已有对应主题文件 → 追加到合适 section
  3. **更新 import 链**：使用方添加 import，`Statlean.lean` 同步更新
  4. **验证**：`lake build Statlean.<Module>` 编译通过
  5. 如果整个文件零 sorry → 同时更新 `Verified.lean`
  6. **不要等**——每个子引理独立入库，不等主定理完成

  **B. 含 sorry 的定理**（自身有 sorry，或依赖链有 sorry）→ **同文件存放，等待攻击**：
  1. 放在同一数学对象文件中，用 `section` 与零 sorry 部分隔离
  2. 添加结构化 sorry 注释（blocker、proof sketch、estimated effort）
  3. 在 `sorry_backlog.yaml` 中注册，标明依赖关系和优先级
  4. 以后有资源时通过 `/prove-deep` 攻击

---

## 输出预算规则（强制）— 屏幕摘要 vs 文件存档

**根本原则**：屏幕上只放用户需要"扫一眼"的信息；所有详情写文件，告诉用户文件路径。

| 内容 | 屏幕输出 | 文件存档 |
|------|---------|---------|
| PROVE 报告 | `PROVE: <name> — sorry N→M \| closed: [names]`（1-3 行） | `reports/prove_report_<name>.md` |
| DAG PROVE 报告 | `DAG PROVE: Xmin \| sorry N→M`（3-5 行） | `reports/prove_deep_<target>.md` |
| 经验报告 | `经验报告已写入 reports/session_report.md`（1 行） | `reports/session_report.md` |
| 知识入库 | `入库 N 条 pattern`（1 行） | YAML + 脚本输出在 Bash 工具内 |
| 策略分析 | `Strategy: X via [API1, API2]`（1 行） | 写入对应报告文件 |
| build 错误 | 1 行摘要 + fix 动作 | build log 在 Bash 工具输出里 |

**预算上限**：
- `/prove` 单 sorry → 屏幕文本 ≤ 3K token
- `/prove-deep` 多 sorry → 屏幕文本 ≤ 5K token
- 超预算 → 极简模式：只输出 sorry 计数变化 + 文件路径
- `/prove-out` 演示模式豁免此限制
- 工具调用输出（Bash、Read、Grep 等）不计入预算

---

## 经验反馈闭环（强制）— 输出分流模式

**每次会话的实质性工作结束后**，执行以下流程：

### 流程

1. **完整报告写文件**（用 Write 工具写入 `reports/session_report.md`）：
```
## 本轮经验报告

### 已入库 proof_knowledge.yaml
- [L1/L2/L3] <trigger 摘要> — <正面/anti> — <来源 sorry/定理>

### 新发现的 Lean/Mathlib 模式（待用户确认入库）
- <编号>. <模式描述> — <发现场景>

### Pipeline / 工具链改进建议
- <建议描述> — <动机>

### 分类 / 路由规则建议
- <规则描述> — <触发的误分类案例>

### 踩坑记录（避免重复）
- <坑描述> — <解决方案>
```

2. **屏幕只输出 1 行摘要**：
```
经验报告已写入 reports/session_report.md（入库 N 条 pattern，K 条踩坑）
```

3. **proof_knowledge 入库（强制，不等用户确认）**：
   - 证明过程中发现的 L1/L2/L3 pattern（正面或 anti）→ 写入临时 YAML 文件后运行
     `python3 scripts/ingest_knowledge.py --input <file>` 标准入库（自动验证 + 去重）
   - `anti: true` 条目 = 负面经验（"不要走这条路"），与正面条目放在同一层级
   - 原来的「证明策略新 pattern」和「踩坑记录中的证明相关部分」**统一进 proof_knowledge**
4. **用户审阅** — 用户决定 Pipeline 改进、分类规则等是否值得固化
5. **用户指令固化** — 用户说「采纳 X」后，Claude 执行：
   - Pipeline 改进 → 更新对应 `theme/scripts/` 代码或 pipeline skill
   - 分类规则 → 更新 `theme/scripts/classify.py` 的 `_THEOREM_RULES` 或 ontology
   - 非证明类踩坑 → 写入 `memory/pitfalls.md`

### Memory 分层写入规则（强制）

Memory 目录：`~/.claude/projects/-home-gavin-statlean/memory/`

**MEMORY.md**（自动加载前 200 行）只放：
- 项目状态、文件结构、sorry 概要、关键 API、slash commands
- **Recently Learned Patterns** 区域：最近常用的 pattern（单行摘要，≤15 条）
- 超过 15 条时，把最旧的移入 `patterns.md`

**Topic 文件**（按需 Read 加载）：
| 文件 | 内容 |
|------|------|
| `patterns.md` | 全部编号 Lean/Mathlib 模式（按类别分组） |
| `pitfalls.md` | 踩坑记录 + 结构性 blocker |
| `completed.md` | 里程碑历史 |
| `convergence_patterns.md` | 收敛证明详细模式 |

**写入流程**：
1. 新 pattern → 先加到 `MEMORY.md` 的 "Recently Learned Patterns"（单行摘要）
2. 同时加到 `patterns.md` 的对应类别下（完整描述 + 来源）
3. 踩坑记录 → 加到 `pitfalls.md`
4. 里程碑 → 加到 `completed.md`
5. 新的专题（如某类证明的详细 pattern 积累 ≥5 条）→ 创建新 topic 文件，从 MEMORY.md 链接
6. **MEMORY.md 必须保持 <200 行** — 每次写入后检查行数，超出则精简或移入 topic 文件

### 什么算「实质性工作」（触发报告）

- 完成 ≥1 个定理的证明或形式化
- Pipeline 运行一轮完整流程（PDF → Gate）
- 攻击 sorry 有实质进展（减少 sorry 或发现新 blocker）
- 修复 ≥2 个编译错误的调试过程

### 什么不需要报告

- 纯问答、文件浏览、简单编辑
- 只跑了 `lake build` 确认编译通过
- 纯 git 操作（commit、push）
