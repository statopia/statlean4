# PRD：最小可运行 Lean4 调试闭环（Rao–Blackwell MSE Skeleton）—Step by Step（中文）

> 目的：你目前对 Lean4/报错/调试都“没概念”。本 PRD 用**最小模块**让你在 WSL(Linux)+VS Code Remote 环境里完成一次“从 0 到可编译 + 定位 Goal + 记录 debug”的闭环。  
> 输出：一个可编译的 Lean 项目 + 一个包含 `sorry` 的定理 skeleton + 一份“逐步截图/日志式”调试记录（按本 PRD 模板填写）。  
> 注意：本阶段**不要求**最终证明完成（不要求消灭 `sorry`），目标是**把流程跑通**，并让你能读懂“Lean 在哪里提示你缺什么”。

---

## 0. 角色与约束

- 你：项目 owner，负责在本地 WSL 执行命令，复制粘贴日志/报错/Goal。
- Claude Code（CC）：执行工程搭建、文件创建、按本 PRD 输出中间结果与解释。
- 约束：
  - OS：WSL Ubuntu（或等价 Debian 系）
  - 编辑器：VS Code Remote - WSL
  - 不假设你已有 Lean/elan/lake 环境
  - 全程使用命令行（bash）+ VS Code
  - 所有步骤都要在 PRD 的“记录模板”里填：命令、输出、解释、下一步

---

## 1. 成功标准（Definition of Done）

### 1.1 最小成功（MVP 成功）
满足以下全部条件即 MVP 成功：

1. `elan --version`、`lake --version` 在 WSL 终端可用。
2. 创建一个 **Lean + mathlib** 项目（使用 `lake init ... mathlib`），并且：
   - `lake exe cache get` 成功（或给出失败原因与替代方案）。
   - `lake build` 在“空项目”阶段成功。
3. 在项目中新增文件 `LeanRb/RaoBlackwell_MSE.lean`（路径以你项目名为准），文件中包含一个 `theorem`，且定理证明处允许 `sorry`。
4. 在 `LeanRb.lean`（项目入口）里加入 `import LeanRb.RaoBlackwell_MSE`，使该文件参与编译。
5. 运行 `lake build`：
   - 若设置允许 `sorry`：build 通过，但 VS Code 中明确显示 `sorry` 警告。
   - 若默认不允许：build 失败，但报错明确指出 `sorry`（这也算成功：因为你成功让 Lean 把“缺失证明”定位出来）。
6. 在 VS Code 中把光标放到 `sorry` 上，右侧能看到 **Goal**（当前证明目标），并把该 Goal 复制到 PRD 记录模板中。

### 1.2 延伸成功（可选）
- 找到并替换一个 `sorry` 为真实证明（哪怕只证明一个小 lemma，例如“平方非负”），并记录过程。

---

## 2. 你将得到的交付物

项目目录（示例）：
```
lean-rb/
  lakefile.lean
  lean-toolchain
  LeanRb.lean
  LeanRb/
    RaoBlackwell_MSE.lean
    (其他文件...)
  DEBUG_LOG.md        <-- 本 PRD 要求 CC 生成并持续追加的调试日志
```

---

## 3. Step-by-step 执行说明（WSL / Linux）

> 每一步都要：  
> - CC 给出要执行的命令  
> - 解释为什么要做  
> - 说明“成功时你会看到什么”  
> - 如果失败，给出“常见失败原因 + 诊断命令 + 修复方案”  
> - 在 `DEBUG_LOG.md` 里写入对应记录

---

### Step 1：检查/安装基础依赖（curl、git、build 工具）

#### 1.1 检查
在 WSL 终端执行：
```bash
which curl && curl --version
which git && git --version
```

**成功标志**：两条都有输出路径与版本。

#### 1.2 若缺失则安装
```bash
sudo apt update
sudo apt install -y curl git build-essential pkg-config libgmp-dev
```

**解释**：
- `elan` 安装需要 `curl`
- 拉取 mathlib 需要 `git`
- 编译/链接可能需要 `build-essential` 与 `libgmp-dev`

---

### Step 2：安装 Lean 工具链（elan + lake）

#### 2.1 安装 elan
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```
提示选择 toolchain 时：直接回车（默认）。

让环境生效：
```bash
source ~/.profile
```

检查：
```bash
elan --version
lake --version
lean --version
```

**成功标志**：三条都有版本号输出。

**常见失败与修复**：
- `command not found`：说明 PATH 未生效 → `source ~/.profile` 或重开终端
- 网络失败：换网络或使用代理（记录错误信息）

---

### Step 3：创建一个 Lean + mathlib 项目（最关键）

#### 3.1 选择工作目录
建议在 home 下建：
```bash
cd ~
mkdir -p projects
cd projects
```

#### 3.2 初始化项目（项目名固定为 lean-rb，便于对照）
```bash
mkdir -p lean-rb
cd lean-rb
lake init lean-rb mathlib
```

**解释**：
- `mathlib` 模板会自动配置依赖，并生成入口文件等。

**成功标志**：
- 目录下出现 `lakefile.lean`、`lean-toolchain`、`.lake/`、`LeanRb.lean`（或相似命名）
- 终端无 error 退出

**常见失败与修复**：
- `unknown template 'mathlib'`：说明 lake 版本/模板不同  
  → 备选：`lake init lean-rb` + 手动添加 mathlib（CC 需给修复步骤）
- GitHub 拉取失败：记录错误、重试、检查网络

---

### Step 4：下载 mathlib 缓存（强烈推荐）

在项目根目录：
```bash
lake update
lake exe cache get
```

**成功标志**：
- 命令输出显示下载 `.olean` 缓存完成
- 之后 build 会明显更快

**常见失败与修复**：
- 如果 `cache get` 失败：仍可继续，但第一次 `lake build` 会很慢（可能 30min+）。  
  CC 必须在日志里写明：失败原因、是否继续、预计影响（“编译更慢”）。

---

### Step 5：第一次构建（确认环境 OK）

```bash
lake build
```

**成功标志**：无 error 返回。

**若失败**：
- 把第一条 error（从顶部开始）完整复制到 `DEBUG_LOG.md`
- CC 需要给出：
  - 错误类型（网络/依赖/编译/路径）
  - 最小修复步骤（命令）

---

### Step 6：用 VS Code Remote - WSL 打开项目

在 WSL 终端（项目根目录）：
```bash
code .
```

在 VS Code 中确认：
- 安装扩展：**Lean 4**（必需），**Remote - WSL**（通常已有）
- 右下角显示在 WSL 环境

**成功标志**：
- `.lean` 文件有语法高亮
- 打开 `LeanRb.lean` 不报“Lean server 未启动”的错误

---

### Step 7：新增最小定理文件（允许 sorry）

#### 7.1 创建文件
在 `LeanRb/` 目录下新建：
`LeanRb/RaoBlackwell_MSE.lean`

> 注意：如果你的库目录叫 `LeanRb/` 以外的名字（取决于模板），请以实际为准，但保证“库目录/文件名”与 import 一致。

#### 7.2 粘贴以下最小内容（先不追求证明，只追求能被 Lean 识别并产生 Goal）

```lean
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] [ProbabilitySpace Ω]

theorem rb_mse_skeleton
  (G : MeasurableSpace Ω) (hG : G ≤ ‹MeasurableSpace Ω›)
  (Y : Ω → ℝ) (θ : ℝ)
  (hY : MemLp Y 2) :
    (∫ ω, (condexp G Y ω - θ)^2 ∂(ℙ : Measure Ω))
      ≤
    (∫ ω, (Y ω - θ)^2 ∂(ℙ : Measure Ω)) := by
  -- 先占位：目标是让你看到 Goal/报错
  sorry
```

**你现在要理解的只有 3 点**：
- `theorem ... : ... := by` 是“我要证明这个结论”
- `sorry` 是“我还没证明完，先占位”
- VS Code 会在 `sorry` 处显示当前 Goal

---

### Step 8：让新文件参与编译（import 入口）

打开项目根目录下的入口文件（通常是 `LeanRb.lean`），加入：

```lean
import LeanRb.RaoBlackwell_MSE
```

> 如果你的库叫 `StatLean` 或其他名字，import 路径需同步修改。  
> 规则：`import <库名>.<文件相对路径（去掉.lean，目录用点号）>`

---

### Step 9：构建并观察报错/警告

回到 WSL 终端：
```bash
lake build
```

可能出现两种情况：

#### 情况 A：build 通过，但有 `sorry` 警告
- 说明项目允许 `sorry`（开发期很常见）
- VS Code 中 `sorry` 会有提示

#### 情况 B：build 失败，提示 `sorryAx` 或 `declaration has sorry`
- 说明项目不允许 `sorry`
- 这也算 MVP 成功：你已让 Lean 精确指出“缺失证明的位置”

---

### Step 10：在 VS Code 里读取 Goal（关键训练）

操作：
1. 打开 `LeanRb/RaoBlackwell_MSE.lean`
2. 把光标放到 `sorry` 那行
3. 看右侧 “Goals” 面板（Lean Infoview）
4. 复制其中内容到 `DEBUG_LOG.md` 对应位置

**你应该看到**类似：

- 当前目标 `⊢ ...`（要证明的不等式）
- 已有假设（`G`, `hG`, `Y`, `θ`, `hY`）

---

## 4. Debug 日志模板（CC 必须创建并填写）

创建文件：`DEBUG_LOG.md`（放项目根目录）

内容模板如下（每一步都追加一段）：

```md
# DEBUG_LOG（按 Step 追加）

## Step X：<步骤名称>
- 命令：
```bash
<你执行的命令>
```

- 终端输出（关键部分，尤其是 error 顶部 30 行）：
```
<粘贴输出>
```

- 解释（中文，面向新手）：
  - 这一步在做什么：
  - 成功标志是什么：
  - 我现在看到的现象说明什么：
  - 下一步要做什么：

- 如果失败（必填）：
  - 失败原因猜测：
  - 诊断命令：
  - 修复方案与命令：

- VS Code/Lean Infoview（如适用）：
  - 当前 Goal：
  - 假设（Context）：
  - 我看不懂的符号/术语：
```

---

## 5. 常见错误类型速查（让你“知道它在提示你缺啥”）

> CC 在遇到这些报错时，必须按此表解释给你（中文）。

### 5.1 unknown identifier / unknown constant
- 含义：引用的名字找不到（没 import 或拼错）
- 典型修复：加 `import ...` 或改名字

### 5.2 failed to synthesize / typeclass instance problem is stuck
- 含义：Lean 需要某个结构/前提（比如“可积性”、“概率测度”），但当前上下文缺
- 典型修复：在 theorem 参数中补假设（如 `Integrable`/`Measurable`/`MemLp`）

### 5.3 type mismatch
- 含义：类型不匹配（例如 `Measure Ω` vs `ProbabilityMeasure Ω`、`ℝ` vs `ℝ≥0∞`）
- 典型修复：用 `simp`/`change`/`have` 做转换，或换用匹配接口的 lemma

### 5.4 “declaration has sorry”
- 含义：你用了 `sorry`，当前设置不允许
- 典型修复：临时允许 `sorry`（开发期）或开始补证明

---

## 6. 扩展任务（可选）：做一个“能去掉的 sorry”（极小示例）

> 目标：让你体验“从 sorry → 真证明”的感觉，但只做最简单的一块。

在 `rb_mse_skeleton` 的 proof 里先证明一个小结论：

```lean
  have h_nonneg : 0 ≤ (∫ ω, (Y ω - θ)^2 ∂(ℙ : Measure Ω)) := by
    apply integral_nonneg
    intro ω
    nlinarith
```

然后把最终目标继续 `sorry`。  
这一步用于训练：`integral_nonneg` + `nlinarith` 的工作方式。

---

## 7. 交付清单（CC 最终必须提交）

1. `lean-rb` 项目目录可完整运行（包含 `lakefile.lean`, `lean-toolchain` 等）。
2. 新增文件 `LeanRb/RaoBlackwell_MSE.lean`（或对应库名路径），内容如 Step7。
3. 入口文件已 `import LeanRb.RaoBlackwell_MSE`。
4. `DEBUG_LOG.md` 完整填写 Steps 1–10 的执行记录，包含：
   - 关键命令
   - 关键输出/报错
   - 对新手的中文解释
   - VS Code Infoview 的 Goal 文本复制
5. 一个最终总结段（中文）：
   - 我们成功跑通了什么
   - 现在 `sorry` 代表什么
   - 下一阶段要做什么（例如：定位 `h_decomp` 所需 lemma）

---

## 8. 备注：为什么本 PRD 选择 Rao–Blackwell skeleton？

- 它属于统计推断常用定理
- 证明结构非常固定，适合后续总结成模板/自动化
- 但本 PRD 的目标不是证明本身，而是跑通 Lean 调试闭环
