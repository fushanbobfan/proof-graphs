# A human audit of the goal-origin graphs / 目标起源图人工审核

Each section is given in English and then in Chinese.

每一节先给英文，再给中文。

## What this is / 这是什么

Three earlier audits compared the graphs that the extractor derives with reconstructions made by language-model
agents, and all of them agreed once the derivation program had been corrected. Two reviews asked for a check by a
person, on difficult syntax and on very long proofs. This kit asks you to rebuild by hand the graphs of 12 proofs,
and of a window of 25 or so steps in each of 3 very long proofs, from the source and from the goals Lean displays.
Your reconstructions are compared with the derived graphs only after you hand them in.

此前的三次审核，把提取程序推导出的图和语言模型智能体做的重建进行了比对，在推导程序修正之后全部一致。两份审稿意见要求补做一次人工检查，重点是较难的语法和很长的证明。这套材料请你根据源码和 Lean 显示的目标，手工重建 12 个证明的图，以及 3 个很长的证明中各一段约 25 个步骤的窗口。你交回重建结果之后，才会与推导出的图进行比对。

## Time / 时间

About three to four hours in all. The items are independent, so the work can be split over several sessions.

总共大约三到四个小时。各题互相独立，可以分几次完成。

## Rules / 规则

1. Work from the proof's source and from the goals Lean displays (VS Code with the Lean 4 extension). Reading
   Lean's and Mathlib's source and documentation is allowed.
2. Open only this kit's folder, `experiments/extraction-audit-v0.4/human-kit/`, and the source files the
   worksheet names. In particular, do not open `datasets/`, the extraction files (`extraction.jsonl.gz`), anything
   else under `experiments/` (the experiment's README, `sample.json` and `preregistration.json` one level up
   included), or anything in `scripts/`, and do not run the extractor (`proof_graph_extract`) or any script.
3. Do the reconstruction yourself, without help from a language model (Codex included): the audit measures what a
   person reads from the source with the written definition.
4. Write every doubt into a Notes column. A noted doubt is useful even when the answer turns out right.

1. 依据证明的源码和 Lean 显示的目标来做（使用装有 Lean 4 扩展的 VS Code）。可以查阅 Lean 和 Mathlib 的源码与文档。
2. 只打开本材料所在的文件夹 `experiments/extraction-audit-v0.4/human-kit/`，以及 `worksheet.md` 中列出的源码文件。尤其不要打开 `datasets/`、各提取文件（`extraction.jsonl.gz`）、`experiments/` 下的其他任何内容（包括上一级的实验 README、`sample.json` 和 `preregistration.json`），以及 `scripts/` 下的任何文件；也不要运行提取程序（`proof_graph_extract`）或任何脚本。
3. 重建请亲手完成，不借助语言模型（包括 Codex）：这次审核衡量的是一个人依据书面定义、从源码中读出的结果。
4. 所有拿不准的地方都写进"备注"一栏。即使答案最后是对的，记下的疑问也有用。

## Setup / 环境准备

You need git, [elan](https://github.com/leanprover/elan) and VS Code with the "Lean 4" extension. The repository
pins Lean 4.32.0, which elan installs by itself; about 8 GB of disk space is needed. On Windows, first run
`git config --global core.longpaths true`, because some file names of the dependency are long. Both repositories
the commands fetch, proof-graphs and proofnet-ir, are public.

需要 git、[elan](https://github.com/leanprover/elan)，以及装有 "Lean 4" 扩展的 VS Code。仓库固定使用 Lean 4.32.0，elan 会自动安装；大约需要 8 GB 磁盘空间。在 Windows 上，请先运行 `git config --global core.longpaths true`，因为依赖中有些文件名很长。下面的命令会拉取 proof-graphs 和 proofnet-ir 两个仓库，二者都是公开的。

```text
git clone https://github.com/fushanbobfan/proof-graphs.git
cd proof-graphs
lake exe cache get
lake build ProofNetIR
code .
```

`lake exe cache get` downloads Mathlib's compiled files, about 6 GB. `lake build ProofNetIR` compiles the library
some of the proofs come from, about ten minutes. `code .` opens the folder in VS Code (or use File > Open Folder).
Then open an item's file (`worksheet.md` gives its path, under `.lake/packages/`) and wait until Lean has finished
checking it (the orange bar in the margin disappears). With the cursor at the start of a tactic, the "Lean
Infoview" panel shows the goals before that tactic; with the cursor at its end, the goals after it.

`lake exe cache get` 下载 Mathlib 已编译的文件，约 6 GB。`lake build ProofNetIR` 编译部分证明所在的库，约十分钟。`code .` 用 VS Code 打开该文件夹（也可以用 File > Open Folder）。之后打开某一题的文件（`worksheet.md` 给出了路径，位于 `.lake/packages/` 之下），等 Lean 检查完毕（左侧的橙色条消失）。把光标放在某个策略的开头，"Lean Infoview" 面板显示执行该策略之前的目标；放在策略末尾，显示执行之后的目标。

## The items / 题目

`worksheet.md` lists the 15 items. P01 to P12 are whole proofs; W1 to W3 are windows of long proofs. Each item
gives the module, the declaration, the file and the lines to reconstruct, and prints the source with its line
numbers. For a window, the steps before the window's first line still matter: a step in the window may consume a
goal that a step before the window created.

`worksheet.md` 列出全部 15 道题。P01 到 P12 是完整的证明；W1 到 W3 是长证明中的窗口。每道题给出模块、声明名、文件和需要重建的行，并附带标有行号的源码。对窗口题来说，窗口第一行之前的步骤依然重要：窗口里的步骤可能消耗了窗口之前某个步骤产生的目标。

## Filling in the answers / 填写答案

`answers.xlsx` has one sheet per item. In the "Steps 步骤" table, write one row per step in source order: its line,
its tactic text, and notes; for a window, also Y or N for whether the step consumes a goal created by a step
outside the window. In the "Edges 边" table, write one row per edge: the number of the step that created the goal
and the number of the step that consumes it, with any doubt about the edge in its Notes column. Steps are numbered
from 0 in your order, as the "#" column shows. `instructions.md` gives the definition, what to write when one
tactic gives several steps (section 4), and two worked examples; read it before the first item.

`answers.xlsx` 每道题一个工作表。在"Steps 步骤"表中，按源码顺序每个步骤写一行：行号、策略文本和备注；窗口题还要填 Y 或 N，表示该步骤是否消耗了窗口外某个步骤产生的目标。在"Edges 边"表中，每条边写一行：产生该目标的步骤编号，以及消耗它的步骤编号；对这条边的疑问写在该行的备注栏。步骤按你列出的顺序从 0 开始编号，即"#"一列所示的编号。`instructions.md` 给出了定义、一个策略产生多个步骤时该怎么写（第 4 节）以及两道例题，请在做第一题之前读完。

## Handing in / 交回

Send the filled `answers.xlsx` to Bob. It is committed to the repository before any comparison is run, and the
comparison, with every disagreement and how it was settled, is reported in this experiment's README.

把填好的 `answers.xlsx` 发给 Bob。它会先提交到仓库，然后才进行比对；比对结果，以及每处分歧及其裁定方式，都会写进本实验的 README。
