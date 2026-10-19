# Reconstructing goal-origin graphs by hand / 手工重建目标起源图

Each section is given in English and then in Chinese. Where the two seem to differ, the English text is the
definition the derivation program implements.

每一节先给英文，再给中文。两者如有出入，以英文为准：英文是推导程序所实现的定义。

## 1. What you write down / 你要写出什么

For each item of `worksheet.md`, write down the **steps** of its goal-origin graph in source order, each with the
source line where it starts and its tactic text, and its **edges**: a pair [i, j] of step numbers (0-based, in
your step order) meaning that step i created a goal that step j consumes. For a **window** item, write down only
the steps on the window's lines, the edges between them, and, for each of these steps, whether it consumes a goal
created by a step outside the window (Y or N). Note anything you were unsure of.

对 `worksheet.md` 中的每一题，按源码顺序写出它的目标起源图（goal-origin graph）的**步骤**（step），每个步骤写明它开始的源码行号和策略（tactic）文本；再写出**依赖边**（edge）：一对步骤编号 [i, j]（从 0 开始，按你列出的步骤顺序编号），表示步骤 i 产生的某个目标被步骤 j 消耗。**窗口**类题目只写窗口所含行上的步骤、这些步骤之间的边，并对每个步骤标明它是否消耗了窗口外某个步骤产生的目标（Y 或 N）。凡是拿不准的地方，都写进备注。

## 2. The definition / 定义

Lean records a proof's elaboration as an *info tree*: one node for each tactic it elaborates, nested as the
tactics are. Steps are derived from these nodes.

Lean 把一个证明的繁饰（elaboration）过程记录为一棵*信息树*（info tree）：它繁饰的每个策略对应一个节点（node），节点的嵌套与策略的嵌套一致。步骤由这些节点推导出来。

- A node **produces** the goals present after it and absent before it. It **consumes** the goals that meet three
  conditions: present before it; absent after it; and absent before every later node of the proof outside the
  node's own subtree. Focusing constructs such as `·` and `case` hide goals; a hidden goal is not closed, so it is
  not consumed. In the third condition, later nodes inside the node's own subtree do not count: a tactic whose
  internal node shows the goal it closes (the internal node of `simpa ... using h`) still consumes that goal.
- The **origin** of a goal is the deepest node producing it. A `have ... := by` node produces its continuation goal
  itself; a multi-binder `intro` produces through its last child. A goal that no node produces (the case goals of
  `induction ... with`, `cases ... with`, `case tag x y =>`, the goal of a nested `by`, the goals of the lines of a
  `calc`) originates in the deepest node that encloses its first mention, holds at least one goal, and does not
  hold this one. A goal for which neither rule finds a node has no origin (the statement's goal, a `decreasing_by`
  proof obligation).
- A node is a **step** when it is the origin of a goal or when it consumes a goal that none of its descendants
  consumes; every other node is a **container**. An origin that consumes nothing itself as a step, because a
  descendant consumes the goal it held (`simpa ... using (by tac)`, whose `simp` part is a child node), is merged
  into that descendant, so that one tactic is one step.
- A step produces the goals it originates, and consumes the goals it consumes as a node minus those consumed by its
  descendant steps.
- A step is **live** when it consumes a goal of a root node (the statement, a `decreasing_by` obligation, a nested
  `by` in a term) or a goal produced by a live step. The other steps belong to failed attempts of `first`, `try`,
  and `repeat`, whose nodes Lean keeps; they are dropped.
- A step **depends on** the origin of every goal it consumes: this is an edge. Write each pair once, even when
  step j consumes several goals that step i created.

- 一个节点**产生**（produce）的目标，是它之后存在、它之前不存在的目标。它**消耗**（consume）的目标，是同时满足以下三条的目标：在它之前存在；在它之后不存在；在证明中位于它自身子树之外的任何后续节点之前，都不存在。`·`、`case` 这类聚焦（focusing）结构会隐藏目标，被隐藏的目标并没有关闭，所以不算被消耗。判断第三条时，不考虑位于该节点自身子树之内的后续节点：如果一个策略的内部节点显示着它正要关闭的目标（例如 `simpa ... using h` 的内部节点），这个策略仍然消耗该目标。
- 一个目标的**起源**（origin）是产生它的最深的节点。`have ... := by` 节点自己产生延续目标（continuation goal）；带多个绑定变量的 `intro` 通过它的最后一个子节点产生目标。没有任何节点产生的目标（`induction ... with`、`cases ... with`、`case tag x y =>` 的分支目标，项中嵌套的 `by` 的目标，`calc` 各行的目标），其起源是这样的最深节点：包含它第一次出现的位置，持有至少一个目标，并且不持有它。按这两条规则都找不到节点的目标没有起源（定理陈述本身的目标、`decreasing_by` 的证明义务）。
- 一个节点如果是某个目标的起源，或者消耗了一个它的后代都没有消耗的目标，它就是**步骤**；其余节点都是**容器**（container）。如果一个起源节点因为它所持有的目标被某个后代消耗，自己（作为步骤）什么也不消耗（例如 `simpa ... using (by tac)`，其中 `simp` 部分是一个子节点），就把它并入那个后代，使一个策略对应一个步骤。
- 一个步骤产生它作为起源的那些目标；它消耗的目标，是它作为节点消耗的目标减去它的后代步骤消耗的目标。
- 如果一个步骤消耗了某个根节点的目标（定理陈述、`decreasing_by` 的证明义务、项中嵌套的 `by`），或者消耗了某个由存活步骤产生的目标，它就是**存活的**（live）。其余步骤属于 `first`、`try`、`repeat` 中失败的尝试，Lean 保留了它们的节点；这些步骤要去掉。
- 一个步骤**依赖于**（depends on）它所消耗的每个目标的起源：这就是一条边。即使步骤 j 消耗了步骤 i 产生的多个目标，[i, j] 也只写一次。

## 3. How Lean behaves / Lean 的实际行为

The definition relies on these facts about Lean 4.

上面的定义依赖 Lean 4 的以下行为。

1. Lean's info tree is not always one node per tactic as written: `rw [a, b]` has one node per rewrite rule, and
   one for its closing `rfl` when that closes the goal (placed on the line where the `rw` starts); `intro x y` has
   one per binder; `conv_lhs` and `conv_rhs` insert a `conv` node; `cases h : e with` has two; a `next` or `case`
   that names hypotheses (`next x y =>`, `case tag x y =>`) is a node, and by fact 2 a step. A tactic that runs on
   several goals (the second tactic of `t <;> s`, the body of `all_goals`) is one node, hence possibly one step,
   per goal it runs on. Where this list does not settle a case, Lean's own elaboration does: the goals it displays
   between tactics, or Lean's source (the tactic's implementation).
2. Almost every tactic that changes a goal (its target or its local context) replaces that goal with a new goal,
   and a tactic that closes a goal produces no goal. So a step that transforms a goal consumes the old goal and
   originates the new one. `show` with the goal's own statement leaves the goal as it was, so it is not a step.
3. Focusing (`·`, and `next` or `case tag =>` without new names) and tactic sequences only select or hide goals, so
   they are containers.

1. Lean 的信息树并不总是"源码里一个策略对应一个节点"：`rw [a, b]` 每条改写规则一个节点，如果最后的 `rfl` 关闭了目标，它也有一个节点（记在 `rw` 开始的那一行）；`intro x y` 每个绑定变量一个节点；`conv_lhs`、`conv_rhs` 会插入一个 `conv` 节点；`cases h : e with` 有两个节点；引入新名字、给假设命名的 `next` 或 `case`（如 `next x y =>`、`case tag x y =>`）是一个节点，并且按第 2 条是一个步骤。作用于多个目标的策略（`t <;> s` 中的第二个策略、`all_goals` 的主体），它作用于几个目标，就有几个节点，因此可能是几个步骤。上述清单没有覆盖的情况，以 Lean 自己的繁饰过程为准：看它在策略之间显示的目标，或者看 Lean 的源码（该策略的实现）。
2. 几乎所有改变目标（目标的结论，即 ⊢ 右边的命题，或局部上下文）的策略，都会用一个新目标替换原目标；关闭目标的策略不产生目标。所以一个变换目标的步骤，消耗旧目标，并且是新目标的起源。用目标本身的陈述写的 `show` 不改变目标，因此不是步骤。
3. 聚焦（`·`，以及不引入新名字的 `next` 和 `case tag =>`）和策略序列只是选择或隐藏目标，因此是容器。

## 4. Lines and order / 行号与顺序

A step's line is the line where its info-tree node starts (for a rewrite rule, the rule's own line). Several steps
on one line are listed in the order they run. When one tactic gives several steps (each rule of a `rw`, its closing
`rfl`, each binder of an `intro`, the second tactic of `t <;> s` on each goal), write one row per step with its line
and a tactic text that says which part it is, for instance `rw [h₁]` rule 2, `rfl` (closing), `intro y`, `s` (goal
2). Long proofs are expected: list every step. The comparison matches steps by line and by order within a line, and
then compares edges.

步骤的行号是它在信息树中的节点开始的那一行（改写规则则取该规则自己所在的行）。同一行上有多个步骤时，按执行顺序列出。如果一个策略产生多个步骤（`rw` 的每条规则、收尾的 `rfl`、`intro` 的每个绑定变量、`t <;> s` 中作用于每个目标的第二个策略），每个步骤写一行，填它的行号，策略文本写明是哪一部分，例如 `rw [h₁]` 第 2 条规则、`rfl`（收尾）、`intro y`、`s`（第 2 个目标）。证明可能很长，每个步骤都要列出。比对时按行号以及同一行内的先后顺序匹配步骤，再比较边。

## 5. Worked examples / 例题

These two proofs come from `fixtures/Fixtures.lean` in this repository and are outside the audit's sample. Their
graphs below are the derivation program's output.

下面两个证明来自本仓库的 `fixtures/Fixtures.lean`，不在本次审核的样本中。下面给出的图就是推导程序的输出。

```lean
14  theorem mixed (p q : Prop) (hp : p) (hq : q) : (p ∧ q) ∧ (q ∧ p) := by
15    constructor
16    · constructor
17      · exact hp
18      · exact hq
19    · constructor
20      · exact hq
21      · exact hp
```

| # | Line 行 | Tactic 策略 |
|---|---|---|
| 0 | 15 | `constructor` |
| 1 | 16 | `constructor` |
| 2 | 17 | `exact hp` |
| 3 | 18 | `exact hq` |
| 4 | 19 | `constructor` |
| 5 | 20 | `exact hq` |
| 6 | 21 | `exact hp` |

Edges / 边: [0, 1], [1, 2], [1, 3], [0, 4], [4, 5], [4, 6]. The `·` nodes are containers: they only focus a goal.
The first `constructor` creates the two goals that the two inner `constructor` steps consume.

`·` 节点是容器，只是聚焦某个目标。第一个 `constructor` 产生两个目标，分别被里面的两个 `constructor` 步骤消耗。

```lean
31  theorem nested_cases (p q r : Prop) (h : p ∨ q) (hr : r) : (q ∨ p) ∧ r := by
32    constructor
33    · cases h with
34      | inl hp => exact Or.inr hp
35      | inr hq => exact Or.inl hq
36    · exact hr
```

| # | Line 行 | Tactic 策略 |
|---|---|---|
| 0 | 32 | `constructor` |
| 1 | 33 | `cases h with` |
| 2 | 34 | `exact Or.inr hp` |
| 3 | 35 | `exact Or.inl hq` |
| 4 | 36 | `exact hr` |

Edges / 边: [0, 1], [1, 2], [1, 3], [0, 4]. No node produces the case goals `inl` and `inr`; they originate in
`cases`, the deepest node that encloses their first mention, holds at least one goal, and does not hold them.

`inl` 和 `inr` 两个分支目标没有任何节点产生；它们的起源是 `cases`：包含它们第一次出现的位置、持有至少一个目标、并且不持有它们的最深节点。
