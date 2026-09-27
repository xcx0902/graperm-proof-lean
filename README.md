# graperm-proof

把 P11832（外平面图上求字典序最小的非交叉顶点排列）题解 `editorial.md` 中的两条关键结论，
完整地形式化到 Lean 4 / Mathlib。全项目 `sorry`-free，`lake build` 通过。

## 两条结论

**结论一（`GrapermProof/OuterCycle.lean`）**
> 对于至少有三个点的点双连通分量，任取一个不交叉的圆周排列，其外边界必是一条经过所有顶点的简单环。

形式化为 `Graperm.outer_cycle_is_hamiltonian`（外边界是哈密顿环）与
`Graperm.hamiltonian_cycle_uses_outer_edges`（非交叉哈密顿环只能沿外环取边，
从而外环顺序唯一，只余正向/反向两种）。

**结论二（`GrapermProof/BlockTree.lean`）**
> 圆方树上递归构造确实为字典序最优方案。

在抽象根化圆方树 `Part`（圆点 `round v cs` / 方点 `block cs`）上定义：

* `Valid` / `ValidList`：递归生成的全部合法排列；
* `seq`：贪心构造 —— 圆点处把各儿子序列与自身单元素按首元素排序后拼接
  （`sortHead`），方点处取外圈两方向中字典序较小者（`blockChoice`）；
* `WF` / `Sep`：刻划「不同儿子顶点集两两不交、圆点不属于任何儿子」。

主要结论：

* `Part.seq_valid`：贪心排列合法；
* `Part.seq_min`：任意合法排列 `l` 满足 `seq p ≤ l`（字典序最优）；
* `Part.seq_nonempty` / `Part.Valid.length_eq`：非空性与长度不变量。

## 模块结构

| 文件 | 内容 |
| --- | --- |
| `GrapermProof/Basic.lean` | 循环序、非交叉（`Between`/`Crosses`）、可容许排列框架 |
| `GrapermProof/OuterCycle.lean` | 结论一 |
| `GrapermProof/SortOpt.lean` | 抽象列表组合引理（`flatten_sorted_min`、`blockChoice`、首元素单调性） |
| `GrapermProof/SortHead.lean` | 按首元素的插入排序 `sortHead` 及其性质 |
| `GrapermProof/DomSort.lean` | 分块支配关系 `Dom` / `Dom2` 与「排序保持支配」 |
| `GrapermProof/BlockTree.lean` | 结论二（抽象圆方树模型内的最优性） |
| `GrapermProof/Separation.lean` | 结论二的图论前提：交错与连续性（见下） |
| `GrapermProof/Arrange.lean` | 圆周 ↔ 线性排列的桥（见下） |
| `GrapermProof/Assemble.lean` | 连续段的合并引理与「圆上连续 ⇒ 占排列一段」（见下） |
| `GrapermProof/Consists.lean` | 几何 → `Part.Valid` 的装配与闭环（见下） |
| `GrapermProof/BlockOrder.lean` | 连续段的**顺序**：按位置排列 ⇒ 拼接即 `flatten`（见下） |
| `GrapermProof/GeoOrder.lean` | `TreeOrdered → GeoOrder`，消掉最后的顺序假设（见下） |
| `GrapermProof/CheckAxioms.lean` | `#print axioms` 检查 |

## 结论二的补全：图论前提与圆周/线性之桥

抽象模型 `Part`/`Valid` 之外，题解「没有遗漏更优排列」依赖一条图论事实。
已形式化如下（`GrapermProof/Separation.lean`，全部无 `sorry`）：

* `CircOrder.alternates_swap` —— 「端点交错」关于两条弦对称；
* `walk_alternates_edge` —— 游走两端分居弦 `{s,t}` 两侧时，必有某条边跨过 `{s,t}`
  （离散介值定理，对游走归纳，不涉及交叉假设）；
* `no_alternation_of_connectedIn` —— **题解的「基础事实」**：两个顶点不交、
  各自内部连通的子图，顶点不可能在圆周上 `A,B,A,B` 交错出现
  （对 `B` 内路径用上一条引理得边 `{u,v}`，再由对称性对 `A` 内路径用一次，
  得到一对真正交叉的边，与 `IsRealizable` 矛盾）；
* `circle_contiguous_of_connected_complement` —— 若 `A` 与其补集都内部连通，
  则 `A` 在圆周上占一段弧。

`GrapermProof/Arrange.lean` 把圆周结论搬到线性排列上：

* `arrangement σ` —— 由圆序诱导的答案排列（按位置 `0,…,n-1` 排列）；
* `seg` / `seg_append` —— 排列的区间段及其拼接；
* `LinearContig` 与 `linear_contig_of_circle` —— 圆上连续的一段，若**不含位于
  位置 `0` 的根**，则在线性排列中也连续（根正好排除了「跨越排列首尾」的缠绕）。

## 结论二的补全（续）：区间合并与闭环

`GrapermProof/Assemble.lean` 补齐「儿子各占一段 ⇒ 可以按出现顺序拼接」这一装配步骤：

* `IsRun L m`：`m` 作为连续段出现在 `L` 中（`L = pre ++ m ++ post`）；
  配套一组剥离引理（`isRun_cons_of_not_mem`、`isRun_append_left/right`、`isRun_of_subrun`、
  `isRun_trans`、`nodup_of_isRun`）；
* **`merge_runs`**（合并引理）：一列互不相交、各自连续、且覆盖 `L` 的段，
  可以按位置顺序拼成 `L`：

  ```
  L.Nodup → (∀ b ∈ bs, IsRun L b) → 两两不交 → 覆盖 L → bs.Nodup
    → ∃ T, T.Perm bs ∧ L = T.flatten
  ```

  证明对段数做强归纳：首元素所在的段必然是 `L` 的前缀（否则首元素与该段最后一个元素
  之间会夹住不属于该段的顶点，与连续性矛盾）。
* `mem_seg` / `seg_nodup` / `arrangement_nodup`：区间段的成员刻画，答案排列无重复；
* **`isRun_of_linear_contig`**：线性连续的顶点集恰好占答案排列的一段；
* **`isRun_restrict`**：把圆上的连续性沿圆方树向下传递（父区间内的子树也连续）。

`GrapermProof/Consists.lean` 完成闭环：

* `Consists σ p L`：`L` 列出 `p` 的顶点且每个儿子占 `L` 的一个连续段、彼此不交；
  圆点处自身可与儿子段任意穿插，方点处必须按外环正序或逆序；
* **`valid_of_consists`**：`Consists σ p L → Part.Valid p L`（圆点处正是 `merge_runs`）；
* `GeoWF` / `AllContig` / `GeoOrder`：几何输入（树结构良好、每棵子树在圆上连续、
  方点遵外环顺序）；
* **`consists_of_geometry`**：由几何输入构造 `Consists`（对圆方树互递归）；
* **`arrangement_valid`** / **`seq_le_arrangement`**：

  ```
  Part.WF p → GeoWF p → AllContig σ p → GeoOrder σ p
    → partVerts p = elems (arrangement σ)
    → Part.seq p ≤ arrangement σ
  ```

  即：贪心递归构造字典序地不大于**任意**非交叉圆序所诱导的排列。

## 结论二的补全（续二）：方点处的顺序条件（`GeoOrder` 已是定理）

方点处「各儿子按外环正序或完全反序出现」这一条**不再需要假设**——它已被证明。
值得注意的是它并不依赖结论一：完备性方向在方点处只用到了「各儿子在圆上各占一段连续区间」
（由 `Separation` 给出）加上「儿子在树中的存储顺序 = 圆上的顺序」（圆方树的构造性质）。

`GrapermProof/BlockOrder.lean`（纯组合，不含任何图论）：

* **`arrangement_pairwise`** —— 答案排列按圆周位置严格递增
  （`arrangement σ = seg σ 0 n`，第 `i` 项就是位置 `i` 的顶点）；
* **`pos_lt_of_before_in_run`** —— 在答案排列的任一连续段 `pre ++ mid ++ post` 中，
  `pre` 的顶点位置都小于 `mid` 的顶点（列表顺序 = 位置顺序）；
* `posSep` / `VertsByPos` —— 「`A` 的顶点全都先于 `B`」/「一列顶点集按位置递增排列」；
* **`flatten_eq_of_runs_by_pos`** —— 互不相交、非空、覆盖 `L` 的连续段，若按位置递增
  排列，则 `L` 恰为 `ms.flatten`。归纳关键：`ms` 的第一段必是 `L` 的**前缀**，
  否则排在它之前的顶点属于某段 `m'`，`m' = m` 与 `L.Nodup` 矛盾、`m'` 更靠后则
  与位置递增矛盾；
* **`block_runs_order`** —— 递增则 `L = ms.flatten`，反序则 `L = ms.reverse.flatten`。
  这正是方点处「只能正序或完全反序」的精确形式。

`GrapermProof/GeoOrder.lean`（树 → 顺序）：

* `Aligned cs ms` —— `ms` 的第 `i` 段恰好列出 `cs` 的第 `i` 个儿子的顶点
  （已作为新子句加进 `ChildData`，使顺序断言有精确含义）；
* **`vertsByPos_of_aligned`** —— 把「树的儿子按圆上顺序存储」传递给「各段按位置顺序排列」；
* **`TreeOrdered σ p`** —— **唯一剩余的树侧假设**：方点的儿子按圆上顺序存储
  （正序或完全反序），圆点处仅向下传递；
* **`geoOrder_of_treeOrdered`** —— `TreeOrdered σ p → GeoOrder σ p`
  （对圆方树互递归，方点处调用 `block_runs_order`）；
* **`arrangement_valid_of_tree`** / **`seq_le_arrangement_of_tree`** —— 闭环：

  ```
  Part.WF p → GeoWF p → AllContig σ p → TreeOrdered σ p
    → partVerts p = elems (arrangement σ)
    → Part.seq p ≤ arrangement σ
  ```

**仍未形式化的剩余部分**：`Part.WF` / `GeoWF` / `AllContig` / `TreeOrdered` 这四条
描述了真实圆方树应当满足的性质，但「题解算法造出的树确实满足它们」尚未形式化
（需把圆方树构造、以及度数为 2 的点消去过程本身写进 Lean），跨连通块合并贪心亦然。
这些已不含关于「排列 / 交叉 / 字典序」的数学难点。

## 公理

`CheckAxioms.lean` 报告全部目标定理仅依赖 `propext`、`Classical.choice`、`Quot.sound`，
不含 `sorryAx`。
