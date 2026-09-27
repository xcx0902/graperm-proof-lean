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
| `GrapermProof/BlockTree.lean` | 结论二 |
| `GrapermProof/CheckAxioms.lean` | `#print axioms` 检查 |

## 公理

`CheckAxioms.lean` 报告全部目标定理仅依赖 `propext`、`Classical.choice`、`Quot.sound`，
不含 `sorryAx`。
