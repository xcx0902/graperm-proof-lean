# AUDIT.md — 形式化审计报告

**审计对象**：`graperm-proof`（Lean 4.34.0 + mathlib，共 7 个 `.lean` 文件，1531 行）
**对照材料**：本工作区根目录下的 `editorial.md`（P11832《图排列》题解）与 `problem.md`（题面），
以及 `README.md` 中声明的「两条结论」。
**结论摘要**：两条结论**在各自声明的形式化范围内是正确的**；结论一忠实且完整；结论二在所建立的
抽象圆方树模型内忠实且正确，但**模型与真实图/圆方树/非交叉排列之间的桥梁没有形式化**，
因此不能说「最终算法的字典序最优性已被端到端证明」。详见第 5 节。

> 说明：本次审计针对的是本工作区自带的 `editorial.md` / `problem.md`（P11832 图排列），
> 与 `README.md` 声明的两条结论一致。若用户所指的是另一个 `two-doors` 项目的题解，
> 则与本仓库无关，需另行审计。

---

## 0. 审计方法与「未修改项目」承诺

| 动作 | 结果 |
| --- | --- |
| 通读全部源码（`Basic / OuterCycle / SortOpt / SortHead / DomSort / BlockTree / CheckAxioms`） | 完成 |
| `lake build` | `Build completed successfully (3117 jobs)`，无错误输出 |
| 源码扫描 `sorry / axiom / admit / unsafe / opaque` | 全部命中仅出现在 `CheckAxioms.lean` 的 `#print axioms` 行，无实际声明 |
| `#print axioms` 检查 | 见 §1.2 |
| 抽象语法树上的独立探针（`#eval`、具体命题的机器证明） | 见 §1.3、§1.4；探针文件写在 `/tmp`，**未写入项目目录** |
| `git status --short` | 干净（无跟踪文件被改动；`lake build` 只写 `.lake/`，已被 `.gitignore` 忽略） |

---

## 1. 机器验证记录（可复现）

### 1.1 构建

```
$ cd graperm-proof-lean && lake build
Build completed successfully (3117 jobs).
```

### 1.2 公理依赖（在 `/tmp` 中用 `lake env lean` 对已编译模块重跑 `#print axioms`）

```
Graperm.succ_adj                          → [propext, Classical.choice, Quot.sound]
Graperm.outer_cycle_is_hamiltonian        → [propext, Classical.choice, Quot.sound]
Graperm.hamiltonian_cycle_uses_outer_edges→ [propext, Classical.choice, Quot.sound]
Graperm.Part.seq_nonempty                 → [propext, Classical.choice, Quot.sound]
Graperm.Part.seq_valid                    → [propext, Classical.choice, Quot.sound]
Graperm.Part.seq_min                      → [propext, Classical.choice, Quot.sound]
Graperm.Part.Valid.length_eq              → [propext, Classical.choice, Quot.sound]
Graperm.Part.part_spec                    → [propext, Classical.choice, Quot.sound]
Graperm.Dom.sortHead_flatten_le_flatten   → [propext, Classical.choice, Quot.sound]
Graperm.flatten_sorted_min                → [propext, Classical.choice, Quot.sound]
```

无 `sorryAx`，与 `README.md` 第 43–46 行的声明一致。✅

### 1.3 `seq`（结论二的贪心构造）在抽象圆方树上的实际取值

```
round 1 [block [round 3 []]]                                   → [1, 3]
round 2 [block [round 4 []]]                                   → [2, 4]
round 1 [block [round 5 []], block [round 2 []]]               → [1, 2, 5]
block  [round 4 [], round 2 []]                                → [2, 4]      -- 反向更优
round 3 [block [round 5 [block [round 7 []]], round 1 []]]     → [1, 5, 7, 3]
```

- 前两行正是 `problem.md` 样例 1 中两个连通块（桥 `{1,3}`、`{2,4}`）的块内序列；
  题解的跨块合并贪心再把它们拼成 `1 2 4 3`，与样例输出一致（合并步骤本身未形式化，见 §4–E）。
- 第 3 行验证「圆点处把各儿子与自身按首元素排序」；第 4 行验证「方点处两方向取字典序较小者」；
  第 5 行验证递归嵌套。行为与 `editorial.md` 描述完全吻合。✅

### 1.4 `Crosses` 定义的语义探针（结论一的前提是否被正确编码）

用项目自身的算术引理，在恒等圆序上机器证明了两个具体命题（均已通过）：

```
-- 端点交错 (0,2) 与 (1,3)：Crosses 为真
example : id4.Crosses (iter z 0) (iter z 2) (iter z 1) (iter z 3) := ...   ✔
-- 端点不交错 (0,1) 与 (2,3)：Crosses 为假
example : ¬ id4.Crosses (iter z 0) (iter z 1) (iter z 2) (iter z 3) := ...  ✔
```

即 `Crosses a b c d` ⟺ 四个端点互异且 `c,d` 中恰有一个落在 `a→b` 的前向开弧上 ⟺ 端点交错，
与题面「不存在 `a_i < a_j < b_i < b_j`」在圆周化后等价。✅

### 1.5 一处可测性备注

`CircOrder.fwd` / `CircOrder.iter` / `CircOrder.succ` 被标记为 `noncomputable`，
因此 `IsRealizable` 无法用 `decide` / `native_decide` 直接求值
（实测报 `dependsOnNoncomputable`）。这不影响正确性，但使得「用小规模穷举交叉验证结论一」
变得不便；§1.4 的探针正是为了绕开这一点而改用 `iter` + 项目引理表述。

---

## 2. 结论一审计：点双分量的外边界是经过所有顶点的简单环（且唯一）

**editorial 原文要点**

1. 所有顶点在外面上 ⇒ 外边界经过所有顶点；若外边界重复经过某点 `x`，删 `x` 后不连通，与点双连通性矛盾
   ⇒ 外边界是**哈密顿环**。
2. 该外环**唯一**：圆周上的非交叉哈密顿环只能沿圆周相邻顺序连边（用弦会导致交叉）
   ⇒ 任何哈密顿环只能用外环的边 ⇒ 分量内的顺序只剩沿外环正向/反向两种。

**形式化对照**

| editorial 子结论 | Lean 定理 | 判定 |
| --- | --- | --- |
| 「圆序上相邻的两点必相连」（⇒ 外边界是覆盖全部顶点的简单环） | `Graperm.succ_adj`（`OuterCycle.lean:29`）、`Graperm.outer_cycle_is_hamiltonian`（:159） | ✅ 正确 |
| 唯一性：任何（非交叉）哈密顿环只用外环的边 | `Graperm.hamiltonian_cycle_uses_outer_edges`（:172） | ✅ 正确 |
| 「不交叉」= 端点交错 | `CircOrder.Between`（`Basic.lean:39`）、`CircOrder.Crosses`（:45）、`IsRealizable`（:189） | ✅ 已机器验证（§1.4） |
| 点双连通 | `IsTwoConn`（`Basic.lean:194`）：连通 + 删去任一点仍连通 | ✅ 标准且充分（n≥3） |

**证明路线核对（`succ_adj`）**：假设 `v₀` 与其后继不相邻，取沿圆周从 `v₀` 起的第一个邻点 `uᵢ`（`i≥2`），
令 `T` 为 `v₀` 与 `uᵢ` 之间的顶点。由非交叉性，`T` 中任一点的邻点只能在 `T` 内或等于 `uᵢ`
（否则边 `u₀uᵢ` 与 `T` 的出边交错），于是任何从 `T` 出发且避开 `uᵢ` 的游走都留在 `T` 内；
而点双连通性给出一条从 `u₁∈T` 到 `v₀∉T` 且避开 `uᵢ` 的游走，矛盾。
该论证与 editorial 的结论一致，**且更强**：它完全避开了 editorial 中「外面 / 外边界」等平面图拓扑概念，
只用了组合化的非交叉条件 + 2-连通性，因而不依赖任何平面图库。这是优点，也是一个需要记录的差异
（见 §3-D）。

**判定：通过（忠实 + 证明独立可信）。**

---

## 3. 结论一的差异与缺口

- **A（轻微·表述）**：`outer_cycle_is_hamiltonian` 的类型只给出 `∀ v, G.Adj v (σ.succ v)`，
  没有显式打包「`v, succ v, succ² v, …` 是顶点互异的简单环」。该事实的两个要件在 `Basic.lean` 中已具备
  （`CircOrder.iter_inj`、`CircOrder.iter_n`），一步可得，但项目里没有这条定理。
- **B（轻微·适用范围）**：定理以「整张图 `G` 二连通」表述，editorial 说的是「≥3 个点的**点双连通分量的诱导子图**」。
  二者等价，但把结论用到分量上时，「限制到分量顶点后仍非交叉、仍二连通」这一步需使用者自行完成，未形式化。
- **C（轻微·假设略强）**：`hamiltonian_cycle_uses_outer_edges` 要求 `IsTwoConn H`；对 `n≥3` 的哈密顿圈该条件自动成立，
  故无害。「哈密顿环」用 `H ≤ G` + 每点恰有 2 个 `H`-邻居 + 二连通 编码；证明实际上只用到「每点恰有 2 个邻居」
  与「`H` 含全部外环边」，并未用到「2-正则 + 连通 = 单圈」这一事实，所以不影响结论可靠性。
- **D（中性·路线差异）**：editorial 用到「外面 / 外边界重复经过顶点」的平面嵌入论证，形式化未涉及平面性。
  结论相同、前提更少，属于可接受的（且更稳健的）改写。

---

## 4. 结论二审计：圆方树上的递归构造确实是字典序最优

**editorial 要点**

1. 合法排列的结构：除公共割点可插在各部分之间外，每个儿子部分必须**连续出现**；
   点双分量内的顺序只剩正向/反向两种。
2. 贪心：圆点处把各儿子序列与自身 `[u]` 按**首元素**排序后拼接；方点处比较 `f(v₁)` 与 `f(vₜ)`，取首元素较小的方向。
3. 只需比较首元素，因为各部分顶点集不交、首元素互异。
4. 归纳：儿子内部已取最小 ⇒ 先放首元素最小者最优。
5. 根是连通块最小顶点 ⇒ 每个块的序列以该块最小顶点开头（供跨块合并使用）。

**形式化对照**

| editorial 子结论 | Lean 定义/定理 | 判定 |
| --- | --- | --- |
| 抽象（根化）圆方树 | `Part V`（`BlockTree.lean:38`）：`round v cs` / `block cs` | ✅ |
| 圆点处：儿子序列与 `[v]` **任意排列**后拼接 | `Valid`（:62）：`∃ T, T.Perm (ms ++ [[v]]) ∧ l = T.flatten` | ✅ 忠实 |
| 方点处：只剩正序/逆序两种 | `Valid`（:62）：`l = ms.flatten ∨ l = ms.reverse.flatten` | ✅ 忠实（旋转由父亲圆点固定，与 editorial 一致） |
| 贪心：圆点排序拼接 | `seq (.round v cs) = (sortHead (seqList cs ++ [[v]])).flatten`（:82） | ✅ 一致 |
| 贪心：方点取较优方向 | `blockChoice`（`SortOpt.lean:201`） | ✅ 见下 |
| 最优性 | `Part.seq_min : WF p → Valid p l → seq p ≤ l`（:429） | ✅ 模型内正确 |
| 合法性 / 非空 / 长度不变 | `seq_valid`（:423）、`seq_nonempty`（:419）、`Valid.length_eq`（:434） | ✅ |
| 各部分顶点集不交、圆点不属于儿子 | `Sep`（:89）、`WF`（:99）、`nodup_map_of_disjoint`（:134） | ✅ 作为**假设**给出 |
| 只需比较首元素 | `Dom.sortHead_flatten_le_flatten`（`DomSort.lean:248`）、`flatten_sorted_min`（`SortOpt.lean:115`）、`lt_iff_head_lt`（:173） | ✅ |
| 方点两方向的单调性 | `Dom2.flatten_le`、`Dom2.reverse`（`DomSort.lean:282/:308`） | ✅ |

**关键实现细节复核（均为正面发现）**

- **方点方向选择**：editorial 说比较 `f(v₁)` 与 `f(vₜ)`；项目用 `blockChoice` 直接比较整条拼接串。
  在首元素互异（由 `Sep` 保证）时两者等价，且后者不依赖该前提，更稳健。✅
- **长度不变式**：`List` 的字典序实例在长度不等时还带有「前缀更小」的成分（实测 `[] < [1]` 为真、`[1,2] < [1]` 为假）。
  项目用 `Valid.length_eq` 保证参与比较的列表等长，从而字典序语义与题目完全一致 —— 这是一个被正确处理、
  容易出错的细节。✅
- **`Dom` / `Dom2` 双层设计**：圆点处儿子可重排，故用带显式匹配的 `Dom`（`erase_min` 逐个剥离最小块）；
  方点处顺序固定，故用位置化的 `Dom2`。与 editorial 指出的「两类自由度」一一对应。✅
- **非空性**全程维护（`Spec` 的 `seq p ≠ []`、`∀ x ∈ S, x ≠ []`），避免 `headV` 的 `Inhabited` 默认值造成退化。✅
- 反向分支同时反转两侧（`Dom2.reverse`）并处理长度不变（`rev_len`）。✅

**判定：在所给抽象模型内 —— 通过。**

---

## 5. 结论二的关键限制（需在使用结论前明确）

- **A（重要·保真度缺口）**：`Valid` 是一个**递归生成式**定义，即「合法排列」被直接定义为递归的输出集合。
  editorial 中最实质的一步 —— 「**没有遗漏更优的排列**」（基于「儿子必须连续出现」的交替 `A,B,A,B` 论证，
  以及「割点可插在中间」）—— **没有被证明**，而是被写进了定义。
  因此 `seq_min` 的正确含义是「在 `Valid` 这个模型内最优」，**而不是**「在所有非交叉排列中最小」。
  仓库中没有任何图、点双分量、圆方树、`Part` ↔ 实际子图、排列 ↔ 非交叉条件 的连接代码。
  这是本项目最大的范围缺口（对纯组合抽象而言是常见且自洽的切分，但结论必须据此表述）。
- **B（重要·假设未证）**：`WF` / `Sep`（儿子顶点集两两不交、圆点不属于任何儿子）是作为**假设**给出的，
  项目未证明真实圆方树满足它们（虽然它们确实是真的：不同块只在割点相交，而块序列已排除父亲方向）。
- **C（范围外·但被结论依赖）**：「根是连通块最小顶点 ⇒ 该块序列以最小顶点开头」未形式化。
  它是跨块合并贪心的输入前提。
- **D（范围外）**：editorial 中「消去度数为 2 的点以恢复外环」这一过程（含「最后只剩两个相邻点时，
  判断已收集边数是否等于分量点数来决定是否补最后一条边」）**完全未形式化**。这是从结论一到可运行算法的
  关键正确性环节。
- **E（范围外）**：跨连通块合并（「用堆按首元素贪心插入另一个连通块的两个相邻顶点之间」）**完全未形式化**。
  样例 1 的最终答案 `1 2 4 3` 需要这一步（§1.3 显示两个块内序列分别为 `[1,3]` 与 `[2,4]`）。
- **F（合理·范围外）**：复杂度分析、输入输出、数据结构（并查集 / 有序集合 / Tarjan）未形式化，符合 README 的声明范围。

---

## 5b. 第二轮：针对 §5-A/B 的补全（新增模块）

针对审计发现的最大缺口（`Valid` 缺少「合法排列 ⇔ 递归生成」这一方向），新增两个模块，
把缺失的**数学内容**补上，均已 `lake build` 通过、`#print axioms` 无 `sorryAx`。

**`GrapermProof/Separation.lean`（图论核心，全部无 sorry）**

| 定理 | 内容 |
| --- | --- |
| `CircOrder.fwd_add_mod / fwd_add_rev / fwd_rev_eq / fwd_of_lt / fwd_of_gt / fwd_eq_sub_of_le` | 圆周距离的算术（环绕、反向、分段） |
| `CircOrder.between_iff_not_between` | 任一点恰在两条开弧之一上 |
| `CircOrder.alternates_swap` | 「端点交错」对两条弦对称（非平凡，含完整算术） |
| `walk_alternates_edge` | 游走两端分居弦两侧 ⇒ 有一条边跨过该弦（离散介值定理） |
| `no_alternation_of_connectedIn` | **题解的「基础事实」**：不交且各自内部连通的两个子图不会 `A,B,A,B` 交错 |
| `circle_contiguous_of_connected_complement` | 自身与补集都内部连通 ⇒ 在圆周上占一段弧 |

其中 `no_alternation_of_connectedIn` 正是 `Valid` 的「儿子必须连续出现」所依赖的那条事实，
现在它是**定理**而不是假设：`walk_alternates_edge` 先用一次（在 `B` 内的路径上，得到跨过
`{a₁,a₂}` 的边 `{u,v}`），再由 `alternates_swap` 交换弦的角色，对 `A` 内的路径用第二次，
得到与 `IsRealizable` 直接矛盾的一对交叉边。

**`GrapermProof/Arrange.lean`（圆周 ↔ 线性）**

- `arrangement σ`：圆序诱导的答案排列；`seg` / `seg_append`：区间段与拼接；
- `LinearContig`、`linear_contig_of_circle`：圆上连续且不含位置 `0` 的根 ⇒ 线性排列中连续。
  这一条是必需的：圆上的「连续」允许绕过排列首尾（例如 `A` 的两个顶点分处排列两端），
  只有当根固定在位置 `0` 且不在该集合内时，绕回才被排除。

**仍未完成的两步（装配工作，无新数学难点）**

1. 区间合并引理：由「各儿子占互不相交的连续区间 ∪ 割点一个位置 = 父区间」
   推出父排列等于各儿子段按位置排序后的拼接（从而递归地落在 `Valid` 中）。
   建议形式：把区间写成 `[lo,hi)`，用 `seg_append` 归纳装配。
2. 方点处「外环顺序或反序」所需的**结论一之子集形式**：结论一目前针对整张图的
   `CircOrder n`，用于点双分量的顶点子集时，需要把「圆上下一个属于该分量的顶点」
   作为后继重述（证明结构与现有 `succ_adj` 相同）。

这两步完成后即可得到完整的：
`∀ σ, IsRealizable σ G → σ.pos root = ⟨0,_⟩ → seq p ≤ arrangement σ`。

## 5c. 第三轮：装配（区间合并 + 几何 → 合法排列）

针对 §5b 末尾列出的第 1 步，新增两个模块，把「各儿子占互不相交的连续区间」装配成
`Part.Valid`，**闭环完成**。全部 `lake build` 通过、`#print axioms` 无 `sorryAx`。

**`GrapermProof/Assemble.lean`（纯组合的区间合并）**

| 定义 / 定理 | 内容 |
| --- | --- |
| `IsRun L m` | `m` 作为**连续段**出现在 `L` 中（`L = pre ++ m ++ post`） |
| `isRun_cons_of_not_mem` / `isRun_append_left` / `isRun_append_right` / `isRun_of_subrun` | 连续段的剥离：从 `a :: L`、`pre ++ post`、`pre ++ L ++ post` 中删去与 `m` 无关的部分 |
| `isRun_trans` / `nodup_of_isRun` | 连续段的传递性与无重复性 |
| **`merge_runs`** | **合并引理**：一列互不相交、各自连续、且覆盖 `L` 的段，可以按位置顺序拼成 `L`，即 `∃ T, T.Perm bs ∧ L = T.flatten`。这正是「儿子各占一段 ⇒ 父排列是这些段的某个排列的拼接」 |

`merge_runs` 的证明对段数做强归纳：取 `L` 的首元素所在的那个段 `b`，由无重复性可知 `b` 必然
是 `L` 的**前缀**（否则首元素与 `b` 的最后一个元素之间会夹住一个不属于 `b` 的顶点，与连续性
矛盾），剥离 `b` 后递归。这正是题解「各儿子连续出现 ⇒ 可以按出现顺序拼接」的精确形式。

| 定义 / 定理 | 内容 |
| --- | --- |
| `mem_range'_bounds` / `mem_seg` / `seg_nodup` / `arrangement_nodup` | `seg` 区间段的成员刻画（`v ∈ seg σ lo len ↔ lo ≤ pos v < lo+len`），从而答案排列无重复 |
| **`isRun_of_linear_contig`** | 线性连续的顶点集恰好占答案排列的一段（取位置的最小/最大值，用 `Finset.min'` / `max'` 与 `seg_append` 构造） |
| `isRun_sub_of_runs` / **`isRun_restrict`** | 把圆上的连续性沿圆方树向下传递：父区间内、且圆上连续的子树顶点集，在父区间内也连续 |

**`GrapermProof/Consists.lean`（几何 → 合法排列）**

| 定义 / 定理 | 内容 |
| --- | --- |
| `partVerts` / `partDisjoint` / `partExcludes` | 子树顶点集、兄弟不交、圆点不属于任何儿子 |
| `Consists σ p L` | 接口谓词：`L` 列出 `p` 的顶点，每个儿子占 `L` 的一个连续段、彼此不交；圆点处圆点自身可与儿子段任意穿插；方点处必须按外环正序或逆序 |
| **`valid_of_consists`** | 一致 ⇒ 合法：圆点处用 `merge_runs` 得到「某个排列的拼接」，正是 `Part.Valid` 允许的形式 |
| `GeoWF` / `AllContig` / **`GeoOrder`** | 几何输入：树结构良好、**每棵子树在圆上连续**（由 `circle_contiguous_of_connected_complement` + `linear_contig_of_circle` 提供）、方点处遵外环顺序 |
| **`consists_of_geometry`** | 由几何输入构造出 `Consists`（对圆方树互递归，逐层用 `isRun_restrict` 取儿子段） |
| **`arrangement_valid`** / **`seq_le_arrangement`** | **闭环**：`Part.Valid p (arrangement σ)`，进而 `Part.seq p ≤ arrangement σ` |

于是 §5b 末尾的第 1 步已完成，缺口只剩第 2 步。

## 5d. 第四轮：`GeoOrder` 由假设变为定理（顺序条件已证明）

新增 `GrapermProof/BlockOrder.lean`（纯组合）与 `GrapermProof/GeoOrder.lean`（树 → 顺序），
把上面「仍未完成的一步」**消掉**：`GeoOrder σ p` 不再是假设，而是由 `TreeOrdered σ p` 推出。

**对上一轮判断的修正。** §5c 曾推测这一步需要「结论一之子集形式」（把 `succ_adj` 重述在点双
分量的诱导圆序上）。实际做完之后发现**并不需要**：完备性方向在方点处只用到了「各儿子在圆上
各占一段连续区间」＋「儿子在树中的存储顺序 = 圆上的顺序」，前者由 `Separation` 给出，后者是
圆方树**构造方式**的性质。结论一（外环是唯一哈密顿环）服务于构造方向的**可行性**（证明贪心
输出的排列确实非交叉），而本项目的 `Part.Valid` 是纯组合谓词，并不含「非交叉」这一语义，
所以结论一在此处本就无需介入。这是 §5c 的一处过度估计，在此更正。

**`GrapermProof/BlockOrder.lean`（纯组合，无图论）**

| 定义 / 定理 | 内容 |
| --- | --- |
| **`arrangement_pairwise`** | 答案排列按圆周位置严格递增（`arrangement σ = seg σ 0 n`，第 `i` 项就是位置 `i` 的顶点）；由 `range'_pairwise` + `List.pairwise_map` 得到 |
| **`pos_lt_of_before_in_run`** | 在答案排列的任一连续段内，列表顺序 = 位置顺序：段 `pre ++ mid ++ post` 中 `pre` 的顶点位置小于 `mid` 的顶点 |
| `posSep` / `VertsByPos` | 「`A` 的所有顶点在圆上都先于 `B`」/「一列顶点集按位置递增排列」 |
| **`flatten_eq_of_runs_by_pos`** | **顺序定理**：互不相交、非空、覆盖 `L` 的连续段，若按位置递增排列，则 `L` 就是它们的拼接 `ms.flatten` |
| **`block_runs_order`** | 递增则 `L = ms.flatten`；反序（`ms.reverse` 递增）则 `L = ms.reverse.flatten` |

`flatten_eq_of_runs_by_pos` 的归纳：取 `ms` 的第一段 `m`，证明它必是 `L` 的**前缀**——
否则 `L` 中有一个顶点 `x` 排在 `m` 之前，`x` 属于某段 `m'`：若 `m' = m` 则与 `L.Nodup` 矛盾；
若 `m'` 在 `ms` 中更靠后，则按位置递增有 `pos (m的元素) < pos x`，而按段内顺序有
`pos x < pos (m的元素)`，矛盾。剥离 `m` 后递归。

**`GrapermProof/GeoOrder.lean`（树 → 顺序）**

| 定义 / 定理 | 内容 |
| --- | --- |
| `Aligned cs ms` | `ms` 的第 `i` 段恰好列出 `cs` 的第 `i` 个儿子的顶点（已加进 `ChildData`） |
| **`aligned_imp_right` / `aligned_imp_left` / `aligned_snoc` / `aligned_reverse`** | 对齐的配套引理 |
| **`vertsByPos_of_aligned`** | 把「树的儿子按圆上顺序存储」传递给「各段按位置顺序排列」 |
| **`TreeOrdered σ p`** | **唯一剩余的树侧假设**：方点的儿子按圆上顺序存储（正序或完全反序）；圆点只向下传递 |
| **`geoOrder_of_treeOrdered`** | `TreeOrdered σ p → GeoOrder σ p`（对圆方树互递归，方点处调用 `block_runs_order`） |
| **`arrangement_valid_of_tree` / `seq_le_arrangement_of_tree`** | 闭环：`Part.Valid p (arrangement σ)`，进而 `Part.seq p ≤ arrangement σ` |

**机器验证**：`lake build` → `Build completed successfully (3123 jobs)`；源码扫描
`sorry / axiom / unsafe / admit / opaque` 全无；`#print axioms` 对 9 个新定理均只报
`[propext, Classical.choice, Quot.sound]`（`arrangement_pairwise`、`pos_lt_of_before_in_run`、
`flatten_eq_of_runs_by_pos`、`block_runs_order`、`vertsByPos_of_aligned`、`aligned_reverse`
连 `Classical.choice` 都不用）。另有两个具体实例探针：`#eval arrangement σ4 = [0,1,2,3]`、
`arrangement_pairwise σ4` 由 `native_decide` 验证、`block_runs_order` 与 `geoOrder_of_treeOrdered`
在 `Fin 4` 的具体例子上实例化成功（确认新定理非空转）。

**于是结论二的缺口只剩「树是怎么从图造出来的」**：`Part.WF`、`GeoWF`、`AllContig`、`TreeOrdered`
四条都描述了真实圆方树应当满足的性质，但「算法造出的树确实满足它们」没有形式化（这需要把
圆方树的构造、乃至度数为 2 的点消去过程本身写进 Lean）。这些已不含关于「排列/交叉/字典序」的
数学难点，属于算法流程的形式化。


## 6. 总结判定

| 结论 | 判定 | 说明 |
| --- | --- | --- |
| **结论一**（外边界是简单哈密顿环 + 唯一性） | ✅ 通过 | 命题忠实、证明独立可信、机器验证（`lake build` + 无 `sorryAx` + `Crosses` 语义探针） |
| **结论二**（圆方树递归构造字典序最优） | ⚠️ 模型内通过；图论前提、区间合并装配与**顺序条件**均已完成 | `seq_valid` / `seq_min` / `Valid.length_eq` 在 `Part`+`Valid`+`WF` 抽象模型内完全正确；支撑「合法排列 = 递归生成」的图论事实（`no_alternation_of_connectedIn`、`circle_contiguous_of_connected_complement`）、圆周/线性之桥（`linear_contig_of_circle`）区间合并装配（`merge_runs`、`valid_of_consists`、`consists_of_geometry`、`arrangement_valid`、`seq_le_arrangement`）与**顺序条件**（`block_runs_order`、`geoOrder_of_treeOrdered`）均已形式化（§5b、§5c、§5d）；`GeoOrder` 已由假设变为定理，唯一剩余的树侧假设 `TreeOrdered`（儿子按圆上顺序存储）是关于圆方树构造方式的性质 |

**一句话结论**：项目把 `editorial.md` 的两条**数学核心结论**都干净地形式化了（无 `sorry`、无额外公理、
构建通过），结论一可视为对题解的完整形式化；结论二形式化的是「递归层面的组合最优性」，
要把它升级为「题解算法输出字典序最小排列」的完整证明，还需补上：
① 真实圆方树满足 `Part.WF` / `GeoWF` / `AllContig` / `TreeOrdered`（四条均有精确定义，
差的是「算法造出的树确实满足它们」）、② 度数为 2 的点消去过程、③ 跨连通块合并贪心。
原先列为第一项的「方点外环顺序」已在 §5d 中证明完毕（`GeoOrder` 不再是假设）。

---

## 7. 附：审计中用到的外部探针文件（均未写入项目目录）

- `/tmp/audit_axioms.lean` —— 对已编译模块重跑 `#print axioms` 与 `#check`
- `/tmp/audit_sanity.lean` —— `Part.seq` 在抽象圆方树上的 `#eval`（结果见 §1.3）
- `/tmp/audit_cross.lean` —— `Crosses` 语义的具体机器证明（结果见 §1.4）
- `/tmp/audit_lex.lean`、`/tmp/audit_zmod.lean`、`/tmp/audit_chk.lean` —— 辅助语义确认

项目文件未作任何改动：`git status --short` 为空；`lake build` 仅更新 `.lake/`（已被 `.gitignore` 忽略）。
