/-
# `GrapermProof.GeoOrder`

Discharging the last hypothesis of `Consists`: the **order condition** at a block node.

Up to here, `GeoOrder σ p` had to be *assumed*.  It says that at every block node the runs of
the answer permutation belonging to the children occur in the order in which the children are
stored in the block-cut tree, either forwards or entirely reversed.  This is now proved.

The proof splits into two independent pieces:

* **Combinatorics** (`BlockOrder.block_runs_order`).  Once the runs are known to be pairwise
  disjoint, nonempty, and to cover `L`, and once they are listed in increasing order of their
  circular position, then `L` *is* their concatenation — and if they are listed the other way
  round, `L` is the concatenation of the reversal.  Nothing here uses graphs or planarity; the
  only geometric input is that `arrangement σ` lists the vertices in increasing order of
  position.

* **Tree bookkeeping** (`TreeOrdered`).  What remains is the statement that the children of a
  block node are *stored* in the order in which they occur along the block's outer cycle — a
  property of the way the block-cut tree is built from the graph, not of the geometry of the
  drawing.  It is isolated as the hypothesis `TreeOrdered σ p`, and `GeoOrder σ p` is derived
  from it by a recursion over the tree.

So the only surviving hypothesis about the block-cut tree is `TreeOrdered`, which says exactly
"the children of a block are stored in cyclic order (or the reverse)".  Everything else —
including the whole order analysis — is now a theorem.
-/
import GrapermProof.BlockOrder
import GrapermProof.Consists

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Graperm

variable {n : ℕ}

/-! ### The order in which the tree stores its children -/

/-- **The children of a block node are stored in the order in which they occur along the
block's outer cycle.**  Concretely: the vertex sets of the children of a block node are listed
in increasing order of their position on the circle, or in the exact reverse of that order.
For a round node there is no condition on the order (its own vertex may be interleaved with
the children arbitrarily), so the property just descends to the children.

This is a property of the *construction* of the block-cut tree from the graph — the algorithm
visits the outer cycle of a biconnected component and attaches the hanging subtrees in that
order.  It is the single remaining hypothesis in the completeness direction of Claim 2. -/
def TreeOrdered (σ : CircOrder n) : Part (Fin n) → Prop
  | .round v cs => ∀ c ∈ cs, TreeOrdered σ c
  | .block cs =>
      (∀ c ∈ cs, TreeOrdered σ c) ∧
        (VertsByPos σ (cs.map partVerts) ∨ VertsByPos σ (cs.map partVerts).reverse)

/-! ### Transferring the positional order from the tree to the runs -/

/-- **Alignment transfers the positional order.**  If the runs `ms` are aligned with the parts
`cs` (the `i`-th run lists exactly the vertices of the `i`-th part) and the vertex sets of
`cs` are in increasing order of position, then so are the runs `ms`. -/
theorem vertsByPos_of_aligned (σ : CircOrder n) :
    ∀ {cs : List (Part (Fin n))} {ms : List (List (Fin n))},
      Aligned cs ms → VertsByPos σ (cs.map partVerts) → VertsByPos σ ms := by
  intro cs
  induction cs with
  | nil =>
      intro ms ha h
      cases ms with
      | nil => simp [VertsByPos]
      | cons m ms' => simp [Aligned] at ha
  | cons c cs' ih =>
      intro ms ha h
      cases ms with
      | nil => simp [Aligned] at ha
      | cons m ms' =>
          simp only [Aligned] at ha
          simp only [List.map_cons] at h
          have hhead : ∀ A' ∈ cs'.map partVerts, posSep σ (partVerts c) A' :=
            (List.pairwise_cons.mp h).1
          have htail : (cs'.map partVerts).Pairwise (posSep σ) := (List.pairwise_cons.mp h).2
          simp only [VertsByPos]
          rw [List.pairwise_cons]
          constructor
          · intro m' hm'
            obtain ⟨c', hc', hv⟩ := aligned_imp_right ha.2 m' hm'
            have hsep : posSep σ (partVerts c) (partVerts c') :=
              hhead (partVerts c') (List.mem_map.mpr ⟨c', hc', rfl⟩)
            intro x hx y hy
            exact hsep x ((ha.1 x).mp hx) y ((hv y).mp hy)
          · exact ih ha.2 htail

/-- The same, for the reversed order. -/
theorem vertsByPos_reverse_of_aligned (σ : CircOrder n)
    {cs : List (Part (Fin n))} {ms : List (List (Fin n))}
    (ha : Aligned cs ms) (h : VertsByPos σ (cs.map partVerts).reverse) :
    VertsByPos σ ms.reverse := by
  exact vertsByPos_of_aligned σ (aligned_reverse ha) (by simpa [List.map_reverse] using h)

/-! ### The order condition is a theorem -/

/-- **`GeoOrder` follows from `TreeOrdered`.**  At a round node there is nothing to prove
beyond descending into the children.  At a block node, `ChildData` supplies a run of `L` for
each child, aligned with the child, pairwise disjoint, nonempty and covering `L`;
`TreeOrdered` says these runs are listed in increasing order of position (or the reverse), and
`block_runs_order` then forces `L` to be their concatenation (or the concatenation of their
reversal). -/
theorem geoOrder_of_treeOrdered (σ : CircOrder n) (p : Part (Fin n)) :
    TreeOrdered σ p → GeoOrder σ p := by
  classical
  exact Part.rec
    (motive_1 := fun p => TreeOrdered σ p → GeoOrder σ p)
    (motive_2 := fun cs => (∀ c ∈ cs, TreeOrdered σ c) → (∀ c ∈ cs, GeoOrder σ c))
    (fun v cs ih => by
      intro hto
      simp only [TreeOrdered] at hto
      simp only [GeoOrder]
      exact ih hto)
    (fun cs ih => by
      intro hto
      simp only [TreeOrdered] at hto
      simp only [GeoOrder]
      constructor
      · exact ih hto.1
      · intro L hLrun hverts ms hcd
        obtain ⟨hms, hrun, hnod, hdisjM, hmsnod, hal₁, hal₂, hne, halign⟩ := hcd
        have hLnod : L.Nodup := nodup_of_isRun (arrangement_nodup σ) hLrun
        have hcov : ∀ x ∈ L, ∃ m ∈ ms, x ∈ m := by
          intro x hx
          have hxv : x ∈ partVerts (.block cs : Part (Fin n)) := (hverts x).mp hx
          simp [partVerts] at hxv
          obtain ⟨c, hc', hxc⟩ := exists_part_of_mem_partVertsList (cs := cs) hxv
          obtain ⟨m, hm, hmv⟩ := hal₁ c hc'
          exact ⟨m, hm, (hmv x).mpr hxc⟩
        have horder : VertsByPos σ ms ∨ VertsByPos σ ms.reverse := by
          rcases hto.2 with h | h
          · exact Or.inl (vertsByPos_of_aligned σ halign h)
          · exact Or.inr (vertsByPos_reverse_of_aligned σ halign h)
        exact block_runs_order σ hLrun hLnod hrun hne hdisjM hmsnod hcov horder)
    (by
      intro hto c hc
      simp at hc)
    (by
      intro head tail ihh iht hto d hd
      rcases List.mem_cons.mp hd with rfl | hd'
      · exact ihh (hto d (by simp))
      · exact iht (fun e he => hto e (by simp [he])) d hd')
    p

/-! ### The completeness direction of Claim 2, free of the order hypothesis -/

/-- **The answer permutation is admissible.**  A tree which is structurally sound (`GeoWF`),
all of whose subtrees are contiguous on the circle (`AllContig`) and which stores the children
of every block in cyclic order (`TreeOrdered`) makes the permutation `arrangement σ` one of
the arrangements the block-cut recursion may produce.  Unlike `arrangement_valid`, no order
hypothesis is left over: `GeoOrder` is derived, not assumed. -/
theorem arrangement_valid_of_tree (σ : CircOrder n) [NeZero n] (p : Part (Fin n))
    (hwf : GeoWF p) (hc : AllContig σ p) (hto : TreeOrdered σ p)
    (hverts : ∀ x, x ∈ arrangement σ ↔ x ∈ partVerts p) :
    Part.Valid p (arrangement σ) :=
  arrangement_valid σ p hwf hc (geoOrder_of_treeOrdered σ p hto) hverts

/-- **Claim 2, completeness direction.**  Under the same hypotheses, and assuming the tree is
also well formed in the sense of `Part.WF`, the greedy recursive construction is
lexicographically at most the permutation induced by *any* non-crossing circular order.

The only remaining hypotheses concern how the block-cut tree is obtained from the graph
(`Part.WF`, `GeoWF`, `AllContig`, `TreeOrdered`); the order analysis itself — the fact that
the children of a block must be visited forwards or backwards — is now proved. -/
theorem seq_le_arrangement_of_tree (σ : CircOrder n) [NeZero n] (p : Part (Fin n))
    (hwfP : Part.WF p) (hwf : GeoWF p) (hc : AllContig σ p) (hto : TreeOrdered σ p)
    (hverts : ∀ x, x ∈ arrangement σ ↔ x ∈ partVerts p) :
    Part.seq p ≤ arrangement σ :=
  Part.seq_min hwfP (arrangement_valid_of_tree σ p hwf hc hto hverts)

end Graperm
