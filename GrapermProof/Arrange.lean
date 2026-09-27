/-
# `GrapermProof.Arrange`

Bridge between the *circular* world of `Separation` (where the non-crossing condition lives)
and the *linear* world of the answer (a permutation, compared lexicographically).

* `arrangement σ` is the answer permutation induced by a circular order `σ`, defined as the
  segment of positions `0, 1, …, n-1`;
* `LinearContig σ A` says that `A` occupies one interval of that permutation;
* `linear_contig_of_circle` proves that a set which is contiguous **on the circle** is also
  contiguous **in the line**, provided the root (the vertex at position `0`) is outside `A`.
  This is the step that makes the block-cut recursion complete: an arc of the circle that
  wraps around the end of the permutation would break the recursion, and the root sitting at
  position `0` is exactly what rules the wrap-around out.
-/
import GrapermProof.Separation

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Graperm

namespace CircOrder

variable {n : ℕ}

/-- When `b` is not before `a`, the forward distance is just the difference of positions. -/
theorem fwd_eq_sub_of_le (σ : CircOrder n) {a b : Fin n}
    (h : (σ.pos a).val ≤ (σ.pos b).val) :
    σ.fwd a b = (σ.pos b).val - (σ.pos a).val := by
  haveI : NeZero n := ⟨σ.hn.ne'⟩
  unfold fwd
  have hsub : ((σ.pos b).val : ZMod n) - ((σ.pos a).val : ZMod n) =
      (((σ.pos b).val - (σ.pos a).val : ℕ) : ZMod n) := by
    have hs : (σ.pos b).val = (σ.pos a).val + ((σ.pos b).val - (σ.pos a).val) := by omega
    nth_rewrite 1 [hs]
    rw [Nat.cast_add]
    ring
  rw [hsub, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (by
    have hb := (σ.pos b).isLt
    omega)

end CircOrder

open CircOrder

variable {n : ℕ}

/-- The segment of the arrangement consisting of the positions `lo, …, lo + len - 1`
(positions are reduced modulo `n`, which is harmless as long as `lo + len ≤ n`). -/
def seg (σ : CircOrder n) (lo len : ℕ) : List (Fin n) :=
  (List.range' lo len).map (fun i => σ.pos.symm ⟨i % n, Nat.mod_lt _ σ.hn⟩)

/-- Consecutive segments concatenate. -/
theorem seg_append (σ : CircOrder n) (lo a b : ℕ) :
    seg σ lo (a + b) = seg σ lo a ++ seg σ (lo + a) b := by
  unfold seg
  rw [← List.range'_append (s := lo) (m := a) (n := b) (step := 1), List.map_append]
  simp

/-- The answer permutation induced by `σ`: the vertices, ordered by their position. -/
def arrangement (σ : CircOrder n) : List (Fin n) := seg σ 0 n

/-- Every vertex occurs in the full arrangement. -/
theorem mem_arrangement (σ : CircOrder n) (v : Fin n) : v ∈ arrangement σ := by
  unfold arrangement seg
  rw [List.mem_map]
  refine ⟨(σ.pos v).val, ?_, ?_⟩
  · rw [List.range'_eq_map_range, List.mem_map]
    refine ⟨(σ.pos v).val, List.mem_range.mpr (σ.pos v).isLt, by simp⟩
  · apply σ.pos.injective
    rw [Equiv.apply_symm_apply]
    exact Fin.ext (by simp [Nat.mod_eq_of_lt (σ.pos v).isLt])

/-- The arrangement has the right length. -/
theorem length_arrangement (σ : CircOrder n) : (arrangement σ).length = n := by
  simp [arrangement, seg]

/-- `A` occupies one interval of the linear arrangement: whenever two vertices of `A` sit at
positions `p ≤ q`, everything between them belongs to `A`. -/
def LinearContig (σ : CircOrder n) (A : Set (Fin n)) : Prop :=
  ∀ {a₁ a₂ x : Fin n}, a₁ ∈ A → a₂ ∈ A →
    (σ.pos a₁).val ≤ (σ.pos x).val → (σ.pos x).val ≤ (σ.pos a₂).val → x ∈ A

/-- **From the circle to the line.**  A set that is contiguous on the circle is contiguous in
the permutation as well, as soon as the vertex sitting at position `0` (the root) is outside
it.  Without that hypothesis the arc could wrap around the end of the permutation. -/
theorem linear_contig_of_circle (σ : CircOrder n) {A : Set (Fin n)}
    (hc : CircleContiguous σ A) {r : Fin n} (hr : σ.pos r = ⟨0, σ.hn⟩) (hrA : r ∉ A) :
    LinearContig σ A := by
  intro a₁ a₂ x ha₁ ha₂ hle₁ hle₂
  by_contra hxA
  have hposr : (σ.pos r).val = 0 := by
    rw [hr]
  have hx_ne_a₁ : x ≠ a₁ := by
    intro h
    exact hxA (by simpa [h] using ha₁)
  have hx_ne_a₂ : x ≠ a₂ := by
    intro h
    exact hxA (by simpa [h] using ha₂)
  have ha₁_pos : 0 < (σ.pos a₁).val := by
    have hne : a₁ ≠ r := by
      intro h
      exact hrA (by simpa [h] using ha₁)
    have hz : (σ.pos a₁).val ≠ (σ.pos r).val := by
      intro h
      exact hne (σ.pos.injective (Fin.ext h))
    have hb := (σ.pos a₁).isLt
    omega
  have hfwd_a₁x : σ.fwd a₁ x = (σ.pos x).val - (σ.pos a₁).val :=
    σ.fwd_eq_sub_of_le hle₁
  have hfwd_a₁a₂ : σ.fwd a₁ a₂ = (σ.pos a₂).val - (σ.pos a₁).val :=
    σ.fwd_eq_sub_of_le (le_trans hle₁ hle₂)
  have hpos_ne₁ : (σ.pos x).val ≠ (σ.pos a₁).val := by
    intro h
    exact hx_ne_a₁ (σ.pos.injective (Fin.ext h))
  have hpos_ne₂ : (σ.pos x).val ≠ (σ.pos a₂).val := by
    intro h
    exact hx_ne_a₂ (σ.pos.injective (Fin.ext h))
  have hBx : σ.Between x a₁ a₂ := by
    simp [CircOrder.Between, hfwd_a₁x, hfwd_a₁a₂]
    constructor <;> omega
  have hfwd_ra₁ : σ.fwd r a₁ = (σ.pos a₁).val := by
    have h := σ.fwd_eq_sub_of_le (a := r) (b := a₁) (by rw [hposr]; exact Nat.zero_le _)
    rw [hposr] at h
    simpa using h
  have hfwd_a₁r : σ.fwd a₁ r = n - (σ.pos a₁).val := by
    have hne : a₁ ≠ r := by
      intro h
      exact hrA (by simpa [h] using ha₁)
    have := σ.fwd_rev_eq hne
    omega
  have hnBr : ¬ σ.Between r a₁ a₂ := by
    simp [CircOrder.Between, hfwd_a₁r, hfwd_a₁a₂]
  have halt : σ.Alternates a₁ a₂ x r := by
    unfold CircOrder.Alternates
    simp [hBx, hnBr]
  exact (hc ha₁ ha₂ hxA hrA) halt

end Graperm
