/-
# `GrapermProof.Basic`

Framework for the olympiad problem *图排列* (P11832, 省选联考 2025).

We fix the vertex set to be `Fin n`.  A **circular order** on `Fin n` is recorded by the
*position* `pos v ∈ Fin n` of every vertex, i.e. by an equivalence `Fin n ≃ Fin n`.

Two edges with four pairwise distinct endpoints **cross** when exactly one endpoint of the
second edge lies on the open arc from the first endpoint of the first edge to the second.
This formalises "把排列中的点放在圆周上，边画成弦，两条边交叉当且仅当端点交错".
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option linter.style.haveILetI false

namespace Graperm

/-- A circular order on `Fin n`, given by the position `pos v` of each vertex. -/
structure CircOrder (n : ℕ) where
  /-- The number of vertices is positive. -/
  hn : 0 < n
  /-- The position of every vertex. -/
  pos : Fin n ≃ Fin n

namespace CircOrder

variable {n : ℕ}

/-- The forward cyclic distance from `x` to `p`, as a natural number in `[0, n)`. -/
noncomputable def fwd (σ : CircOrder n) (x p : Fin n) : ℕ :=
  (((σ.pos p).val : ZMod n) - ((σ.pos x).val : ZMod n)).val

/-- `p` lies strictly on the open arc running forward from `x` to `y`. -/
def Between (σ : CircOrder n) (p x y : Fin n) : Prop :=
  0 < σ.fwd x p ∧ σ.fwd x p < σ.fwd x y

/-- The edges `{a,b}` and `{c,d}` *cross*: the four endpoints are distinct and exactly one of
`c`, `d` lies strictly between `a` and `b` along the circle.  (Equivalently the endpoints
interleave.) -/
def Crosses (σ : CircOrder n) (a b c d : Fin n) : Prop :=
  a ≠ b ∧ c ≠ d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
    (σ.Between c a b ↔ ¬ σ.Between d a b)

/-- The `j`-th vertex met when walking forward from `v` (indices are taken modulo `n`). -/
noncomputable def iter (σ : CircOrder n) (v : Fin n) (j : ℕ) : Fin n :=
  σ.pos.symm ⟨((σ.pos v).val + j) % n, Nat.mod_lt _ σ.hn⟩

/-- The cyclic successor of `v`. -/
noncomputable def succ (σ : CircOrder n) (v : Fin n) : Fin n := σ.iter v 1

/-! ### Basic arithmetic of the forward distance -/

/-- Casting a natural number into `ZMod n` only depends on it modulo `n`. -/
lemma zmod_natCast_mod {n : ℕ} (a : ℕ) : ((a % n : ℕ) : ZMod n) = (a : ZMod n) := by
  nth_rewrite 2 [← Nat.mod_add_div a n]
  push_cast
  rw [ZMod.natCast_self, zero_mul, add_zero]

@[simp] lemma fwd_self (σ : CircOrder n) (x : Fin n) : σ.fwd x x = 0 := by
  simp [fwd]

lemma fwd_lt (σ : CircOrder n) (x p : Fin n) : σ.fwd x p < n := by
  haveI : NeZero n := ⟨σ.hn.ne'⟩
  exact ZMod.val_lt _

lemma fwd_eq_zero_iff (σ : CircOrder n) (x p : Fin n) : σ.fwd x p = 0 ↔ p = x := by
  unfold fwd
  rw [ZMod.val_eq_zero, sub_eq_zero]
  constructor
  · intro h
    have h2 := (ZMod.natCast_eq_natCast_iff' (σ.pos p).val (σ.pos x).val n).mp h
    rw [Nat.mod_eq_of_lt (σ.pos p).isLt, Nat.mod_eq_of_lt (σ.pos x).isLt] at h2
    exact σ.pos.injective (Fin.ext h2)
  · rintro rfl
    rfl

/-- The position of the `j`-th forward vertex. -/
lemma pos_iter (σ : CircOrder n) (v : Fin n) (j : ℕ) :
    σ.pos (σ.iter v j) = ⟨((σ.pos v).val + j) % n, Nat.mod_lt _ σ.hn⟩ :=
  Equiv.apply_symm_apply σ.pos _

lemma iter_zero (σ : CircOrder n) (v : Fin n) : σ.iter v 0 = v := by
  apply σ.pos.injective
  rw [pos_iter]
  exact Fin.ext (by simp [Nat.mod_eq_of_lt (σ.pos v).isLt])

/-- Walking `j` steps forward from `v` has forward distance `j` from `v` (for `j < n`). -/
lemma fwd_iter_zero (σ : CircOrder n) (v : Fin n) (j : ℕ) (hj : j < n) :
    σ.fwd v (σ.iter v j) = j := by
  unfold fwd
  rw [pos_iter]
  rw [zmod_natCast_mod]
  have hsub : (((σ.pos v).val + j : ℕ) : ZMod n) - (((σ.pos v).val : ℕ) : ZMod n)
      = ((j : ℕ) : ZMod n) := by
    rw [Nat.cast_add]
    ring
  rw [hsub, ZMod.val_natCast, Nat.mod_eq_of_lt hj]

/-- Every vertex is reached by walking forward from `v`, namely after `fwd v z` steps. -/
lemma iter_fwd (σ : CircOrder n) (v z : Fin n) : σ.iter v (σ.fwd v z) = z := by
  haveI : NeZero n := ⟨σ.hn.ne'⟩
  have hp := σ.pos_iter v (σ.fwd v z)
  have hcast : (((σ.fwd v z : ℕ)) : ZMod n)
      = ((σ.pos z).val : ZMod n) - ((σ.pos v).val : ZMod n) := by
    unfold fwd
    rw [ZMod.natCast_zmod_val]
  have h1 : ((((σ.pos v).val + σ.fwd v z : ℕ)) : ZMod n) = ((σ.pos z).val : ZMod n) := by
    rw [Nat.cast_add, hcast]
    ring
  have h2 := congrArg ZMod.val h1
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (σ.pos z).isLt] at h2
  apply σ.pos.injective
  rw [hp]
  exact Fin.ext h2

/-- `iter v` is injective on indices below `n`. -/
lemma iter_inj (σ : CircOrder n) (v : Fin n) {j k : ℕ} (hj : j < n) (hk : k < n)
    (h : σ.iter v j = σ.iter v k) : j = k := by
  have h1 := σ.fwd_iter_zero v j hj
  have h2 := σ.fwd_iter_zero v k hk
  rw [h] at h1
  rw [h2] at h1
  exact h1.symm

/-- `succ` moves forward by one step. -/
lemma fwd_succ (σ : CircOrder n) (v : Fin n) (hn1 : 1 < n) : σ.fwd v (σ.succ v) = 1 :=
  σ.fwd_iter_zero v 1 hn1

/-- Iterating forward is additive. -/
lemma iter_iter (σ : CircOrder n) (v : Fin n) (k j : ℕ) :
    σ.iter (σ.iter v k) j = σ.iter v (k + j) := by
  apply σ.pos.injective
  rw [pos_iter, pos_iter, pos_iter]
  exact Fin.ext (by
    have h : (((σ.pos v).val + k) % n + j) ≡ ((σ.pos v).val + (k + j)) [MOD n] := by
      have h1 : (((σ.pos v).val + k) % n + j) ≡ ((σ.pos v).val + k) + j [MOD n] :=
        (Nat.mod_modEq ((σ.pos v).val + k) n).add_right j
      rwa [Nat.add_assoc] at h1
    exact h)

/-- Going all the way round the circle returns to the starting point. -/
lemma iter_n (σ : CircOrder n) (v : Fin n) : σ.iter v n = v := by
  apply σ.pos.injective
  rw [pos_iter]
  exact Fin.ext (by
    simp [Nat.mod_eq_of_lt (σ.pos v).isLt])

/-- The cyclic predecessor of `v`. -/
noncomputable def pred (σ : CircOrder n) (v : Fin n) : Fin n := σ.iter v (n - 1)

lemma pred_eq_iter (σ : CircOrder n) (v : Fin n) : σ.pred v = σ.iter v (n - 1) := rfl

/-- The successor of the predecessor is the vertex itself. -/
lemma succ_pred (σ : CircOrder n) (v : Fin n) : σ.succ (σ.pred v) = v := by
  have hn : 0 < n := σ.hn
  rw [succ, pred_eq_iter, iter_iter]
  have : n - 1 + 1 = n := by omega
  rw [this, iter_n]

/-- The predecessor of the successor is the vertex itself. -/
lemma pred_succ (σ : CircOrder n) (v : Fin n) : σ.pred (σ.succ v) = v := by
  have hn : 0 < n := σ.hn
  rw [pred_eq_iter, succ, iter_iter]
  have : 1 + (n - 1) = n := by omega
  rw [this, iter_n]

/-- The forward distance to the predecessor is `n - 1`. -/
lemma fwd_pred (σ : CircOrder n) (v : Fin n) : σ.fwd v (σ.pred v) = n - 1 := by
  have hn : 0 < n := σ.hn
  rw [pred_eq_iter]
  exact σ.fwd_iter_zero v (n - 1) (by omega)

/-- The successor and predecessor of a vertex differ (needs at least three vertices). -/
lemma succ_ne_pred (σ : CircOrder n) (v : Fin n) (h3 : 3 ≤ n) : σ.succ v ≠ σ.pred v := by
  intro h
  have h1 : σ.fwd v (σ.succ v) = 1 := σ.fwd_succ v (by omega)
  have h2 : σ.fwd v (σ.pred v) = n - 1 := σ.fwd_pred v
  rw [h] at h1
  omega

end CircOrder

/-- The circular order `σ` is **realizable** for `G`: no two vertex-disjoint edges cross. -/
def IsRealizable {n : ℕ} (σ : CircOrder n) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ a b c d : Fin n, G.Adj a b → G.Adj c d → ¬ σ.Crosses a b c d

/-- `G` is **2-vertex-connected**: it is connected, and deleting any single vertex leaves a
connected graph.  (Phrased via walks so that no extra API is needed.) -/
def IsTwoConn {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  (∀ u v : Fin n, Nonempty (G.Walk u v)) ∧
    (∀ w u v : Fin n, u ≠ w → v ≠ w → ∃ p : G.Walk u v, w ∉ p.support)

end Graperm
