/-
# `GrapermProof.Separation`

The graph-theoretic core that Claim 2 of the editorial rests on but that the abstract
model of `GrapermProof.BlockTree` takes for granted.

Everything here lives at the level of a graph `G` on `Fin n` together with a
non-crossing circular order `σ` (`IsRealizable`).  The two results are

* `walk_alternates_edge` — a walk whose two endpoints lie on *different* sides of a chord
  `{s,t}` must use an edge that crosses `{s,t}` (a discrete intermediate value theorem:
  walking along the walk, the side can only change by crossing);

* `no_alternation_of_connected` — two vertex-disjoint subgraphs that are each internally
  connected can never have their vertices alternate `A, B, A, B` around the circle.
  This is the editorial's "基础事实", proved by applying the previous lemma twice:
  first to a path inside `B` (which produces an edge `{u,v}` of `B` lying across the
  chord `{a₁,a₂}`), then to a path inside `A` (which produces an edge of `A` crossing
  `{u,v}`), contradicting non-crossing.

The consequence actually used by the block-cut tree recursion is
`circle_contiguous_of_connected_complement`: if `A` and its complement are both
internally connected, then `A` occupies one arc of the circle (no two vertices of `A`
are separated by vertices outside `A`).
-/
import GrapermProof.OuterCycle

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Graperm

/-! ### Small `ZMod` helper -/

/-- The value of a sum in `ZMod n` is the sum of the values, reduced modulo `n`. -/
lemma zmod_val_add {n : ℕ} [NeZero n] (u v : ZMod n) : (u + v).val = (u.val + v.val) % n := by
  conv_lhs => rw [← ZMod.natCast_zmod_val u, ← ZMod.natCast_zmod_val v]
  rw [← Nat.cast_add, ZMod.val_natCast]

namespace CircOrder

variable {n : ℕ}

/-- **Triangle rule (modulo `n`).**  Forward distances add up around the circle. -/
theorem fwd_add_mod (σ : CircOrder n) (x y z : Fin n) :
    σ.fwd x z = (σ.fwd x y + σ.fwd y z) % n := by
  haveI : NeZero n := ⟨σ.hn.ne'⟩
  unfold fwd
  have h : (((σ.pos z).val : ZMod n) - ((σ.pos x).val : ZMod n)) =
      (((σ.pos y).val : ZMod n) - ((σ.pos x).val : ZMod n)) +
        (((σ.pos z).val : ZMod n) - ((σ.pos y).val : ZMod n)) := by
    ring
  rw [h]
  exact zmod_val_add _ _

/-- A non-trivial forward distance is positive. -/
theorem fwd_pos_of_ne (σ : CircOrder n) {x y : Fin n} (h : x ≠ y) : 0 < σ.fwd x y := by
  have h0 : σ.fwd x y ≠ 0 := fun hz => h ((σ.fwd_eq_zero_iff x y).mp hz).symm
  omega

/-- Going there and back is exactly one full turn. -/
theorem fwd_add_rev (σ : CircOrder n) {x y : Fin n} (h : x ≠ y) : σ.fwd x y + σ.fwd y x = n := by
  haveI : NeZero n := ⟨σ.hn.ne'⟩
  have hm : (σ.fwd x y + σ.fwd y x) % n = 0 := by
    rw [← σ.fwd_add_mod x y x, σ.fwd_self]
  have hpos : 0 < σ.fwd x y + σ.fwd y x := by
    have := σ.fwd_pos_of_ne h
    omega
  have h1 : σ.fwd x y ≤ n - 1 := by
    have := σ.fwd_lt x y
    omega
  have h2 : σ.fwd y x ≤ n - 1 := by
    have := σ.fwd_lt y x
    omega
  have hlt : σ.fwd x y + σ.fwd y x ≤ 2 * n - 2 := by omega
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hm
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hkz : k = 0 := Nat.lt_one_iff.mp (Nat.lt_of_not_ge hk0)
    subst k
    simp at hk
    omega
  have hknot2 : ¬ 2 ≤ k := by
    intro hk2
    have hm2 : 2 * n ≤ n * k := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left n hk2
    have hbad : 2 * n ≤ 2 * n - 2 := by
      calc 2 * n ≤ n * k := hm2
        _ = σ.fwd x y + σ.fwd y x := hk.symm
        _ ≤ 2 * n - 2 := hlt
    exact (not_le_of_gt (Nat.sub_lt (Nat.mul_pos (by norm_num) σ.hn) (by norm_num))) hbad
  have hk_le1 : k ≤ 1 :=
    Nat.le_of_not_gt (by intro hkgt; exact hknot2 (Nat.succ_le_of_lt hkgt))
  have hk_eq : k = 1 := le_antisymm hk_le1 hk1
  subst k
  simpa using hk

/-- The backward distance is the complement of the forward one. -/
theorem fwd_rev_eq (σ : CircOrder n) {x y : Fin n} (h : x ≠ y) : σ.fwd y x = n - σ.fwd x y := by
  have hs := σ.fwd_add_rev h
  have hlt : σ.fwd x y ≤ n := by
    have := σ.fwd_lt x y
    omega
  omega

/-- For a fixed start point the forward distance determines the endpoint. -/
theorem fwd_injective_right (σ : CircOrder n) {x y z : Fin n} (h : σ.fwd x y = σ.fwd x z) : y = z := by
  haveI : NeZero n := ⟨σ.hn.ne'⟩
  unfold fwd at h
  have hz : (((σ.pos y).val : ZMod n) - ((σ.pos x).val : ZMod n)) =
      (((σ.pos z).val : ZMod n) - ((σ.pos x).val : ZMod n)) := by
    apply ZMod.val_injective
    exact h
  have hz'' : ((σ.pos y).val : ZMod n) + (-((σ.pos x).val : ZMod n)) =
      ((σ.pos z).val : ZMod n) + (-((σ.pos x).val : ZMod n)) := by
    simpa [sub_eq_add_neg] using hz
  have hz' : ((σ.pos y).val : ZMod n) = ((σ.pos z).val : ZMod n) :=
    add_right_cancel hz''
  have hv := (ZMod.natCast_eq_natCast_iff' (σ.pos y).val (σ.pos z).val n).mp hz'
  rw [Nat.mod_eq_of_lt (σ.pos y).isLt, Nat.mod_eq_of_lt (σ.pos z).isLt] at hv
  exact σ.pos.injective (Fin.ext hv)

/-- Every vertex other than the two endpoints lies on exactly one of the two open arcs. -/
theorem between_iff_not_between (σ : CircOrder n) {s t x : Fin n}
    (hxs : x ≠ s) (hxt : x ≠ t) (hst : s ≠ t) :
    σ.Between x s t ↔ ¬ σ.Between x t s := by
  haveI : NeZero n := ⟨σ.hn.ne'⟩
  have hn0 : 0 < n := σ.hn
  unfold Between
  set A := σ.fwd s t with hA
  set B := σ.fwd s x with hB
  have hApos : 0 < A := by
    rw [hA]; exact σ.fwd_pos_of_ne hst
  have hAlt : A < n := by rw [hA]; exact σ.fwd_lt s t
  have hBpos : 0 < B := by
    rw [hB]; exact σ.fwd_pos_of_ne hxs.symm
  have hBlt : B < n := by rw [hB]; exact σ.fwd_lt s x
  have hBne : B ≠ A := by
    intro hBA
    have : x = t := σ.fwd_injective_right (by show σ.fwd s x = σ.fwd s t; rw [← hB, ← hA]; exact hBA)
    exact hxt this
  have hft : σ.fwd t s = n - A := by
    rw [hA]; exact σ.fwd_rev_eq hst
  -- the two sides of the case split
  have htx : σ.fwd t x = if A < B then B - A else n + B - A := by
    have hm := σ.fwd_add_mod t s x
    rw [hft] at hm
    have hm' : σ.fwd t x = (n - A + B) % n := by
      simpa [← hB] using hm
    rw [hm']
    by_cases hAB : A < B
    · have hmod : (n - A + B) % n = B - A := by
        have hsum : n - A + B = (B - A) + 1 * n := by omega
        rw [hsum, Nat.add_mul_mod_self_right]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hmod]
      simp [hAB]
    · have hlt2 : n - A + B < n := by omega
      have hmod : (n - A + B) % n = n - A + B := Nat.mod_eq_of_lt hlt2
      rw [hmod]
      simp [hAB]
      omega
  rw [htx, hft]
  by_cases hAB : A < B
  · -- `x` lies on the arc `t → s`
    simp [hAB]
    constructor <;> intro h <;> omega
  · -- `x` lies on the arc `s → t`, using `B ≠ A`
    have hBA : B < A := by omega
    simp [hAB]
    constructor <;> intro h <;> omega

/-- Forward distance between two points that both lie after `b` on the arc from `a`. -/
theorem fwd_of_lt (σ : CircOrder n) {a b c : Fin n} (hab : a ≠ b) (h : σ.fwd a b < σ.fwd a c) :
    σ.fwd b c = σ.fwd a c - σ.fwd a b := by
  have hba : σ.fwd b a = n - σ.fwd a b := σ.fwd_rev_eq hab
  have hm := σ.fwd_add_mod b a c
  rw [hba] at hm
  rw [hm]
  have hBn : σ.fwd a b ≤ n := by
    have := σ.fwd_lt a b
    omega
  have hsum : n - σ.fwd a b + σ.fwd a c = (σ.fwd a c - σ.fwd a b) + 1 * n := by
    rw [one_mul]
    omega
  rw [hsum, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt (by
    have := σ.fwd_lt a c
    omega)

/-- Forward distance when `c` lies before `b` on the arc from `a`. -/
theorem fwd_of_gt (σ : CircOrder n) {a b c : Fin n} (hab : a ≠ b) (h : σ.fwd a c < σ.fwd a b) :
    σ.fwd b c = n + σ.fwd a c - σ.fwd a b := by
  have hba : σ.fwd b a = n - σ.fwd a b := σ.fwd_rev_eq hab
  have hm := σ.fwd_add_mod b a c
  rw [hba] at hm
  rw [hm]
  have hlt : n - σ.fwd a b + σ.fwd a c < n := by
    have := σ.fwd_lt a c
    omega
  rw [Nat.mod_eq_of_lt hlt]
  have hBn : σ.fwd a b ≤ n := by
    have := σ.fwd_lt a b
    omega
  omega

/-- `x` and `y` lie on **different** sides of the chord `{s,t}`: exactly one of them is on
the open arc running from `s` to `t`.  For four distinct points this is precisely the
crossing condition; unlike `Crosses` it does not require `{s,t}` or `{x,y}` to be edges. -/
def Alternates (σ : CircOrder n) (s t x y : Fin n) : Prop :=
  σ.Between x s t ↔ ¬ σ.Between y s t

-- `Alternates` is impossible when the two reference points coincide
theorem alternates_irrefl (σ : CircOrder n) (s t x : Fin n) : ¬ σ.Alternates s t x x := by
  unfold Alternates
  tauto

theorem alternates_irrefl_left (σ : CircOrder n) (s x y : Fin n) : ¬ σ.Alternates s s x y := by
  simp [Alternates, Between]

/-- `Alternates` does not depend on the order inside a pair. -/
theorem alternates_comm (σ : CircOrder n) {s t x y : Fin n} :
    σ.Alternates s t x y ↔ σ.Alternates s t y x := by
  unfold Alternates
  tauto

/-- Interleaving is symmetric in the two chords: if `x,y` straddle `{s,t}` then `s,t`
straddle `{x,y}`.  This is the combinatorial heart of the "no `A,B,A,B`" argument. -/
theorem alternates_swap (σ : CircOrder n) {s t x y : Fin n}
    (hsx : x ≠ s) (hxt : x ≠ t) (hsy : y ≠ s) (hyt : y ≠ t)
    (hst : s ≠ t) (hxy : x ≠ y)
    (h : σ.Alternates s t x y) : σ.Alternates x y s t := by
  unfold Alternates at h ⊢
  by_cases hbx : σ.Between x s t
  · -- cyclic order `s, x, t, y`
    have hny : ¬ σ.Between y s t := fun hy => (h.mp hbx) hy
    have hXpos : 0 < σ.fwd s x := by simpa [Between] using hbx.1
    have hXA : σ.fwd s x < σ.fwd s t := by simpa [Between] using hbx.2
    have hYpos : 0 < σ.fwd s y := σ.fwd_pos_of_ne hsy.symm
    have hYne : σ.fwd s y ≠ σ.fwd s t := by
      intro he
      exact hyt (σ.fwd_injective_right he)
    have hAY : σ.fwd s t < σ.fwd s y := by
      by_contra hle
      apply hny
      simp [Between]
      constructor
      · exact hYpos
      · omega
    have hxs : σ.fwd x s = n - σ.fwd s x := σ.fwd_rev_eq hsx.symm
    have hxt' : σ.fwd x t = σ.fwd s t - σ.fwd s x := σ.fwd_of_lt hsx.symm hXA
    have hxy' : σ.fwd x y = σ.fwd s y - σ.fwd s x :=
      σ.fwd_of_lt hsx.symm (by omega)
    have hnB1 : ¬ σ.Between s x y := by
      simp [Between, hxs, hxy']
      intro _
      have := σ.fwd_lt s y
      omega
    have hB2 : σ.Between t x y := by
      simp [Between, hxt', hxy']
      constructor <;> omega
    simp [hnB1, hB2]
  · -- cyclic order `s, y, t, x`
    have hby : σ.Between y s t := by
      by_contra hy
      exact hbx (h.mpr hy)
    have hYpos : 0 < σ.fwd s y := by simpa [Between] using hby.1
    have hYA : σ.fwd s y < σ.fwd s t := by simpa [Between] using hby.2
    have hXpos : 0 < σ.fwd s x := σ.fwd_pos_of_ne hsx.symm
    have hXne : σ.fwd s x ≠ σ.fwd s t := by
      intro he
      exact hxt (σ.fwd_injective_right he)
    have hAX : σ.fwd s t < σ.fwd s x := by
      by_contra hle
      apply hbx
      simp [Between]
      constructor
      · exact hXpos
      · omega
    have hxs : σ.fwd x s = n - σ.fwd s x := σ.fwd_rev_eq hsx.symm
    have hxt' : σ.fwd x t = n + σ.fwd s t - σ.fwd s x := σ.fwd_of_gt hsx.symm hAX
    have hxy' : σ.fwd x y = n + σ.fwd s y - σ.fwd s x := σ.fwd_of_gt hsx.symm (by omega)
    have hB1 : σ.Between s x y := by
      simp [Between, hxs, hxy']
      have := σ.fwd_lt s x
      constructor <;> omega
    have hnB2 : ¬ σ.Between t x y := by
      simp [Between, hxt', hxy']
      intro hc
      omega
    simp [hB1, hnB2]

end CircOrder

open CircOrder

/-! ### Walks cannot jump across a chord -/

/-- **Discrete intermediate value theorem.**  If the two endpoints of a walk lie on different
sides of the chord `{s,t}`, and the walk avoids `s` and `t`, then some edge of the walk
straddles `{s,t}` as well.  (No non-crossing assumption is needed here.) -/
theorem walk_alternates_edge {n : ℕ} {G : SimpleGraph (Fin n)} (σ : CircOrder n) {s t : Fin n} :
    ∀ {x y : Fin n} (P : G.Walk x y), s ∉ P.support → t ∉ P.support →
      σ.Alternates s t x y →
      ∃ u v : Fin n, G.Adj u v ∧ u ∈ P.support ∧ v ∈ P.support ∧ σ.Alternates s t u v := by
  intro x y P
  induction P with
  | nil =>
      intro _ _ halt
      exfalso
      exact (σ.alternates_irrefl s t _) halt
  | cons hadj P' ih =>
      intro hs ht halt
      rename_i x₀ z y₀
      rw [SimpleGraph.Walk.support_cons] at hs ht
      simp at hs ht
      by_cases hz : σ.Alternates s t x₀ z
      · refine ⟨x₀, z, hadj, ?_, ?_, hz⟩
        · simp [SimpleGraph.Walk.support_cons]
        · simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.start_mem_support]
      · have hzy : σ.Alternates s t z y₀ := by
          unfold CircOrder.Alternates at hz halt ⊢
          by_cases bx : σ.Between x₀ s t <;>
            by_cases bz : σ.Between z s t <;>
            by_cases by₀ : σ.Between y₀ s t <;>
            simp [bx, bz, by₀] at hz halt ⊢
        obtain ⟨u, v, huv, hu, hv, halt_uv⟩ := ih hs.2 ht.2 hzy
        refine ⟨u, v, huv, ?_, ?_, halt_uv⟩
        · simp [SimpleGraph.Walk.support_cons, hu]
        · simp [SimpleGraph.Walk.support_cons, hv]

/-- `A` is connected *inside* itself: any two vertices of `A` are joined by a walk that never
leaves `A`. -/
def ConnectedIn {V : Type*} (G : SimpleGraph V) (A : Set V) : Prop :=
  ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∃ P : G.Walk a₁ a₂, ∀ v ∈ P.support, v ∈ A

/-- **The editorial's 基础事实.**  Two vertex-disjoint subgraphs that are each internally
connected can never have their vertices alternate `A, B, A, B` around the circle.

The proof applies `walk_alternates_edge` twice: a path inside `B` yields an edge `{u,v}` of
`B` straddling `{a₁,a₂}`; by `alternates_swap`, `a₁` and `a₂` straddle `{u,v}`, so a path
inside `A` yields an edge of `A` crossing `{u,v}` — contradicting non-crossing. -/
theorem no_alternation_of_connectedIn {n : ℕ} (σ : CircOrder n) {G : SimpleGraph (Fin n)}
    (hr : IsRealizable σ G) {A B : Set (Fin n)}
    (hdisj : ∀ v : Fin n, v ∈ A → v ∈ B → False)
    (hA : ConnectedIn G A) (hB : ConnectedIn G B)
    {a₁ a₂ b₁ b₂ : Fin n} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
    (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) : ¬ σ.Alternates a₁ a₂ b₁ b₂ := by
  intro halt
  have ha₁a₂ : a₁ ≠ a₂ := by
    intro h
    have hbad : ¬ σ.Alternates a₁ a₁ b₁ b₂ := σ.alternates_irrefl_left a₁ b₁ b₂
    exact hbad (by simpa [h] using halt)
  obtain ⟨Q, hQ⟩ := hB b₁ hb₁ b₂ hb₂
  have ha₁Q : a₁ ∉ Q.support := fun h => hdisj a₁ ha₁ (hQ a₁ h)
  have ha₂Q : a₂ ∉ Q.support := fun h => hdisj a₂ ha₂ (hQ a₂ h)
  obtain ⟨u, v, huv, huQ, hvQ, halt_uv⟩ := walk_alternates_edge σ Q ha₁Q ha₂Q halt
  have huB : u ∈ B := hQ u huQ
  have hvB : v ∈ B := hQ v hvQ
  have huA : u ∉ A := fun h => hdisj u h huB
  have hvA : v ∉ A := fun h => hdisj v h hvB
  have huv_ne : u ≠ v := by
    intro h
    subst v
    exact G.irrefl huv
  have hswap : σ.Alternates u v a₁ a₂ := by
    apply σ.alternates_swap
    · intro h; exact huA (by simpa [h] using ha₁)
    · intro h; exact huA (by simpa [h] using ha₂)
    · intro h; exact hvA (by simpa [h] using ha₁)
    · intro h; exact hvA (by simpa [h] using ha₂)
    · exact ha₁a₂
    · exact huv_ne
    · exact halt_uv
  obtain ⟨P, hP⟩ := hA a₁ ha₁ a₂ ha₂
  have huP : u ∉ P.support := fun h => huA (hP u h)
  have hvP : v ∉ P.support := fun h => hvA (hP v h)
  obtain ⟨p, q, hpq, hpP, hqP, halt_pq⟩ := walk_alternates_edge σ P huP hvP hswap
  have hpA : p ∈ A := hP p hpP
  have hqA : q ∈ A := hP q hqP
  have hcross : σ.Crosses u v p q := by
    unfold CircOrder.Crosses
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact huv_ne
    · intro h
      subst q
      exact G.irrefl hpq
    · intro h
      exact huA (by simpa [h] using hpA)
    · intro h
      exact huA (by simpa [h] using hqA)
    · intro h
      exact hvA (by simpa [h] using hpA)
    · intro h
      exact hvA (by simpa [h] using hqA)
    · exact halt_pq
  exact hr u v p q huv hpq hcross

/-- `A` occupies a single arc of the circle: no two vertices outside `A` separate two
vertices inside `A`. -/
def CircleContiguous (σ : CircOrder n) (A : Set (Fin n)) : Prop :=
  ∀ {a₁ a₂ x y : Fin n}, a₁ ∈ A → a₂ ∈ A → x ∉ A → y ∉ A → ¬ σ.Alternates a₁ a₂ x y

/-- If `A` and its complement are both internally connected, `A` is a single arc. -/
theorem circle_contiguous_of_connected_complement {n : ℕ} (σ : CircOrder n)
    {G : SimpleGraph (Fin n)} (hr : IsRealizable σ G) {A : Set (Fin n)}
    (hA : ConnectedIn G A) (hAc : ConnectedIn G {v | v ∉ A}) :
    CircleContiguous σ A := by
  intro a₁ a₂ x y ha₁ ha₂ hx hy halt
  exact no_alternation_of_connectedIn σ hr (A := A) (B := {v | v ∉ A})
    (fun v hvA hvB => hvB hvA) hA hAc ha₁ ha₂ hx hy halt

end Graperm
