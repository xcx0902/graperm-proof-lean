/-
# `GrapermProof.OuterCycle`

Claim 1 of the editorial, made precise.

Fix a 2-connected graph `G` on `Fin n` together with a non-crossing circular realization `σ`
(an `IsRealizable` circular order).  Then **every vertex is adjacent to its cyclic
successor**.  Hence the cyclically consecutive pairs of `σ` are edges of `G`, so they form a
Hamiltonian cycle of `G` — the *outer cycle*.  Moreover any non-crossing Hamiltonian cycle of
`G` must use exactly these edges (see `hamiltonian_cycle_uses_outer_edges`).
-/
import GrapermProof.Basic

namespace Graperm

open CircOrder

variable {n : ℕ}

/-- **Claim 1 (main lemma).**  If `G` is 2-connected and `σ` is a non-crossing circular
order for `G` (on at least three vertices), then every vertex is adjacent to its cyclic
successor.

The proof follows the editorial: suppose `v₀` is not adjacent to its successor `v₁`, and let
`i ≥ 2` be the index of the first neighbour `uᵢ` of `v₀` along the circle starting at `v₀`.
Writing `T = {u₁, …, u_{i-1}}`, one shows that no edge leaves `T` except possibly to `uᵢ`
(edges `u₀uᵢ` and `u_k u_m` with `0 < k < i < m` would cross).  Hence deleting `uᵢ`
disconnects `T` from `v₀`, contradicting 2-connectivity. -/
theorem succ_adj (σ : CircOrder n) (G : SimpleGraph (Fin n))
    (h3 : 3 ≤ n) (hconn : IsTwoConn G) (hr : IsRealizable σ G) (v0 : Fin n) :
    G.Adj v0 (σ.succ v0) := by
  classical
  obtain ⟨hpre, hdel⟩ := hconn
  have hn1 : 1 < n := by omega
  have hn0 : 0 < n := σ.hn
  have hzero : σ.iter v0 0 = v0 := σ.iter_zero v0
  have hfwd : ∀ j, j < n → σ.fwd v0 (σ.iter v0 j) = j := fun j hj => σ.fwd_iter_zero v0 j hj
  have hinj : ∀ {j k : ℕ}, j < n → k < n → σ.iter v0 j = σ.iter v0 k → j = k :=
    fun {j k} hj hk h => σ.iter_inj v0 hj hk h
  have hsurj : ∀ z : Fin n, σ.iter v0 (σ.fwd v0 z) = z := fun z => σ.iter_fwd v0 z
  have hfwdlt : ∀ z : Fin n, σ.fwd v0 z < n := fun z => σ.fwd_lt v0 z
  have hfwd0 : ∀ t, t < n → σ.fwd (σ.iter v0 0) (σ.iter v0 t) = t := by
    intro t ht
    rw [hzero]
    exact hfwd t ht
  by_contra hnot
  -- `v₀` has a neighbour, and every neighbour is some `u j`
  have hex : ∃ j, 1 ≤ j ∧ j < n ∧ G.Adj v0 (σ.iter v0 j) := by
    have hne : σ.succ v0 ≠ v0 := by
      intro h
      have := σ.fwd_succ v0 hn1
      rw [h, σ.fwd_self] at this
      omega
    obtain ⟨p⟩ := hpre v0 (σ.succ v0)
    obtain ⟨z, hadj, p', -⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hne.symm p
    refine ⟨σ.fwd v0 z, ?_, hfwdlt z, ?_⟩
    · have hz0 : σ.fwd v0 z ≠ 0 := by
        intro hc
        have hz : z = v0 := (σ.fwd_eq_zero_iff v0 z).mp hc
        rw [hz] at hadj
        exact G.irrefl hadj
      omega
    · rw [hsurj z]; exact hadj
  -- `i` is the minimal such index
  set i : ℕ := Nat.find hex with hi_def
  have hispec : 1 ≤ i ∧ i < n ∧ G.Adj v0 (σ.iter v0 i) := by
    have := Nat.find_spec hex
    rw [← hi_def] at this
    exact this
  obtain ⟨hi1, hi2, hiadj⟩ := hispec
  have himin : ∀ j, 1 ≤ j → j < n → G.Adj v0 (σ.iter v0 j) → i ≤ j :=
    fun j hj1 hj2 hjadj => Nat.find_min' hex ⟨hj1, hj2, hjadj⟩
  have hi_ge2 : 2 ≤ i := by
    by_contra hc
    have hi_eq : i = 1 := by omega
    rw [hi_eq] at hiadj
    exact hnot (by simpa [CircOrder.succ] using hiadj)
  -- `T` collects the vertices strictly between `v₀` and `uᵢ`
  set T : Set (Fin n) := {w | ∃ j, 1 ≤ j ∧ j < i ∧ σ.iter v0 j = w} with hT
  have hT1 : σ.iter v0 1 ∈ T := by
    rw [hT]; exact ⟨1, le_refl 1, by omega, rfl⟩
  have hTv0 : v0 ∉ T := by
    rw [hT]
    rintro ⟨j, hj1, hj2, hjeq⟩
    have hjn : j < n := by omega
    have heq : σ.iter v0 j = σ.iter v0 0 := by rw [hjeq, hzero]
    have : j = 0 := hinj hjn hn0 heq
    omega
  -- the crucial edge-closure property of `T`
  have hedge : ∀ w ∈ T, ∀ z : Fin n, G.Adj w z → z ∈ T ∨ z = σ.iter v0 i := by
    intro w hw z hadj
    rw [hT] at hw
    rcases hw with ⟨j, hj1, hj2, rfl⟩
    have hjn : j < n := by omega
    rw [hT]
    set m : ℕ := σ.fwd v0 z with hm_def
    have hm_lt : m < n := by rw [hm_def]; exact hfwdlt z
    have hz : σ.iter v0 m = z := by rw [hm_def]; exact hsurj z
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · exfalso
      have hz0 : z = v0 := by
        have : σ.fwd v0 z = 0 := by rw [hm_def] at hm0; omega
        exact (σ.fwd_eq_zero_iff v0 z).mp this
      rw [hz0] at hadj
      have hle : i ≤ j := himin j hj1 hjn hadj.symm
      omega
    · rcases lt_trichotomy m i with hlt | heq | hgt
      · exact Or.inl ⟨m, hmpos, hlt, hz⟩
      · exact Or.inr (by rw [← hz, heq])
      · exfalso
        have hcross : σ.Crosses (σ.iter v0 0) (σ.iter v0 i) (σ.iter v0 j) (σ.iter v0 m) := by
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro h; have : (0:ℕ) = i := hinj hn0 hi2 h; omega
          · intro h; have : j = m := hinj hjn hm_lt h; omega
          · intro h; have : (0:ℕ) = j := hinj hn0 hjn h; omega
          · intro h; have : (0:ℕ) = m := hinj hn0 hm_lt h; omega
          · intro h; have : i = j := hinj hi2 hjn h; omega
          · intro h; have : i = m := hinj hi2 hm_lt h; omega
          · have hB1 : σ.Between (σ.iter v0 j) (σ.iter v0 0) (σ.iter v0 i) := by
              simp only [CircOrder.Between, hfwd0 j hjn, hfwd0 i hi2]
              exact ⟨by omega, hj2⟩
            have hB2 : ¬ σ.Between (σ.iter v0 m) (σ.iter v0 0) (σ.iter v0 i) := by
              simp only [CircOrder.Between, hfwd0 m hm_lt, hfwd0 i hi2]
              rintro ⟨-, hlt2⟩
              omega
            exact ⟨fun _ => hB2, fun _ => hB1⟩
        exact hr _ _ _ _ (by rw [hzero]; exact hiadj) (by rw [hz]; exact hadj) hcross
  -- any walk starting in `T` and avoiding `uᵢ` stays in `T`
  have hstay : ∀ {a b : Fin n}, ∀ (p : G.Walk a b), a ∈ T → σ.iter v0 i ∉ p.support → b ∈ T := by
    intro a b p
    induction p with
    | nil => intro ha _; exact ha
    | cons hadj p' ih =>
      intro ha hnotmem
      rw [SimpleGraph.Walk.support_cons] at hnotmem
      have hnotmem' : σ.iter v0 i ∉ p'.support :=
        fun hc => hnotmem (List.mem_cons_of_mem _ hc)
      rcases hedge _ ha _ hadj with hv | hv
      · exact ih hv hnotmem'
      · exfalso
        apply hnotmem
        rw [← hv]
        exact List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support p')
  have hne1 : σ.iter v0 1 ≠ σ.iter v0 i := by
    intro h
    have : (1:ℕ) = i := hinj hn1 hi2 h
    omega
  have hne2 : v0 ≠ σ.iter v0 i := by
    intro h
    have heq : σ.iter v0 0 = σ.iter v0 i := by rw [hzero]; exact h
    have : (0:ℕ) = i := hinj hn0 hi2 heq
    omega
  obtain ⟨p, hp⟩ := hdel (σ.iter v0 i) (σ.iter v0 1) v0 hne1 hne2
  exact hTv0 (hstay p hT1 hp)

/-- **Claim 1 (conclusion, existence).**  In a 2-connected graph with a non-crossing circular
order, the cyclically consecutive pairs of the order are edges of the graph, i.e. they form a
Hamiltonian cycle of `G` — the *outer cycle*. -/
theorem outer_cycle_is_hamiltonian (σ : CircOrder n) (G : SimpleGraph (Fin n))
    (h3 : 3 ≤ n) (hconn : IsTwoConn G) (hr : IsRealizable σ G) :
    ∀ v : Fin n, G.Adj v (σ.succ v) :=
  fun v => succ_adj σ G h3 hconn hr v

/-- **Claim 1 (conclusion, uniqueness).**  Any non-crossing Hamiltonian cycle of `G` must use
exactly the edges of the outer cycle.

Here a "Hamiltonian cycle" of `G` is encoded as a spanning subgraph `H ≤ G` which is
2-connected and 2-regular (each vertex has exactly two `H`-neighbours).  Since a 2-connected
2-regular graph is a single cycle, this is precisely a Hamiltonian cycle.  The conclusion
`b = σ.succ a ∨ a = σ.succ b` says that each edge of `H` joins cyclically consecutive vertices,
matching the editorial's "任何哈密顿环都只能使用外环的边". -/
theorem hamiltonian_cycle_uses_outer_edges (σ : CircOrder n) (G H : SimpleGraph (Fin n))
    (h3 : 3 ≤ n) (hHG : H ≤ G) (hHconn : IsTwoConn H)
    (hHdeg : ∀ v : Fin n, (H.neighborSet v).ncard = 2) (hr : IsRealizable σ G) :
    ∀ a b : Fin n, H.Adj a b → (b = σ.succ a ∨ a = σ.succ b) := by
  have hrH : IsRealizable σ H :=
    fun a b c d hab hcd hcross => hr a b c d (hHG hab) (hHG hcd) hcross
  have hsucc : ∀ v : Fin n, H.Adj v (σ.succ v) := fun v => succ_adj σ H h3 hHconn hrH v
  intro a b hab
  rcases eq_or_ne b (σ.succ a) with hb | hb
  · exact Or.inl hb
  · right
    have hpair_sub : ({σ.succ a, σ.pred a} : Set (Fin n)) ⊆ H.neighborSet a := by
      intro x hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hsucc a
      · have h' : H.Adj (σ.succ (σ.pred a)) (σ.pred a) := (hsucc (σ.pred a)).symm
        rw [σ.succ_pred a] at h'
        exact h'
    have heq : ({σ.succ a, σ.pred a} : Set (Fin n)) = H.neighborSet a :=
      Set.eq_of_subset_of_ncard_le hpair_sub
        (by rw [hHdeg a, Set.ncard_pair (σ.succ_ne_pred a h3)])
    have hba : b ∈ ({σ.succ a, σ.pred a} : Set (Fin n)) := by
      rw [heq]; exact hab
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hba
    rcases hba with hba | hba
    · exact absurd hba hb
    · rw [hba, σ.succ_pred a]

end Graperm
