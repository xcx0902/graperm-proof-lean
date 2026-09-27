/-
# `GrapermProof.BlockOrder`

The **order** part of the assembly step of Claim 2.

`Assemble.merge_runs` shows that a family of pairwise disjoint runs covering `L` concatenate
to `L` in *some* order.  Here we settle *which* order: if the runs are listed in increasing
order of their circular position (or entirely the other way round), then the concatenation is
exactly their flatten (respectively the flatten of their reversal).

The only geometric input needed is that `arrangement σ` — the answer permutation — lists the
vertices in increasing order of their position on the circle (`arrangement_pairwise`).  From
that, `flatten_eq_of_runs_by_pos` is a pure induction on the number of runs: the first run of
the list must be a *prefix* of `L`, because anything standing before it would have to belong
to a later run and would then have a larger position, contradicting the fact that inside a run
of the answer permutation the list order is the position order.

Combining the two directions gives `block_runs_order`, which is precisely the order condition
that a block node of the block-cut tree imposes: the children are visited forwards or
backwards, never in a shuffled order.
-/
import GrapermProof.Assemble

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Graperm

variable {n : ℕ}

/-! ## 1. The answer permutation is sorted by circular position -/

/-- `List.range' s n` is strictly increasing, and all of its entries are `< s + n`. -/
theorem range'_pairwise (s n : ℕ) :
    (List.range' s n).Pairwise (fun a b => a < b ∧ a < s + n ∧ b < s + n) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
      rw [List.range'_succ]
      rw [List.pairwise_cons]
      constructor
      · intro a' ha'
        rw [List.mem_range'] at ha'
        obtain ⟨i, hi, rfl⟩ := ha'
        constructor
        · omega
        · constructor <;> omega
      · exact List.Pairwise.imp (fun h => ⟨h.1, by omega, by omega⟩) (ih (s + 1))

/-- **The answer permutation lists the vertices in increasing order of their position on the
circle.**  This is the whole content of "linearizing the circle at the root": the vertex at
position `i` is the `i`-th entry of `arrangement σ`. -/
theorem arrangement_pairwise (σ : CircOrder n) :
    (arrangement σ).Pairwise (fun x y : Fin n => (σ.pos x).val < (σ.pos y).val) := by
  unfold arrangement seg
  rw [List.pairwise_map]
  apply List.Pairwise.imp _ (range'_pairwise 0 n)
  intro a b h
  have ha : a % n = a := Nat.mod_eq_of_lt (by omega)
  have hb : b % n = b := Nat.mod_eq_of_lt (by omega)
  simp only [Equiv.apply_symm_apply]
  rw [ha, hb]
  exact h.1

/-- **Inside a run of the answer permutation the list order is the position order.**  If
`L = pre ++ mid ++ post` and `L` is a run of `arrangement σ`, then every vertex of `pre` has
smaller position than every vertex of `mid`. -/
theorem pos_lt_of_before_in_run (σ : CircOrder n) {L : List (Fin n)}
    (hL : IsRun (arrangement σ) L) {pre mid post : List (Fin n)}
    (h : L = pre ++ mid ++ post) :
    ∀ {x y : Fin n}, x ∈ pre → y ∈ mid → (σ.pos x).val < (σ.pos y).val := by
  let R : Fin n → Fin n → Prop := fun x y => (σ.pos x).val < (σ.pos y).val
  have hpair : (arrangement σ).Pairwise R := arrangement_pairwise σ
  rcases hL with ⟨A, B, hArr⟩
  have h1 : ((A ++ L) ++ B).Pairwise R := by
    simpa [hArr, List.append_assoc] using hpair
  have hLpair : L.Pairwise R := (List.pairwise_append.mp (List.pairwise_append.mp h1).1).2.1
  have h2 : ((pre ++ mid) ++ post).Pairwise R := by
    simpa [h, List.append_assoc] using hLpair
  have hcross : ∀ a ∈ pre, ∀ b ∈ mid, R a b :=
    (List.pairwise_append.mp (List.pairwise_append.mp h2).1).2.2
  exact fun {x y} hx hy => hcross x hx y hy

/-! ## 2. Runs listed in positional order concatenate in that order -/

/-- Every vertex of `A` precedes every vertex of `B` on the circle. -/
def posSep (σ : CircOrder n) (A B : List (Fin n)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, (σ.pos x).val < (σ.pos y).val

/-- A family of vertex sets is listed in increasing order of position. -/
def VertsByPos (σ : CircOrder n) (As : List (List (Fin n))) : Prop :=
  As.Pairwise (posSep σ)

/-- A nonempty list has an element. -/
theorem exists_mem_of_ne_nil {l : List (Fin n)} (h : l ≠ []) : ∃ x, x ∈ l := by
  cases h' : l with
  | nil => exact False.elim (h h')
  | cons x t => exact ⟨x, by simp⟩

/-- **Concatenation in positional order.**  Let `L` be a repetition-free run of the answer
permutation and let `ms` be a repetition-free family of nonempty, pairwise disjoint runs of
`L` which together contain every vertex of `L`.  If `ms` is listed in increasing order of
position, then `L` is exactly the concatenation `ms.flatten`.

The proof is an induction on `ms`: the first member `m` of `ms` must be a *prefix* of `L`.
Indeed if `x` stood before `m` in `L`, then `x` would lie in some member `m'` of `ms`; it
cannot be `m` itself (`L` has no repetition) and it cannot be a later one (later members have
larger positions, but `x` precedes `m` inside a run of the answer permutation, so it has a
smaller position). -/
theorem flatten_eq_of_runs_by_pos (σ : CircOrder n) :
    ∀ (ms : List (List (Fin n))) (L : List (Fin n)),
      IsRun (arrangement σ) L →
        L.Nodup →
        (∀ m ∈ ms, IsRun L m) →
        (∀ m ∈ ms, m ≠ []) →
        (∀ b₁ ∈ ms, ∀ b₂ ∈ ms, b₁ ≠ b₂ → ListDisj b₁ b₂) →
        ms.Nodup →
        (∀ x ∈ L, ∃ m ∈ ms, x ∈ m) →
        VertsByPos σ ms →
        L = ms.flatten := by
  intro ms
  induction ms with
  | nil =>
      intro L hLrun hLnod hrun hne hdisj hnod hcov hvb
      have hL : L = [] := by
        cases L with
        | nil => rfl
        | cons x t =>
            exfalso
            obtain ⟨m, hm, _⟩ := hcov x (by simp)
            simpa using hm
      simp [hL]
  | cons m rest ih =>
      intro L hLrun hLnod hrun hne hdisj hnod hcov hvb
      obtain ⟨pre, post, hL⟩ := hrun m (by simp)
      have hpre : pre = [] := by
        cases pre with
        | nil => rfl
        | cons x pre' =>
            exfalso
            have hxL : x ∈ L := by rw [hL]; simp
            obtain ⟨m', hm'ms, hxm'⟩ := hcov x hxL
            by_cases heq : m' = m
            · have hnod1 : ((x :: pre') ++ (m ++ post)).Nodup := by
                simpa [hL, List.append_assoc] using hLnod
              have hd := (List.nodup_append.mp hnod1).2.2
              exact (hd x (by simp) x (List.mem_append.mpr (Or.inl (by simpa [heq] using hxm')))) rfl
            · have hm'rest : m' ∈ rest := by
                rcases List.mem_cons.mp hm'ms with h | h
                · exact False.elim (heq h)
                · exact h
              obtain ⟨y, hy⟩ := exists_mem_of_ne_nil (hne m (by simp))
              have hlt1 : (σ.pos y).val < (σ.pos x).val :=
                (List.pairwise_cons.mp hvb).1 m' hm'rest y hy x hxm'
              have hlt2 : (σ.pos x).val < (σ.pos y).val :=
                pos_lt_of_before_in_run σ hLrun hL (by simp) hy
              omega
      have hLm : L = m ++ post := by simpa [hpre] using hL
      have hm_not_rest : m ∉ rest := (List.nodup_cons.mp hnod).1
      have hrest_nod : rest.Nodup := (List.nodup_cons.mp hnod).2
      have hnod_mp : (m ++ post).Nodup := by simpa [hLm] using hLnod
      have hpost_nod : post.Nodup := (List.nodup_append.mp hnod_mp).2.1
      have hpost_disj_m : ∀ v ∈ post, v ∉ m := by
        have hd := (List.nodup_append.mp hnod_mp).2.2
        intro v hv hvm
        exact (hd v hvm v hv) rfl
      have hpost_run : IsRun (arrangement σ) post := by
        rcases hLrun with ⟨A, B, hArr⟩
        refine ⟨A ++ m, B, ?_⟩
        rw [hArr, hLm]
        simp [List.append_assoc]
      have hrun' : ∀ m' ∈ rest, IsRun post m' := by
        intro m' hm'
        have hm'_ms : m' ∈ m :: rest := List.mem_cons_of_mem m hm'
        have hm_ne : m ≠ m' := by
          intro hmm
          exact hm_not_rest (by rw [hmm]; exact hm')
        have hdj : ListDisj m m' := hdisj m (by simp) m' hm'_ms hm_ne
        have hr : IsRun (m ++ post) m' := by simpa [hLm] using hrun m' hm'_ms
        exact isRun_append_left m hr (fun a ha => hdj a ha)
      have hdisj' : ∀ b₁ ∈ rest, ∀ b₂ ∈ rest, b₁ ≠ b₂ → ListDisj b₁ b₂ := by
        intro b₁ hb₁ b₂ hb₂ hne'
        exact hdisj b₁ (List.mem_cons_of_mem m hb₁) b₂ (List.mem_cons_of_mem m hb₂) hne'
      have hne' : ∀ m' ∈ rest, m' ≠ [] := fun m' hm' => hne m' (List.mem_cons_of_mem m hm')
      have hcov' : ∀ x ∈ post, ∃ m' ∈ rest, x ∈ m' := by
        intro x hx
        have hxL : x ∈ L := by rw [hLm]; exact List.mem_append.mpr (Or.inr hx)
        obtain ⟨m', hm'ms, hxm'⟩ := hcov x hxL
        refine ⟨m', ?_, hxm'⟩
        rcases List.mem_cons.mp hm'ms with h | h
        · exfalso
          exact hpost_disj_m x hx (by simpa [h] using hxm')
        · exact h
      have hvb' : VertsByPos σ rest := (List.pairwise_cons.mp hvb).2
      have hres : post = rest.flatten :=
        ih post hpost_run hpost_nod hrun' hne' hdisj' hrest_nod hcov' hvb'
      rw [hLm, hres]
      rfl

/-- **The order condition at a block node.**  Under the hypotheses of
`flatten_eq_of_runs_by_pos`, if the runs are listed in increasing order of position then
`L = ms.flatten`; if they are listed in decreasing order (equivalently: the reversal is
increasing) then `L = ms.reverse.flatten`.  These are the only two orders in which the
children of a block can be visited. -/
theorem block_runs_order (σ : CircOrder n) {L : List (Fin n)} {ms : List (List (Fin n))}
    (hLrun : IsRun (arrangement σ) L) (hLnod : L.Nodup)
    (hrun : ∀ m ∈ ms, IsRun L m) (hne : ∀ m ∈ ms, m ≠ [])
    (hdisj : ∀ b₁ ∈ ms, ∀ b₂ ∈ ms, b₁ ≠ b₂ → ListDisj b₁ b₂)
    (hnod : ms.Nodup) (hcov : ∀ x ∈ L, ∃ m ∈ ms, x ∈ m)
    (horder : VertsByPos σ ms ∨ VertsByPos σ ms.reverse) :
    L = ms.flatten ∨ L = ms.reverse.flatten := by
  rcases horder with h | h
  · exact Or.inl (flatten_eq_of_runs_by_pos σ ms L hLrun hLnod hrun hne hdisj hnod hcov h)
  · have hrevnod : ms.reverse.Nodup := by simpa using hnod
    have hrevne : ∀ m ∈ ms.reverse, m ≠ [] := by
      intro m hm
      exact hne m (by simpa using hm)
    have hrevrun : ∀ m ∈ ms.reverse, IsRun L m := by
      intro m hm
      exact hrun m (by simpa using hm)
    have hrevdisj : ∀ b₁ ∈ ms.reverse, ∀ b₂ ∈ ms.reverse,
        b₁ ≠ b₂ → ListDisj b₁ b₂ := by
      intro b₁ hb₁ b₂ hb₂ hne'
      exact hdisj b₁ (by simpa using hb₁) b₂ (by simpa using hb₂) hne'
    have hrevcov : ∀ x ∈ L, ∃ m ∈ ms.reverse, x ∈ m := by
      intro x hx
      obtain ⟨m, hm, hxm⟩ := hcov x hx
      exact ⟨m, by simpa using hm, hxm⟩
    exact Or.inr (flatten_eq_of_runs_by_pos σ ms.reverse L hLrun hLnod hrevrun hrevne
      hrevdisj hrevnod hrevcov h)

end Graperm
