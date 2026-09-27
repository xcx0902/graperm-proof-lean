/-
# `GrapermProof.Assemble`

The **assembly step** of Claim 2.  `Separation.lean` shows that every subtree of the
block-cut tree occupies one contiguous arc of the circle, and `Arrange.lean` turns that into
contiguity inside the linear answer permutation.  What is still missing in order to conclude
that a *realizable* circular order produces an **admissible** arrangement (`Part.Valid`) is
purely combinatorial bookkeeping:

* pairwise disjoint contiguous runs of a list can be **concatenated in positional order**, and
  the resulting concatenation is a *permutation* of the runs (§1);
* conversely, a set which is contiguous in the circular sense really does occupy one run of the
  permutation (§2).

§1 is proved here in complete generality, for arbitrary lists; §2 connects it to
`LinearContig`.  Both together say: *any* non-crossing circular order yields an arrangement
that the block-cut recursion is allowed to produce — the completeness direction of Claim 2.
-/
import GrapermProof.Arrange

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Graperm

/-! ## 1. Contiguous runs and their merging -/

/-- The list `m` occurs as a **contiguous run** of `L`: `L = pre ++ m ++ post`. -/
def IsRun {V : Type*} (L m : List V) : Prop := ∃ pre post : List V, L = pre ++ m ++ post

/-- Two lists share no element. -/
def ListDisj {V : Type*} (l₁ l₂ : List V) : Prop := ∀ x ∈ l₁, x ∉ l₂

/-- The empty list is a run of anything. -/
theorem isRun_nil {V : Type*} (L : List V) : IsRun L ([] : List V) := ⟨[], L, by simp⟩

/-- Every list is a run of itself. -/
theorem isRun_self {V : Type*} (L : List V) : IsRun L L := ⟨[], [], by simp⟩

/-- **Peeling the head.**  A run of `a :: L` that does not contain `a` is a run of `L`. -/
theorem isRun_cons_of_not_mem {V : Type*} {a : V} {L m : List V}
    (h : IsRun (a :: L) m) (ha : a ∉ m) : IsRun L m := by
  obtain ⟨pre, post, hL⟩ := h
  cases m with
  | nil => exact ⟨[], L, by simp⟩
  | cons y m' =>
      cases pre with
      | nil =>
          exfalso
          have hL' : a :: L = y :: (m' ++ post) := by simpa using hL
          have hay : a = y := by simpa using congrArg List.head? hL'
          exact ha (by rw [hay]; simp)
      | cons c pre' =>
          have hL' : a :: L = c :: (pre' ++ (y :: m') ++ post) := by
            simpa [List.cons_append] using hL
          have hL'' : L = pre' ++ (y :: m') ++ post := by
            simpa using congrArg List.tail hL'
          exact ⟨pre', post, hL''⟩

/-- **Peeling a prefix.**  A run of `pre ++ post` avoiding every element of `pre` is a run of
`post`. -/
theorem isRun_append_left {V : Type*} (pre : List V) {post m : List V}
    (h : IsRun (pre ++ post) m) (hnot : ∀ a ∈ pre, a ∉ m) : IsRun post m := by
  induction pre with
  | nil => simpa using h
  | cons a t ih =>
      exact ih (isRun_cons_of_not_mem (by simpa using h) (hnot a (by simp)))
        (fun a' ha' => hnot a' (by simp [ha']))

/-- **Peeling a suffix.**  A run of `L ++ post` avoiding every element of `post` is a run of
`L`. -/
theorem isRun_append_right {V : Type*} {L post m : List V}
    (h : IsRun (L ++ post) m) (hnot : ∀ a ∈ post, a ∉ m) : IsRun L m := by
  have hr : IsRun ((L ++ post).reverse) m.reverse := by
    obtain ⟨pre, post', hL⟩ := h
    refine ⟨post'.reverse, pre.reverse, ?_⟩
    rw [hL]
    simp [List.reverse_append]
  have hr' : IsRun (post.reverse ++ L.reverse) m.reverse := by
    simpa [List.reverse_append] using hr
  have hr'' : IsRun L.reverse m.reverse :=
    isRun_append_left post.reverse hr' (by
      intro a ha
      have : a ∈ post := by simpa using ha
      simpa using hnot a this)
  obtain ⟨pre, post₀, hLrev⟩ := hr''
  refine ⟨post₀.reverse, pre.reverse, ?_⟩
  have := congrArg List.reverse hLrev
  simpa [List.reverse_append] using this

/-- **Restricting the ambient list.**  A run of `pre ++ L ++ post` that avoids both `pre` and
`post` is a run of `L`. -/
theorem isRun_of_subrun {V : Type*} {A L m pre post : List V}
    (hA : A = pre ++ L ++ post) (h : IsRun A m)
    (hpre : ∀ a ∈ pre, a ∉ m) (hpost : ∀ a ∈ post, a ∉ m) : IsRun L m := by
  have h0 : IsRun (pre ++ L ++ post) m := by simpa [hA] using h
  have h1 : IsRun (pre ++ (L ++ post)) m := by simpa [List.append_assoc] using h0
  have h2 : IsRun (L ++ post) m := isRun_append_left pre h1 hpre
  exact isRun_append_right h2 hpost

/-- A run of a repetition-free list is repetition-free. -/
theorem nodup_of_isRun {V : Type*} {L m : List V} (hL : L.Nodup) (hm : IsRun L m) :
    m.Nodup := by
  obtain ⟨pre, post, hp⟩ := hm
  have hn : ((pre ++ m) ++ post).Nodup := by
    simpa [List.append_assoc] using
      (by simpa [hp] using hL : (pre ++ m ++ post).Nodup)
  exact (List.nodup_append.mp (List.nodup_append.mp hn).1).2.1

/-- Runs compose: a run of a run is a run. -/
theorem isRun_trans {V : Type*} {A L m : List V} (hL : IsRun A L) (hm : IsRun L m) :
    IsRun A m := by
  obtain ⟨p₁, p₂, hA⟩ := hL
  obtain ⟨q₁, q₂, hL'⟩ := hm
  refine ⟨p₁ ++ q₁, q₂ ++ p₂, ?_⟩
  rw [hA, hL']
  simp [List.append_assoc]

/-- Splitting a list at an occurrence of one of its elements. -/
theorem list_mem_split {V : Type*} {a : V} {l : List V} (h : a ∈ l) :
    ∃ l₁ l₂ : List V, l = l₁ ++ a :: l₂ := by
  induction l with
  | nil => simpa using h
  | cons x t ih =>
      simp at h
      rcases h with rfl | h'
      · exact ⟨[], t, rfl⟩
      · obtain ⟨l₁, l₂, ht⟩ := ih h'
        exact ⟨x :: l₁, l₂, by simp [ht]⟩

/-- What the merging lemma has to prove, isolated so that it can be used as an induction
motive. -/
def MergeSpec {V : Type*} (bs : List (List V)) (L : List V) : Prop :=
  L.Nodup →
    (∀ b ∈ bs, IsRun L b) →
    (∀ b₁ ∈ bs, ∀ b₂ ∈ bs, b₁ ≠ b₂ → ListDisj b₁ b₂) →
    (∀ v ∈ L, ∃ b ∈ bs, v ∈ b) →
    bs.Nodup →
    ∃ T : List (List V), T.Perm bs ∧ L = T.flatten

/-- **Merging lemma.**  Let `L` be a list without repetitions and let `bs` be a repetition-free
family of pairwise disjoint lists, each of which occurs as a contiguous run of `L`, such that
every element of `L` belongs to one of them.  Then `L` is the concatenation of the members of
`bs` in the order in which they occur, i.e. it is the flatten of a *permutation* of `bs`.

This is exactly the combinatorial content of "the children of a node of the block-cut tree
occupy disjoint intervals, hence the answer is obtained by concatenating them in some order":
the order is forced by the positions, and `Part.Valid` allows precisely the orders that arise
this way. -/
theorem merge_runs {V : Type*} : ∀ (bs : List (List V)) (L : List V), MergeSpec bs L := by
  have aux : ∀ k : ℕ, ∀ (bs : List (List V)), bs.length = k → ∀ L : List V, MergeSpec bs L := by
    intro k
    induction k with
    | zero =>
        intro bs hlen L hnod hrun hdisj hcov hnodbs
        have hbs : bs = [] := List.length_eq_zero_iff.mp hlen
        subst bs
        have hL : L = [] := by
          cases L with
          | nil => rfl
          | cons x t =>
              exfalso
              obtain ⟨b, hb, _⟩ := hcov x (by simp)
              simpa using hb
        subst L
        exact ⟨[], by simp, by simp⟩
    | succ k ih =>
        intro bs hlen L hnod hrun hdisj hcov hnodbs
        cases L with
        | nil =>
            have hb_nil : ∀ b ∈ bs, b = [] := by
              intro b hb
              obtain ⟨pre, post, hL⟩ := hrun b hb
              have hlen0 : (pre ++ b ++ post).length = 0 := by
                rw [← hL]
                simp
              have hle : b.length ≤ (pre ++ b ++ post).length := by
                simp [List.length_append]
                omega
              exact List.length_eq_zero_iff.mp (by omega)
            refine ⟨bs, ?_, ?_⟩
            · rfl
            · symm
              exact List.flatten_eq_nil_iff.mpr hb_nil
        | cons x L' =>
            obtain ⟨b, hb, hxb⟩ := hcov x (by simp)
            obtain ⟨bs₁, bs₂, hsplit⟩ := list_mem_split hb
            obtain ⟨pre, post, hrunb⟩ := hrun b hb
            have hpre : pre = [] := by
              cases pre with
              | nil => rfl
              | cons c pre' =>
                  exfalso
                  have hL2 : x :: L' = c :: (pre' ++ b ++ post) := by
                    simpa [List.cons_append] using hrunb
                  have hcx : c = x := by simpa using (congrArg List.head? hL2).symm
                  have hdup : ¬ ((c :: pre') ++ b ++ post).Nodup := by
                    intro hn
                    have hn' : ((c :: pre') ++ (b ++ post)).Nodup := by
                      simpa [List.append_assoc] using hn
                    have hd := (List.nodup_append.mp hn').2.2
                    exact (hd c (by simp) c (by simp [hcx, hxb])) rfl
                  exact hdup (by simpa [hrunb] using hnod)
            have hLb : x :: L' = b ++ post := by simpa [hpre] using hrunb
            have hnod_bpost : (b ++ post).Nodup := by simpa [hLb] using hnod
            have hpost_disj_b : ∀ v ∈ post, v ∉ b := by
              have hd := (List.nodup_append.mp hnod_bpost).2.2
              intro v hv hvb
              exact (hd v hvb v hv) rfl
            have hnod_post : post.Nodup := (List.nodup_append.mp hnod_bpost).2.1
            have hb_not_rest : b ∉ bs₁ ++ bs₂ := by
              have hn : (bs₁ ++ (b :: bs₂)).Nodup := by simpa [hsplit] using hnodbs
              obtain ⟨hn_bs1, hn_b_bs2, hd⟩ := List.nodup_append.mp hn
              have hb_not_bs2 : b ∉ bs₂ := by
                have := List.nodup_cons.mp hn_b_bs2
                exact this.1
              have hb_not_bs1 : b ∉ bs₁ := by
                intro hb1
                exact (hd b hb1 b (by simp)) rfl
              intro hb12
              rcases List.mem_append.mp hb12 with h | h
              · exact hb_not_bs1 h
              · exact hb_not_bs2 h
            let bs' : List (List V) := bs₁ ++ bs₂
            have hlen' : bs'.length = k := by
              rw [hsplit] at hlen
              simp [bs'] at hlen ⊢
              omega
            have mem_bs'_bs : ∀ {b' : List V}, b' ∈ bs' → b' ∈ bs := by
              intro b' hb'
              rw [hsplit]
              rcases List.mem_append.mp hb' with h | h
              · exact List.mem_append.mpr (Or.inl h)
              · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem b h))
            have hrun' : ∀ b' ∈ bs', IsRun post b' := by
              intro b' hb'
              have hb'_bs : b' ∈ bs := mem_bs'_bs hb'
              have hb_ne : b ≠ b' := by
                intro heq
                exact hb_not_rest (by rw [heq]; exact hb')
              have hdisj_bb' : ListDisj b b' := hdisj b hb b' hb'_bs hb_ne
              have hrun_b' : IsRun (x :: L') b' := hrun b' hb'_bs
              have hrun_b'_bpost : IsRun (b ++ post) b' := by simpa [hLb] using hrun_b'
              exact isRun_append_left b hrun_b'_bpost hdisj_bb'
            have hdisj' : ∀ b₁' ∈ bs', ∀ b₂' ∈ bs', b₁' ≠ b₂' → ListDisj b₁' b₂' := by
              intro b₁' hb₁' b₂' hb₂' hne
              exact hdisj b₁' (mem_bs'_bs hb₁') b₂' (mem_bs'_bs hb₂') hne
            have hcov' : ∀ v ∈ post, ∃ b' ∈ bs', v ∈ b' := by
              intro v hv
              obtain ⟨b'', hb''bs, hvb''⟩ := hcov v (by
                rw [hLb]
                exact List.mem_append.mpr (Or.inr hv))
              have hb''ne : b'' ≠ b := by
                intro heq
                exact hpost_disj_b v hv (by rw [← heq]; exact hvb'')
              refine ⟨b'', ?_, hvb''⟩
              rw [hsplit] at hb''bs
              rcases List.mem_append.mp hb''bs with h | h
              · exact List.mem_append.mpr (Or.inl h)
              · rcases List.mem_cons.mp h with heq | h
                · exact False.elim (hb''ne heq)
                · exact List.mem_append.mpr (Or.inr h)
            have hnodbs' : bs'.Nodup := by
              have hn : (bs₁ ++ (b :: bs₂)).Nodup := by simpa [hsplit] using hnodbs
              obtain ⟨hn1, hn2, hd⟩ := List.nodup_append.mp hn
              have hn2' : bs₂.Nodup := (List.nodup_cons.mp hn2).2
              exact List.nodup_append.mpr ⟨hn1, hn2', by
                intro a ha b'' hb''
                exact hd a ha b'' (List.mem_cons_of_mem b hb'')⟩
            obtain ⟨T', hT'perm, hT'flat⟩ :=
              ih bs' hlen' post hnod_post hrun' hdisj' hcov' hnodbs'
            refine ⟨b :: T', ?_, ?_⟩
            · have h1 : (b :: T').Perm (b :: bs') := List.Perm.cons b hT'perm
              have h2 : (b :: bs').Perm (bs₁ ++ b :: bs₂) := by
                simpa [bs'] using (List.perm_middle (a := b) (l₁ := bs₁) (l₂ := bs₂)).symm
              exact h1.trans (h2.trans (by simpa [hsplit]))
            · rw [List.flatten_cons, ← hT'flat, ← hLb]
  intro bs L
  exact aux bs.length bs rfl L

/-! ## 2. From contiguity on the circle to a run of the permutation -/

variable {n : ℕ}

/-- Bounds for the elements of `List.range' lo len`. -/
theorem mem_range'_bounds {lo len i : ℕ} (hi : i ∈ List.range' lo len) :
    lo ≤ i ∧ i < lo + len := by
  rw [List.range'_eq_map_range, List.mem_map] at hi
  obtain ⟨j, hj, hji⟩ := hi
  rw [List.mem_range] at hj
  omega

/-- Membership in a segment is membership of the position in the corresponding interval. -/
theorem mem_seg (σ : CircOrder n) {lo len : ℕ} (hle : lo + len ≤ n) (v : Fin n) :
    v ∈ seg σ lo len ↔ lo ≤ (σ.pos v).val ∧ (σ.pos v).val < lo + len := by
  unfold seg
  rw [List.mem_map]
  constructor
  · rintro ⟨i, hi, hiv⟩
    have hpos : σ.pos v = ⟨i % n, Nat.mod_lt i σ.hn⟩ := by
      rw [← hiv]
      exact Equiv.apply_symm_apply σ.pos _
    have hbi := mem_range'_bounds hi
    have hval : (σ.pos v).val = i := by
      rw [hpos]
      exact Nat.mod_eq_of_lt (by omega)
    omega
  · rintro ⟨hlo, hhi⟩
    refine ⟨(σ.pos v).val, ?_, ?_⟩
    · rw [List.range'_eq_map_range, List.mem_map]
      refine ⟨(σ.pos v).val - lo, ?_, ?_⟩
      · rw [List.mem_range]
        omega
      · omega
    · apply σ.pos.injective
      rw [Equiv.apply_symm_apply]
      exact Fin.ext (by simp [Nat.mod_eq_of_lt (σ.pos v).isLt])

/-- A segment contains no repeated vertex. -/
theorem seg_nodup (σ : CircOrder n) {lo len : ℕ} (hle : lo + len ≤ n) :
    (seg σ lo len).Nodup := by
  induction len generalizing lo with
  | zero => simp [seg]
  | succ len ih =>
      have hle' : lo + len ≤ n := by omega
      have hlt : lo + len < n := by omega
      have hx : seg σ (lo + len) 1 =
          [σ.pos.symm ⟨(lo + len) % n, Nat.mod_lt (lo + len) σ.hn⟩] := by
        simp [seg, List.range'_eq_map_range]
      rw [seg_append σ lo len 1, hx, List.nodup_append]
      refine ⟨ih hle', by simp, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton.mp hb]
      intro hab
      have hpa := (mem_seg σ hle' a).mp ha
      have hposx : (σ.pos (σ.pos.symm ⟨(lo + len) % n, Nat.mod_lt (lo + len) σ.hn⟩)).val =
          lo + len := by
        rw [Equiv.apply_symm_apply]
        exact Nat.mod_eq_of_lt hlt
      have : (σ.pos a).val = lo + len := by rw [hab, hposx]
      omega

/-- The answer permutation really is a permutation: no vertex occurs twice. -/
theorem arrangement_nodup (σ : CircOrder n) : (arrangement σ).Nodup := by
  unfold arrangement
  exact seg_nodup σ (by omega)

/-- **A linearly contiguous set occupies one run of the permutation.**  If `A` is contiguous
for the linear order of the positions (as `linear_contig_of_circle` produces) and nonempty,
then there is a list `m` which occurs as a contiguous run of `arrangement σ` and whose
elements are exactly the members of `A` — namely the segment between the first and the last
position of `A`. -/
theorem isRun_of_linear_contig (σ : CircOrder n) {A : Set (Fin n)}
    (hc : LinearContig σ A) (hne : ∃ v, v ∈ A) :
    ∃ m : List (Fin n), IsRun (arrangement σ) m ∧ (∀ v, v ∈ m ↔ v ∈ A) := by
  classical
  let U : Finset (Fin n) := Finset.univ.filter (fun v => v ∈ A)
  have hUne : U.Nonempty := by
    obtain ⟨v, hv⟩ := hne
    exact ⟨v, by simp [U, hv]⟩
  let S : Finset ℕ := U.image (fun v => (σ.pos v).val)
  have hSne : S.Nonempty := hUne.image (fun v => (σ.pos v).val)
  let lo : ℕ := S.min' hSne
  let hi : ℕ := S.max' hSne + 1
  have hA_iff : ∀ v, v ∈ A ↔ lo ≤ (σ.pos v).val ∧ (σ.pos v).val < hi := by
    intro v
    constructor
    · intro hv
      have hvS : (σ.pos v).val ∈ S := by
        simp [S, U]
        exact ⟨v, hv, rfl⟩
      have hlo : lo ≤ (σ.pos v).val := by
        exact Finset.min'_le S (σ.pos v).val hvS
      have hhi : (σ.pos v).val < hi := by
        have := Finset.le_max' S (σ.pos v).val hvS
        unfold hi
        omega
      exact ⟨hlo, hhi⟩
    · rintro ⟨hlo, hhi⟩
      obtain ⟨a₁, ha₁U, ha₁pos⟩ := Finset.mem_image.mp (Finset.min'_mem S hSne)
      obtain ⟨a₂, ha₂U, ha₂pos⟩ := Finset.mem_image.mp (Finset.max'_mem S hSne)
      have ha₁A : a₁ ∈ A := by simpa [U] using ha₁U
      have ha₂A : a₂ ∈ A := by simpa [U] using ha₂U
      have h1 : (σ.pos a₁).val ≤ (σ.pos v).val := by
        rw [ha₁pos]
        exact hlo
      have h2 : (σ.pos v).val ≤ (σ.pos a₂).val := by
        rw [ha₂pos]
        unfold hi at hhi
        omega
      exact hc ha₁A ha₂A h1 h2
  have hle1 : lo ≤ hi := by
    have := Finset.min'_le S (S.max' hSne) (Finset.max'_mem S hSne)
    unfold hi
    omega
  have hhi_le_n : hi ≤ n := by
    obtain ⟨v, _, hvval⟩ := Finset.mem_image.mp (Finset.max'_mem S hSne)
    have : S.max' hSne < n := by
      rw [← hvval]
      exact (σ.pos v).isLt
    unfold hi
    omega
  refine ⟨seg σ lo (hi - lo), ?_, ?_⟩
  · refine ⟨seg σ 0 lo, seg σ hi (n - hi), ?_⟩
    have h1 : seg σ 0 n = seg σ 0 lo ++ seg σ lo (n - lo) := by
      simpa [show lo + (n - lo) = n by omega] using (seg_append σ 0 lo (n - lo))
    have h2 : seg σ lo (n - lo) = seg σ lo (hi - lo) ++ seg σ hi (n - hi) := by
      simpa [show n - lo = (hi - lo) + (n - hi) by omega,
        show lo + (hi - lo) = hi by omega] using (seg_append σ lo (hi - lo) (n - hi))
    unfold arrangement
    calc
      seg σ 0 n = seg σ 0 lo ++ seg σ lo (n - lo) := h1
      _ = seg σ 0 lo ++ (seg σ lo (hi - lo) ++ seg σ hi (n - hi)) := by rw [h2]
      _ = seg σ 0 lo ++ seg σ lo (hi - lo) ++ seg σ hi (n - hi) := by rw [List.append_assoc]
  · intro v
    rw [mem_seg σ (by omega : lo + (hi - lo) ≤ n) v, show lo + (hi - lo) = hi by omega]
    exact (hA_iff v).symm

/-- **Restricting one run to another.**  If both `L` and `m` are runs of the permutation and
every vertex of `m` lies in `L`, then `m` is a run of `L` as well.  This is how the contiguity
proved for the whole circle is transported down the block-cut tree. -/
theorem isRun_sub_of_runs (σ : CircOrder n) {L m : List (Fin n)}
    (hL : IsRun (arrangement σ) L) (hm : IsRun (arrangement σ) m)
    (hsub : ∀ x ∈ m, x ∈ L) : IsRun L m := by
  obtain ⟨preL, postL, hArrL⟩ := hL
  have hn1 : ((preL ++ L) ++ postL).Nodup := by
    simpa [List.append_assoc] using
      (by simpa [hArrL] using arrangement_nodup σ : (preL ++ L ++ postL).Nodup)
  have hn2 : (preL ++ L).Nodup := (List.nodup_append.mp hn1).1
  have hd_pre := (List.nodup_append.mp hn2).2.2
  have hd_post := (List.nodup_append.mp hn1).2.2
  have hpre : ∀ a ∈ preL, a ∉ m := by
    intro a ha hm'
    exact (hd_pre a ha a (hsub a hm')) rfl
  have hpost : ∀ a ∈ postL, a ∉ m := by
    intro a ha hm'
    exact (hd_post a (List.mem_append.mpr (Or.inr (hsub a hm'))) a ha) rfl
  exact isRun_of_subrun hArrL hm hpre hpost

/-- **A contiguous set of vertices of a run forms a run.**  Combining
`isRun_of_linear_contig` with `isRun_sub_of_runs`: this is the form in which the separation
theory is consumed by the block-cut recursion. -/
theorem isRun_restrict (σ : CircOrder n) {L : List (Fin n)} {A : Set (Fin n)}
    (hL : IsRun (arrangement σ) L) (hsub : ∀ v ∈ A, v ∈ L)
    (hc : LinearContig σ A) (hne : ∃ v, v ∈ A) :
    ∃ m : List (Fin n), IsRun L m ∧ (∀ v, v ∈ m ↔ v ∈ A) := by
  obtain ⟨m, hm, hmA⟩ := isRun_of_linear_contig σ hc hne
  have hsubm : ∀ x ∈ m, x ∈ L := fun x hx => hsub x ((hmA x).mp hx)
  exact ⟨m, isRun_sub_of_runs σ hL hm hsubm, hmA⟩

end Graperm
