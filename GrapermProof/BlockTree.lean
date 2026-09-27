/-
# `GrapermProof.BlockTree`

Claim 2 of the editorial: **the recursive construction on the block-cut tree（圆方树）is
lexicographically optimal.**

We model the rooted block-cut tree of a connected component abstractly:

* `Part.round v cs` — a *round* vertex `v` (a cut vertex, or the root of the component)
  together with the child parts `cs` hanging below it;
* `Part.block cs` — a *square* vertex, i.e. a block, whose non-parent vertices, viewed as
  child parts, are listed in the order in which they occur along the block's outer cycle
  starting from the parent.

The admissibility predicate `Valid` mirrors the recursion with arbitrary legal choices; the
greedy construction `seq` is the concrete lexicographically smallest candidate.  The main
results are

* `Part.seq_valid` — the greedy construction is admissible, and
* `Part.seq_min` — it is below every admissible arrangement.

The optimality step at a round node is the editorial's observation that *only the first
elements need to be compared* (`Dom.sortHead_flatten_le_flatten`), and at a block node it is
the choice between the two outer-cycle directions (`blockChoice`).
-/
import GrapermProof.DomSort
import GrapermProof.SortHead

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Graperm

/-- A node of the rooted block-cut tree.

* `round v cs`: the round vertex `v` with the child parts `cs` below it;
* `block cs`: a block whose child parts are listed in outer-cycle order from its parent. -/
inductive Part (V : Type*) where
  | round : V → List (Part V) → Part V
  | block : List (Part V) → Part V
  deriving Inhabited

namespace Part

variable {V : Type*}

mutual
/-- Admissibility of a family of child parts: one admissible sequence per child, aligned
positionally with the family. -/
def ValidList [Inhabited V] [LinearOrder V] : List (Part V) → List (List V) → Prop
  | [], ms => ms = []
  | c :: rest, ms => ∃ m ms', Valid c m ∧ ValidList rest ms' ∧ ms = m :: ms'

/-- The arrangements that are **admissible** for a part, i.e. those produced by the
block-cut tree recursion with arbitrary legal choices.

* at a round vertex `v`: the admissible sequences of the child parts together with the
  singleton `[v]` may be arranged in **any order** and concatenated — this is the editorial's
  "the vertex `u` may itself be placed anywhere between them";
* at a block: the child parts must be concatenated in outer-cycle order, either **forwards or
  entirely reversed**. -/
def Valid [Inhabited V] [LinearOrder V] : Part V → List V → Prop
  | .round v cs, l =>
      ∃ ms, ValidList cs ms ∧ ∃ T : List (List V), T.Perm (ms ++ [[v]]) ∧ l = T.flatten
  | .block cs, l => (∃ ms, ValidList cs ms ∧ l = ms.flatten) ∨
                    (∃ ms, ValidList cs ms ∧ l = ms.reverse.flatten)
end

variable [Inhabited V] [LinearOrder V]

mutual
/-- The greedy child sequences, one per child part. -/
def seqList : List (Part V) → List (List V)
  | [] => []
  | c :: rest => seq c :: seqList rest

/-- The greedy (lexicographically smallest) arrangement of a part.

* at a round vertex: the child sequences together with the singleton `[v]` are sorted by
  first element and concatenated;
* at a block: the better of the two outer-cycle directions is taken. -/
def seq : Part V → List V
  | .round v cs => (sortHead (seqList cs ++ [[v]])).flatten
  | .block cs => blockChoice (seqList cs)
end

/-- **Sibling separation.**  Distinct parts of a family live on disjoint vertex sets: any two
admissible sequences of distinct siblings share no vertex. -/
def Sep (cs : List (Part V)) : Prop :=
  cs.Pairwise (fun c₁ c₂ => ∀ l₁, Valid c₁ l₁ → ∀ l₂, Valid c₂ l₂ → ∀ x ∈ l₁, x ∉ l₂)

/-- Well-formedness of a rooted block-cut tree.

This records exactly the graph-theoretic facts about the block-cut tree that the greedy
argument uses: distinct child parts live on **pairwise disjoint vertex sets**, and a round
vertex lies in none of its children.  Admissible sequences of distinct siblings therefore
have pairwise distinct first elements — the editorial's remark that "the parts being compared
have disjoint vertex sets, so their first elements cannot coincide". -/
def WF : Part V → Prop
  | .round v cs =>
      (∀ c ∈ cs, WF c) ∧ Sep cs ∧ (∀ c ∈ cs, ∀ l, Valid c l → v ∉ l)
  | .block cs =>
      cs ≠ [] ∧ (∀ c ∈ cs, WF c) ∧ Sep cs

/-! ### The greedy construction unfolds -/

theorem seqList_eq_map (cs : List (Part V)) : seqList cs = cs.map seq := by
  induction cs with
  | nil => rfl
  | cons c t ih => simp only [seqList, List.map_cons, ih]

/-! ### Basic facts about admissibility -/

theorem validList_nil_iff {ms : List (List V)} :
    ValidList ([] : List (Part V)) ms ↔ ms = [] := by
  simp only [ValidList]

theorem validList_cons_iff {c : Part V} {rest : List (Part V)} {ms : List (List V)} :
    ValidList (c :: rest) ms ↔ ∃ m ms', Valid c m ∧ ValidList rest ms' ∧ ms = m :: ms' := by
  simp only [ValidList]

/-- Admissible families are aligned with the child list. -/
theorem ValidList.length_eq {cs : List (Part V)} {ms : List (List V)}
    (h : ValidList cs ms) : ms.length = cs.length := by
  induction cs generalizing ms with
  | nil => simp [validList_nil_iff.mp h]
  | cons c t ih =>
      obtain ⟨m, ms', _, hrest, rfl⟩ := validList_cons_iff.mp h
      simp [ih hrest]

/-- **Distinct siblings have distinct first elements.**  If the child parts of a family have
pairwise disjoint vertex sets, then any list of representatives, one admissible sequence per
child, has pairwise distinct first elements.  This is the editorial's remark made precise. -/
theorem nodup_map_of_disjoint {cs : List (Part V)} {f : Part V → V}
    (hdisj : Sep cs)
    (hf : ∀ c ∈ cs, ∃ l, Valid c l ∧ f c ∈ l) : (cs.map f).Nodup := by
  unfold Sep at hdisj
  induction cs with
  | nil => simp
  | cons a l ih =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hdisj
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih htail (fun c hc => hf c (List.mem_cons_of_mem _ hc))⟩
      intro hfa
      obtain ⟨lf, hlf, hflf⟩ := hf a (List.mem_cons_self ..)
      obtain ⟨c', hc', hfc'⟩ := List.mem_map.mp hfa
      obtain ⟨lf', hlf', hflf'⟩ := hf c' (List.mem_cons_of_mem _ hc')
      exact (hhead c' hc' lf hlf lf' hlf' (f a) hflf) (hfc' ▸ hflf')

/-- `v` never occurs as a first element of an admissible sequence of a sibling of a round
node rooted at `v`. -/
theorem not_mem_map_headV_of_disjoint {cs : List (Part V)} {f : Part V → V} {v : V}
    (huniv : ∀ c ∈ cs, ∀ l, Valid c l → v ∉ l)
    (hf : ∀ c ∈ cs, ∃ l, Valid c l ∧ f c ∈ l) : v ∉ cs.map f := by
  intro hv
  obtain ⟨c, hc, hfc⟩ := List.mem_map.mp hv
  obtain ⟨l, hl, hfl⟩ := hf c hc
  exact (huniv c hc l hl) (hfc ▸ hfl)

/-- Every admissible sequence in a family belongs to some child. -/
theorem ValidList.exists_part {cs : List (Part V)} {ms : List (List V)}
    (h : ValidList cs ms) : ∀ m ∈ ms, ∃ c ∈ cs, Valid c m := by
  induction cs generalizing ms with
  | nil => rw [validList_nil_iff.mp h]; simp
  | cons c t ih =>
      obtain ⟨m₀, ms', hvc, hrest, rfl⟩ := validList_cons_iff.mp h
      intro m hm
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact ⟨c, List.mem_cons_self .., hvc⟩
      · obtain ⟨c', hc', hvc'⟩ := ih hrest m hm'
        exact ⟨c', List.mem_cons_of_mem _ hc', hvc'⟩

/-! ### The greedy construction is admissible and optimal -/

/-- Specification of the greedy construction at a part: it is nonempty, admissible, below
every admissible arrangement, and all admissible arrangements have the same length. -/
def Spec (p : Part V) : Prop :=
  WF p → seq p ≠ [] ∧ Valid p (seq p) ∧
    (∀ l, Valid p l → seq p ≤ l) ∧
    (∀ l, Valid p l → l ≠ []) ∧
    (∀ l₁, Valid p l₁ → ∀ l₂, Valid p l₂ → l₁.length = l₂.length)

theorem list_spec (cs : List (Part V)) :
    (∀ c ∈ cs, Spec c) → (∀ c ∈ cs, WF c) → Sep cs →
    (∀ c ∈ cs, seq c ≠ []) ∧
    ValidList cs (seqList cs) ∧
    (∀ ms, ValidList cs ms → Dom2 (seqList cs) ms) ∧
    (∀ ms, ValidList cs ms → ∀ m ∈ ms, m ≠ []) ∧
    (∀ ms, ValidList cs ms → (ms.map headV).Nodup) ∧
    (∀ ms ms', ValidList cs ms → ValidList cs ms' →
      ms.flatten.length = ms'.flatten.length) := by
  induction cs with
  | nil =>
      intro _ _ _
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro c hc; exact absurd hc (by simp)
      · exact validList_nil_iff.mpr rfl
      · intro ms hms; rw [validList_nil_iff.mp hms]; exact trivial
      · intro ms hms m hm
        rw [validList_nil_iff.mp hms] at hm
        exact absurd hm (by simp)
      · intro ms hms; rw [validList_nil_iff.mp hms]; simp
      · intro ms ms' h1 h2
        simp [validList_nil_iff.mp h1, validList_nil_iff.mp h2]
  | cons c t ih =>
      intro hP hwf hdisj
      unfold Sep at hdisj
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hdisj
      have hPc : Spec c := hP c (List.mem_cons_self ..)
      have hwf_c : WF c := hwf c (List.mem_cons_self ..)
      have hP_t : ∀ c' ∈ t, Spec c' := fun c' hc' => hP c' (List.mem_cons_of_mem _ hc')
      have hwf_t : ∀ c' ∈ t, WF c' := fun c' hc' => hwf c' (List.mem_cons_of_mem _ hc')
      obtain ⟨ih_nil_ne, ih_valid, ih_dom2, ih_ne, ih_nodup, ih_len⟩ := ih hP_t hwf_t htail
      obtain ⟨hc_nil_ne, hc_valid, hc_min, hc_ne, hc_len⟩ := hPc hwf_c
      have hseqlist : seqList (c :: t) = seq c :: seqList t := rfl
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro c' hc'
        rcases List.mem_cons.mp hc' with rfl | hc''
        · exact hc_nil_ne
        · exact ih_nil_ne c' hc''
      · rw [hseqlist]
        exact validList_cons_iff.mpr ⟨seq c, seqList t, hc_valid, ih_valid, rfl⟩
      · intro ms hms
        obtain ⟨m, ms', hvc, hrest, rfl⟩ := validList_cons_iff.mp hms
        rw [hseqlist]
        exact ⟨hc_nil_ne, hc_ne m hvc, hc_min m hvc, headV_le_of_le hc_nil_ne (hc_min m hvc),
          hc_len (seq c) hc_valid m hvc, ih_dom2 ms' hrest⟩
      · intro ms hms m hm
        obtain ⟨m₀, ms', hvc, hrest, rfl⟩ := validList_cons_iff.mp hms
        rcases List.mem_cons.mp hm with heq | hm'
        · rw [heq]; exact hc_ne m₀ hvc
        · exact ih_ne ms' hrest m hm'
      · intro ms hms
        obtain ⟨m₀, ms', hvc, hrest, rfl⟩ := validList_cons_iff.mp hms
        rw [List.map_cons, List.nodup_cons]
        refine ⟨?_, ih_nodup ms' hrest⟩
        intro hm0
        obtain ⟨m', hm', hvm'⟩ := List.mem_map.mp hm0
        obtain ⟨c', hc', hvc'⟩ := ValidList.exists_part hrest m' hm'
        have hm0ne : m₀ ≠ [] := hc_ne m₀ hvc
        have hm'ne : m' ≠ [] := ih_ne ms' hrest m' hm'
        have : headV m₀ ∈ m' := hvm' ▸ headV_mem hm'ne
        exact (hhead c' hc' m₀ hvc m' hvc' (headV m₀) (headV_mem hm0ne)) this
      · intro ms ms' h1 h2
        obtain ⟨m₁, ms₁, hvc1, hrest1, rfl⟩ := validList_cons_iff.mp h1
        obtain ⟨m₂, ms₂, hvc2, hrest2, rfl⟩ := validList_cons_iff.mp h2
        rw [List.flatten_cons, List.flatten_cons, List.length_append, List.length_append,
          hc_len m₁ hvc1 m₂ hvc2, ih_len ms₁ ms₂ hrest1 hrest2]

theorem part_spec (p : Part V) : Spec p :=
  Part.rec (motive_1 := Spec) (motive_2 := fun cs => ∀ c ∈ cs, Spec c)
    (fun v cs ih => by
      intro hwf
      simp only [WF] at hwf
      obtain ⟨h1, h2, h3⟩ := hwf
      obtain ⟨Q_nil_ne, Q_valid, Q_dom2, Q_ne, Q_nodup, Q_len⟩ := list_spec cs ih h1 h2
      let S : List (List V) := seqList cs ++ [[v]]
      have hS : S = seqList cs ++ [[v]] := rfl
      have hseq_def : seq (Part.round v cs) = (sortHead S).flatten := rfl
      have hf : ∀ c ∈ cs, ∃ l, Valid c l ∧ headV (seq c) ∈ l := fun c hc =>
        ⟨seq c, (ih c hc (h1 c hc)).2.1, headV_mem (ih c hc (h1 c hc)).1⟩
      have hnod_seqlist : ((seqList cs).map headV).Nodup := by
        rw [seqList_eq_map, List.map_map]
        exact nodup_map_of_disjoint h2 hf
      have hv_not_seqlist : v ∉ (seqList cs).map headV := by
        rw [seqList_eq_map, List.map_map]
        exact not_mem_map_headV_of_disjoint h3 hf
      have hSne : S ≠ [] := by
        rw [hS]; intro h
        have : ([v] : List V) ∈ seqList cs ++ [[v]] :=
          List.mem_append_right _ (List.mem_singleton_self _)
        rw [h] at this
        simp at this
      have hneS : ∀ x ∈ sortHead S, x ≠ [] := by
        intro x hx
        have hx' : x ∈ S := (sortHead_perm S).mem_iff.mp hx
        rw [hS] at hx'
        rcases List.mem_append.mp hx' with hx'' | hx''
        · rw [seqList_eq_map] at hx''
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx''
          exact Q_nil_ne c hc
        · rw [List.mem_singleton.mp hx'']; simp
      have hndS : (S.map headV).Nodup := by
        have hm : S.map headV = (seqList cs).map headV ++ [v] := by
          rw [hS]; simp [List.map_append, headV_cons]
        rw [hm, List.nodup_append]
        exact ⟨hnod_seqlist, List.nodup_singleton v,
          fun a ha b hb hab => hv_not_seqlist (by
            rw [hab, List.mem_singleton.mp hb] at ha
            exact ha)⟩
      have key : ∀ (ms T : List (List V)), ValidList cs ms → T.Perm (ms ++ [[v]]) →
          (sortHead S).flatten ≤ T.flatten := by
        intro ms T hms hT
        have hdom : Dom (seqList cs) ms := (Q_dom2 ms hms).toDom
        have hdomS : Dom S (ms ++ [[v]]) := by
          rw [hS]
          exact hdom.append [[v]] (fun x hx => by
            rw [List.mem_singleton.mp hx]; exact List.cons_ne_nil v [])
        have hdomT : Dom S T := hdomS.perm_right hT.symm
        have hv_ms : v ∉ ms.map headV := by
          intro hv
          obtain ⟨m, hm, hvm⟩ := List.mem_map.mp hv
          obtain ⟨c, hc, hvc⟩ := ValidList.exists_part hms m hm
          exact (h3 c hc m hvc) (hvm ▸ headV_mem (Q_ne ms hms m hm))
        have hndT : (T.map headV).Nodup := by
          refine (hT.map headV).nodup_iff.mpr ?_
          have hm : (ms ++ [[v]]).map headV = ms.map headV ++ [v] := by
            simp [List.map_append, headV_cons]
          rw [hm, List.nodup_append]
          exact ⟨Q_nodup ms hms, List.nodup_singleton v,
            fun a ha b hb hab => hv_ms (by
              rw [hab, List.mem_singleton.mp hb] at ha
              exact ha)⟩
        have hneT : ∀ x ∈ T, x ≠ [] := by
          intro x hx
          have hx' : x ∈ ms ++ [[v]] := hT.mem_iff.mp hx
          rcases List.mem_append.mp hx' with hx'' | hx''
          · exact Q_ne ms hms x hx''
          · rw [List.mem_singleton.mp hx'']; simp
        exact Dom.sortHead_flatten_le_flatten hdomT hndS hneT hndT
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hseq_def]
        exact flatten_ne_nil (sortHead_ne_nil hSne) hneS
      · rw [hseq_def]
        refine ⟨seqList cs, Q_valid, sortHead S, ?_, rfl⟩
        show (sortHead S).Perm S
        exact sortHead_perm S
      · rw [hseq_def]
        intro l hl
        obtain ⟨ms, hms, T, hT, rfl⟩ := hl
        exact key ms T hms hT
      · intro l hl
        obtain ⟨ms, hms, T, hT, rfl⟩ := hl
        intro hf
        rw [List.flatten_eq_nil_iff] at hf
        have hm : ([v] : List V) ∈ T :=
          hT.mem_iff.mpr (List.mem_append_right _ (List.mem_singleton_self _))
        exact absurd (hf [v] hm) (List.cons_ne_nil v [])
      · intro l₁ hl₁ l₂ hl₂
        obtain ⟨ms₁, hms₁, T₁, hT₁, rfl⟩ := hl₁
        obtain ⟨ms₂, hms₂, T₂, hT₂, rfl⟩ := hl₂
        have e1 : T₁.flatten.length = ms₁.flatten.length + 1 := by
          rw [(hT₁.flatten).length_eq]
          simp [List.flatten_append]
        have e2 : T₂.flatten.length = ms₂.flatten.length + 1 := by
          rw [(hT₂.flatten).length_eq]
          simp [List.flatten_append]
        rw [e1, e2, Q_len ms₁ ms₂ hms₁ hms₂]
    )
    (fun cs ih => by
      intro hwf
      simp only [WF] at hwf
      obtain ⟨hne, h1, h2⟩ := hwf
      obtain ⟨Q_nil_ne, Q_valid, Q_dom2, Q_ne, Q_nodup, Q_len⟩ := list_spec cs ih h1 h2
      have hss_ne : seqList cs ≠ [] := by
        rw [seqList_eq_map]
        intro h
        exact hne (List.map_eq_nil_iff.mp h)
      have hne_ss : ∀ x ∈ seqList cs, x ≠ [] := by
        rw [seqList_eq_map]; intro x hx
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
        exact Q_nil_ne c hc
      have hfwd_ne : (seqList cs).flatten ≠ [] := flatten_ne_nil hss_ne hne_ss
      have hrev_ne : (seqList cs).reverse.flatten ≠ [] :=
        flatten_ne_nil (by intro h; exact hss_ne (by simpa using congrArg List.reverse h))
          (by intro x hx; rw [List.mem_reverse] at hx; exact hne_ss x hx)
      have ms_ne_nil : ∀ ms, ValidList cs ms → ms ≠ [] := by
        intro ms hms h
        have hlen : ms.length = cs.length := ValidList.length_eq hms
        rw [h, List.length_nil] at hlen
        exact hne (List.length_eq_zero_iff.mp hlen.symm)
      have rev_len : ∀ ms : List (List V), ms.reverse.flatten.length = ms.flatten.length := by
        intro ms
        rw [List.length_flatten, List.length_flatten, List.map_reverse, List.sum_reverse]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · show blockChoice (seqList cs) ≠ []
        unfold blockChoice
        split
        · exact hrev_ne
        · exact hfwd_ne
      · show Valid (Part.block cs) (blockChoice (seqList cs))
        unfold blockChoice
        split
        · exact Or.inr ⟨seqList cs, Q_valid, rfl⟩
        · exact Or.inl ⟨seqList cs, Q_valid, rfl⟩
      · intro l hl
        change blockChoice (seqList cs) ≤ l
        rcases hl with ⟨ms, hms, rfl⟩ | ⟨ms, hms, rfl⟩
        · exact le_trans (blockChoice_le_forward (seqList cs)) (Dom2.flatten_le (Q_dom2 ms hms))
        · exact le_trans (blockChoice_le_reverse (seqList cs))
            (Dom2.flatten_le ((Q_dom2 ms hms).reverse))
      · intro l hl
        rcases hl with ⟨ms, hms, rfl⟩ | ⟨ms, hms, rfl⟩
        · exact flatten_ne_nil (ms_ne_nil ms hms) (Q_ne ms hms)
        · refine flatten_ne_nil ?_ (by
            intro x hx; rw [List.mem_reverse] at hx; exact Q_ne ms hms x hx)
          intro h
          exact ms_ne_nil ms hms (by simpa using congrArg List.reverse h)
      · intro l₁ hl₁ l₂ hl₂
        rcases hl₁ with ⟨ms₁, hms₁, hfl1⟩ | ⟨ms₁, hms₁, hfl1⟩
        · rcases hl₂ with ⟨ms₂, hms₂, hfl2⟩ | ⟨ms₂, hms₂, hfl2⟩
          · rw [hfl1, hfl2]; exact Q_len ms₁ ms₂ hms₁ hms₂
          · rw [hfl1, hfl2, rev_len]; exact Q_len ms₁ ms₂ hms₁ hms₂
        · rcases hl₂ with ⟨ms₂, hms₂, hfl2⟩ | ⟨ms₂, hms₂, hfl2⟩
          · rw [hfl1, hfl2, rev_len]; exact Q_len ms₁ ms₂ hms₁ hms₂
          · rw [hfl1, hfl2, rev_len, rev_len]; exact Q_len ms₁ ms₂ hms₁ hms₂
    )
    (fun c hc => absurd hc (by simp))
    (fun head tail ihh iht => by
      intro c hc
      rcases List.mem_cons.mp hc with heq | hc'
      · rw [heq]; exact ihh
      · exact iht c hc')
    p

/-! ### Claim 2: the recursive construction is admissible and lexicographically optimal -/

/-- The greedy construction at a part is **nonempty** when the tree is well formed. -/
theorem seq_nonempty {p : Part V} (hwf : WF p) : seq p ≠ [] := (part_spec p hwf).1

/-- The greedy construction is **admissible**: it is one of the arrangements generated by the
block-cut tree recursion. -/
theorem seq_valid {p : Part V} (hwf : WF p) : Valid p (seq p) := (part_spec p hwf).2.1

/-- **Claim 2 (lexicographic optimality).**  For a well-formed rooted block-cut tree, every
admissible arrangement is lexicographically at least the greedy recursive construction: at a
round node the child sequences together with the vertex itself are sorted by first element and
concatenated, and at a block node the better of the two outer-cycle directions is taken. -/
theorem seq_min {p : Part V} (hwf : WF p) {l : List V} (hl : Valid p l) : seq p ≤ l :=
  (part_spec p hwf).2.2.1 l hl

/-- Every admissible arrangement of a part has the same length (the number of vertices in the
subtree). -/
theorem Valid.length_eq {p : Part V} (hwf : WF p) {l₁ l₂ : List V}
    (h₁ : Valid p l₁) (h₂ : Valid p l₂) : l₁.length = l₂.length :=
  (part_spec p hwf).2.2.2.2 l₁ h₁ l₂ h₂

end Part

end Graperm
