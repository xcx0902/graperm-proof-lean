/-
# `GrapermProof.Consists`

The last link of Claim 2: turning the **geometric** information produced by
`Separation` / `Arrange` (every subtree of the block-cut tree occupies one contiguous
interval of the answer permutation) into the **combinatorial** notion of admissibility
`Part.Valid` used by `BlockTree`.

The interface is a predicate `Consists σ p L`, which says that the list `L` is a listing of the
vertices of `p` in which

* every child of `p` occupies one contiguous **run** of `L`,
* distinct children are disjoint, and — at a round node — none of them contains the node's own
  vertex, and
* at a block node the runs occur in the outer-cycle order, forwards or backwards.

Two theorems are proved:

* `valid_of_consists` — a consistent listing is **admissible** (`Part.Valid`).  This is where
  the merging lemma `merge_runs` is used: the runs can be concatenated in *some* order, and
  `Part.Valid` allows exactly those orders.
* `consists_of_geometry` — the geometry really does give a consistent listing, provided every
  subtree is contiguous on the circle (`AllContig`) and the tree is structurally sound
  (`GeoWF`).
-/
import GrapermProof.Assemble
import GrapermProof.BlockTree

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace Graperm

/-! ### Vertices of a part -/

variable {V : Type*}

mutual
/-- The vertices below a family of parts. -/
def partVertsList : List (Part V) → List V
  | [] => []
  | c :: rest => partVerts c ++ partVertsList rest

/-- The vertices of a part, listed in the canonical (recursive) order. -/
def partVerts : Part V → List V
  | .round v cs => v :: partVertsList cs
  | .block cs => partVertsList cs
end

/-- The vertices of a child are vertices of the family. -/
theorem mem_partVertsList_of_mem {c : Part V} {cs : List (Part V)} (hc : c ∈ cs) :
    ∀ {x : V}, x ∈ partVerts c → x ∈ partVertsList cs := by
  induction cs with
  | nil => intro x hx; simp at hc
  | cons d t ih =>
      intro x hx
      simp at hc
      rcases hc with rfl | hc'
      · simp [partVertsList, hx]
      · simp [partVertsList, ih hc' hx]

/-- Conversely: a vertex of a family belongs to one of its members. -/
theorem exists_part_of_mem_partVertsList {cs : List (Part V)} :
    ∀ {x : V}, x ∈ partVertsList cs → ∃ c ∈ cs, x ∈ partVerts c := by
  induction cs with
  | nil => intro x hx; simp [partVertsList] at hx
  | cons d t ih =>
      intro x hx
      simp [partVertsList] at hx
      rcases hx with hx | hx
      · exact ⟨d, by simp, hx⟩
      · obtain ⟨c, hc, hxc⟩ := ih hx
        exact ⟨c, by simp [hc], hxc⟩

/-- A vertex of a child of a round node is a vertex of the round node. -/
theorem mem_partVerts_round_of_child {v : V} {cs : List (Part V)} {c : Part V} (hc : c ∈ cs) :
    ∀ {x : V}, x ∈ partVerts c → x ∈ partVerts (.round v cs : Part V) := by
  intro x hx
  simp [partVerts, mem_partVertsList_of_mem hc hx]

/-- A vertex of a child of a block node is a vertex of the block node. -/
theorem mem_partVerts_block_of_child {cs : List (Part V)} {c : Part V} (hc : c ∈ cs) :
    ∀ {x : V}, x ∈ partVerts c → x ∈ partVerts (.block cs : Part V) := by
  intro x hx
  simp [partVerts, mem_partVertsList_of_mem hc hx]

/-- Distinct parts of a family live on disjoint vertex sets. -/
def partDisjoint (cs : List (Part V)) : Prop :=
  cs.Pairwise (fun c₁ c₂ => ListDisj (partVerts c₁) (partVerts c₂))

/-- The vertex `v` lies in none of the parts `cs`. -/
def partExcludes (v : V) (cs : List (Part V)) : Prop :=
  ∀ c ∈ cs, v ∉ partVerts c

/-! ### Consistency -/

variable {n : ℕ}

mutual
/-- A whole family of parts is consistent: one sequence per child, in the same order. -/
def ConsistsList (σ : CircOrder n) : List (Part (Fin n)) → List (List (Fin n)) → Prop
  | [], ms => ms = []
  | c :: rest, ms => ∃ m ms', Consists σ c m ∧ ConsistsList σ rest ms' ∧ ms = m :: ms'

/-- **`p` is consistent with `L`.**  `L` is a repetition-free listing of the vertices of `p`
in which every child occupies one contiguous run, distinct children are disjoint, and — at a
round node — the node's own vertex `v` lies in none of the children and together with them
exhausts `L`.  At a block node the runs must occur in the outer-cycle order, forwards or
entirely reversed; that is the one place where Claim 1 is used. -/
def Consists (σ : CircOrder n) : Part (Fin n) → List (Fin n) → Prop
  | .round v cs, L =>
      ∃ ms, ConsistsList σ cs ms ∧
        L.Nodup ∧
        (∀ m ∈ ms, IsRun L m) ∧
        (∀ b₁ ∈ ms, ∀ b₂ ∈ ms, b₁ ≠ b₂ → ListDisj b₁ b₂) ∧
        (∀ b ∈ ms, v ∉ b) ∧
        ms.Nodup ∧
        v ∈ L ∧
        (∀ x ∈ L, x = v ∨ ∃ b ∈ ms, x ∈ b)
  | .block cs, L =>
      ∃ ms, ConsistsList σ cs ms ∧
        L.Nodup ∧
        (∀ m ∈ ms, IsRun L m) ∧
        (∀ b₁ ∈ ms, ∀ b₂ ∈ ms, b₁ ≠ b₂ → ListDisj b₁ b₂) ∧
        ms.Nodup ∧
        (L = ms.flatten ∨ L = ms.reverse.flatten)
end

/-- Every sequence of a consistent family comes from some child. -/
theorem ConsistsList.exists_part {σ : CircOrder n} {cs : List (Part (Fin n))}
    {ms : List (List (Fin n))} (h : ConsistsList σ cs ms) :
    ∀ m ∈ ms, ∃ c ∈ cs, Consists σ c m := by
  induction cs generalizing ms with
  | nil =>
      intro m hm
      have : ms = [] := by simpa [ConsistsList] using h
      rw [this] at hm
      simp at hm
  | cons d t ih =>
      intro m hm
      simp only [ConsistsList] at h
      obtain ⟨m₀, ms', hc, hrest, rfl⟩ := h
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact ⟨d, by simp, hc⟩
      · obtain ⟨c', hc', hv⟩ := ih hrest m hm'
        exact ⟨c', by simp [hc'], hv⟩

/-- The vertex listing of a consistent part is repetition free. -/
theorem nodup_of_consists {σ : CircOrder n} {p : Part (Fin n)} {L : List (Fin n)}
    (h : Consists σ p L) : L.Nodup := by
  cases p with
  | round v cs =>
      simp only [Consists] at h
      obtain ⟨ms, hms, hLnod, hrun, hdisj, hvnot, hmsnod, hvL, hcov⟩ := h
      exact hLnod
  | block cs =>
      simp only [Consists] at h
      obtain ⟨ms, hms, hLnod, hrun, hdisj, hmsnod, horder⟩ := h
      exact hLnod

/-! ### Consistency implies admissibility -/

/-- **Assembly.**  Every consistent listing of a part is admissible for it, i.e. it is one of
the arrangements that the block-cut recursion may produce.  Together with `Part.seq_min` this
shows that the greedy construction is at most as large as *any* arrangement coming from a
non-crossing circular order. -/
theorem valid_of_consists (σ : CircOrder n) [NeZero n] (p : Part (Fin n)) :
    ∀ {L : List (Fin n)}, Consists σ p L → Part.Valid p L := by
  classical
  exact Part.rec
    (motive_1 := fun p => ∀ {L : List (Fin n)}, Consists σ p L → Part.Valid p L)
    (motive_2 := fun cs => ∀ (ms : List (List (Fin n))),
      ConsistsList σ cs ms → Part.ValidList cs ms)
    (fun v cs ih => by
      intro L h
      simp only [Consists] at h
      obtain ⟨ms, hms, hLnod, hrun, hdisj, hvnot, hmsnod, hvL, hcov⟩ := h
      have hVms : Part.ValidList cs ms := ih ms hms
      let bs : List (List (Fin n)) := ms ++ [[v]]
      have hv_not_ms : ([v] : List (Fin n)) ∉ ms := by
        intro hm
        exact hvnot [v] hm (by simp)
      have hbsnod : bs.Nodup := by
        rw [List.nodup_append]
        refine ⟨hmsnod, by simp, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton.mp hb]
        intro heq
        exact hv_not_ms (by rw [← heq]; exact ha)
      have hrun_bs : ∀ b ∈ bs, IsRun L b := by
        intro b hb
        rcases List.mem_append.mp hb with hb' | hb'
        · exact hrun b hb'
        · rw [List.mem_singleton.mp hb']
          obtain ⟨pre, post, hL⟩ := list_mem_split hvL
          exact ⟨pre, post, by simpa using hL⟩
      have hdisj_bs : ∀ b₁ ∈ bs, ∀ b₂ ∈ bs, b₁ ≠ b₂ → ListDisj b₁ b₂ := by
        intro b₁ hb₁ b₂ hb₂ hne
        rcases List.mem_append.mp hb₁ with h₁ | h₁
        · rcases List.mem_append.mp hb₂ with h₂ | h₂
          · exact hdisj b₁ h₁ b₂ h₂ hne
          · have hb₂eq : b₂ = [v] := List.mem_singleton.mp h₂
            rw [hb₂eq]
            intro x hx hxv
            rw [List.mem_singleton.mp hxv] at hx
            exact hvnot b₁ h₁ hx
        · have hb₁eq : b₁ = [v] := List.mem_singleton.mp h₁
          rcases List.mem_append.mp hb₂ with h₂ | h₂
          · rw [hb₁eq]
            intro x hxv hx
            rw [List.mem_singleton.mp hxv] at hx
            exact hvnot b₂ h₂ hx
          · have hb₂eq : b₂ = [v] := List.mem_singleton.mp h₂
            exfalso
            exact hne (hb₁eq.trans hb₂eq.symm)
      have hcov_bs : ∀ x ∈ L, ∃ b ∈ bs, x ∈ b := by
        intro x hx
        rcases hcov x hx with hxv | ⟨b, hb, hxb⟩
        · refine ⟨[v], List.mem_append.mpr (Or.inr (by simp)), ?_⟩
          simpa [hxv]
        · exact ⟨b, List.mem_append.mpr (Or.inl hb), hxb⟩
      obtain ⟨T, hTperm, hTflat⟩ := merge_runs bs L hLnod hrun_bs hdisj_bs hcov_bs hbsnod
      exact ⟨ms, hVms, T, by simpa [bs] using hTperm, hTflat⟩)
    (fun cs ih => by
      intro L h
      simp only [Consists] at h
      obtain ⟨ms, hms, hLnod, hrun, hdisj, hmsnod, horder⟩ := h
      have hVms : Part.ValidList cs ms := ih ms hms
      rcases horder with hf | hr
      · exact Or.inl ⟨ms, hVms, hf⟩
      · exact Or.inr ⟨ms, hVms, hr⟩)
    (by
      intro ms h
      have : ms = [] := by simpa [ConsistsList] using h
      exact Part.validList_nil_iff.mpr this)
    (by
      intro head tail ihh iht ms h
      simp only [ConsistsList] at h
      obtain ⟨m, ms', hc, hrest, rfl⟩ := h
      exact Part.validList_cons_iff.mpr ⟨m, ms', ihh hc, iht ms' hrest, rfl⟩)
    p

/-! ### The geometry produces a consistent listing -/

/-- A nonempty list has an element. -/
theorem nonempty_of_ne_nil {cs : List (Part (Fin n))}
    (h : ∀ c ∈ cs, partVerts c ≠ []) : ∀ c ∈ cs, ∃ x, x ∈ partVerts c := by
  intro c hc
  cases hmem : partVerts c with
  | nil => exact False.elim (h c hc hmem)
  | cons x t => exact ⟨x, by simp⟩

/-- Disjointness of lists is symmetric. -/
theorem listDisj_symm {l₁ l₂ : List (Fin n)} (h : ListDisj l₁ l₂) : ListDisj l₂ l₁ := by
  intro x hx₂ hx₁
  exact h x hx₁ hx₂

/-- Structural soundness of a part tree: the children of a node have pairwise disjoint,
nonempty vertex sets, and a round vertex lies in none of its children. -/
def GeoWF : Part (Fin n) → Prop
  | .round v cs =>
      (∀ c ∈ cs, GeoWF c) ∧ partDisjoint cs ∧ partExcludes v cs ∧
        (∀ c ∈ cs, partVerts c ≠ [])
  | .block cs =>
      (∀ c ∈ cs, GeoWF c) ∧ partDisjoint cs ∧ (∀ c ∈ cs, partVerts c ≠ [])

/-- Every subtree occupies a contiguous set of positions on the circle.  This is what
`circle_contiguous_of_connected_complement` and `linear_contig_of_circle` deliver. -/
def AllContig (σ : CircOrder n) : Part (Fin n) → Prop
  | .round v cs =>
      LinearContig σ {x | x ∈ partVerts (.round v cs : Part (Fin n))} ∧
        (∀ c ∈ cs, AllContig σ c)
  | .block cs =>
      LinearContig σ {x | x ∈ partVerts (.block cs : Part (Fin n))} ∧
        (∀ c ∈ cs, AllContig σ c)

/-- The contiguity of a part itself. -/
theorem contig_of_allContig {σ : CircOrder n} {p : Part (Fin n)} (h : AllContig σ p) :
    LinearContig σ {x | x ∈ partVerts p} := by
  cases p with
  | round v cs =>
      simp only [AllContig] at h
      exact h.1
  | block cs =>
      simp only [AllContig] at h
      exact h.1

/-- **Alignment.**  The runs `ms` are listed in the same order as the parts `cs`, and the `i`-th
run lists exactly the vertices of the `i`-th part.  This is what ties the combinatorial
decomposition back to the order in which the block-cut tree stores its children. -/
def Aligned : List (Part (Fin n)) → List (List (Fin n)) → Prop
  | [], [] => True
  | c :: cs, m :: ms => (∀ x, x ∈ m ↔ x ∈ partVerts c) ∧ Aligned cs ms
  | _, _ => False

/-- Every run of an aligned family comes from a part of the family. -/
theorem aligned_imp_right {cs : List (Part (Fin n))} {ms : List (List (Fin n))}
    (h : Aligned cs ms) :
    ∀ m ∈ ms, ∃ c ∈ cs, ∀ x, x ∈ m ↔ x ∈ partVerts c := by
  induction cs generalizing ms with
  | nil =>
      intro m hm
      cases ms with
      | nil => simp at hm
      | cons m' ms' => simp [Aligned] at h
  | cons c cs' ih =>
      intro m hm
      cases ms with
      | nil => simp [Aligned] at h
      | cons m' ms' =>
          simp only [Aligned] at h
          rcases List.mem_cons.mp hm with rfl | hm'
          · exact ⟨c, by simp, h.1⟩
          · obtain ⟨c', hc', hv⟩ := ih h.2 m hm'
            exact ⟨c', by simp [hc'], hv⟩

/-- Every part of an aligned family has a corresponding run. -/
theorem aligned_imp_left {cs : List (Part (Fin n))} {ms : List (List (Fin n))}
    (h : Aligned cs ms) :
    ∀ c ∈ cs, ∃ m ∈ ms, ∀ x, x ∈ m ↔ x ∈ partVerts c := by
  induction cs generalizing ms with
  | nil =>
      intro c hc
      simp at hc
  | cons c cs' ih =>
      intro d hd
      cases ms with
      | nil => simp [Aligned] at h
      | cons m' ms' =>
          simp only [Aligned] at h
          rcases List.mem_cons.mp hd with rfl | hd'
          · exact ⟨m', by simp, h.1⟩
          · obtain ⟨m'', hm'', hv⟩ := ih h.2 d hd'
            exact ⟨m'', by simp [hm''], hv⟩

/-- Alignment is preserved by appending one further pair. -/
theorem aligned_snoc {cs : List (Part (Fin n))} {ms : List (List (Fin n))}
    (h : Aligned cs ms) {c : Part (Fin n)} {m : List (Fin n)}
    (hm : ∀ x, x ∈ m ↔ x ∈ partVerts c) :
    Aligned (cs ++ [c]) (ms ++ [m]) := by
  induction cs generalizing ms with
  | nil =>
      cases ms with
      | nil => simp [Aligned, hm]
      | cons m' ms' => simp [Aligned] at h
  | cons c' cs' ih =>
      cases ms with
      | nil => simp [Aligned] at h
      | cons m' ms' =>
          simp only [Aligned] at h ⊢
          exact ⟨h.1, ih h.2⟩

/-- Alignment is preserved by reversing both lists. -/
theorem aligned_reverse {cs : List (Part (Fin n))} {ms : List (List (Fin n))}
    (h : Aligned cs ms) : Aligned cs.reverse ms.reverse := by
  induction cs generalizing ms with
  | nil =>
      cases ms with
      | nil => simp [Aligned]
      | cons m' ms' => simp [Aligned] at h
  | cons c cs' ih =>
      cases ms with
      | nil => simp [Aligned] at h
      | cons m' ms' =>
          simp only [Aligned] at h
          simpa using (aligned_snoc (ih h.2) h.1)

/-- What the recursive construction of the child sequences must deliver: a sequence per child
which is a run of `L`, repetition-free, pairwise disjoint from the others, and listing exactly
the vertices of its child (in both directions). -/
def ChildData (σ : CircOrder n) (cs : List (Part (Fin n))) (L : List (Fin n))
    (ms : List (List (Fin n))) : Prop :=
  ConsistsList σ cs ms ∧
    (∀ m ∈ ms, IsRun L m) ∧
    (∀ m ∈ ms, m.Nodup) ∧
    (∀ b₁ ∈ ms, ∀ b₂ ∈ ms, b₁ ≠ b₂ → ListDisj b₁ b₂) ∧
    ms.Nodup ∧
    (∀ c ∈ cs, ∃ m ∈ ms, ∀ x, x ∈ m ↔ x ∈ partVerts c) ∧
    (∀ m ∈ ms, ∃ c ∈ cs, ∀ x, x ∈ m ↔ x ∈ partVerts c) ∧
    (∀ m ∈ ms, m ≠ []) ∧
    Aligned cs ms

/-- **The outer-cycle order condition** (Claim 1, subset form).  At every block node the answer
visits the children in the order in which they occur along the block's outer cycle, either
forwards or entirely reversed.  This is the single place where Claim 1 enters the completeness
direction of Claim 2; it is isolated here as a hypothesis so that everything else is
independent of it. -/
def GeoOrder (σ : CircOrder n) : Part (Fin n) → Prop
  | .round v cs => ∀ c ∈ cs, GeoOrder σ c
  | .block cs =>
      (∀ c ∈ cs, GeoOrder σ c) ∧
        (∀ {L : List (Fin n)}, IsRun (arrangement σ) L →
          (∀ x, x ∈ L ↔ x ∈ partVerts (.block cs : Part (Fin n))) →
          ∀ ms : List (List (Fin n)), ChildData σ cs L ms →
            L = ms.flatten ∨ L = ms.reverse.flatten)

/-- **From geometry to consistency.**  If the part tree is structurally sound (`GeoWF`), every
subtree is contiguous on the circle (`AllContig`) and the block nodes respect the outer-cycle
order (`GeoOrder`), then the run `L` of the answer permutation that lists the vertices of `p`
is consistent with `p`. -/
theorem consists_of_geometry (σ : CircOrder n) [NeZero n] (p : Part (Fin n))
    (hwf : GeoWF p) (hc : AllContig σ p) (ho : GeoOrder σ p) :
    ∀ {L : List (Fin n)}, IsRun (arrangement σ) L →
      (∀ x, x ∈ L ↔ x ∈ partVerts p) → Consists σ p L := by
  classical
  exact Part.rec
    (motive_1 := fun p => GeoWF p → AllContig σ p → GeoOrder σ p →
      ∀ {L : List (Fin n)}, IsRun (arrangement σ) L →
        (∀ x, x ∈ L ↔ x ∈ partVerts p) → Consists σ p L)
    (motive_2 := fun cs => partDisjoint cs → (∀ c ∈ cs, GeoWF c) →
      (∀ c ∈ cs, AllContig σ c) → (∀ c ∈ cs, GeoOrder σ c) →
      ∀ {L : List (Fin n)}, IsRun (arrangement σ) L →
        (∀ c ∈ cs, ∀ x, x ∈ partVerts c → x ∈ L) →
        (∀ c ∈ cs, ∃ x, x ∈ partVerts c) →
        ∃ ms, ChildData σ cs L ms)
    (fun v cs ih => by
      intro hwf hc ho L hLrun hverts
      simp only [GeoWF] at hwf
      obtain ⟨hwf_ch, hdisj, hexcl, hne_ch⟩ := hwf
      simp only [GeoOrder] at ho
      simp only [AllContig] at hc
      obtain ⟨ms, hcd⟩ := ih hdisj hwf_ch hc.2 ho hLrun
        (fun c hc' x hx => (hverts x).mpr (mem_partVerts_round_of_child hc' hx))
        (nonempty_of_ne_nil hne_ch)
      obtain ⟨hms, hrun, hnod, hdisjM, hmsnod, hal₁, hal₂, hne, halign⟩ := hcd
      have hLnod : L.Nodup := nodup_of_isRun (arrangement_nodup σ) hLrun
      have hvL : v ∈ L := (hverts v).mpr (by simp [partVerts])
      have hcov : ∀ x ∈ L, x = v ∨ ∃ b ∈ ms, x ∈ b := by
        intro x hx
        have hxv : x ∈ partVerts (.round v cs : Part (Fin n)) := (hverts x).mp hx
        simp [partVerts] at hxv
        rcases hxv with rfl | hxv'
        · exact Or.inl rfl
        · obtain ⟨c, hc', hxc⟩ := exists_part_of_mem_partVertsList (cs := cs) hxv'
          obtain ⟨b, hb, hbv⟩ := hal₁ c hc'
          exact Or.inr ⟨b, hb, (hbv x).mpr hxc⟩
      have hvnot : ∀ b ∈ ms, v ∉ b := by
        intro b hb hvb
        obtain ⟨c, hc', hbc⟩ := hal₂ b hb
        exact (hexcl c hc') ((hbc v).mp hvb)
      simp only [Consists]
      exact ⟨ms, hms, hLnod, hrun, hdisjM, hvnot, hmsnod, hvL, hcov⟩)
    (fun cs ih => by
      intro hwf hc ho L hLrun hverts
      simp only [GeoWF] at hwf
      obtain ⟨hwf_ch, hdisj, hne_ch⟩ := hwf
      simp only [GeoOrder] at ho
      simp only [AllContig] at hc
      obtain ⟨ms, hcd⟩ := ih hdisj hwf_ch hc.2 ho.1 hLrun
        (fun c hc' x hx => (hverts x).mpr (mem_partVerts_block_of_child hc' hx))
        (nonempty_of_ne_nil hne_ch)
      have horder : L = ms.flatten ∨ L = ms.reverse.flatten := ho.2 hLrun hverts ms hcd
      obtain ⟨hms, hrun, hnod, hdisjM, hmsnod, hal₁, hal₂, hne, halign⟩ := hcd
      have hLnod : L.Nodup := nodup_of_isRun (arrangement_nodup σ) hLrun
      simp only [Consists]
      exact ⟨ms, hms, hLnod, hrun, hdisjM, hmsnod, horder⟩)
    (by
      intro hd hwf hc ho L hLrun hsub hne
      exact ⟨[], by simp [ChildData, ConsistsList, Aligned]⟩)
    (by
      intro head tail ihh iht hd hwf hc ho L hLrun hsub hne
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hd
      have hLnod : L.Nodup := nodup_of_isRun (arrangement_nodup σ) hLrun
      have hne_head : ∃ x, x ∈ partVerts head := hne head (by simp)
      have hsub_head : ∀ x ∈ ({x | x ∈ partVerts head} : Set (Fin n)), x ∈ L :=
        fun x hx => hsub head (by simp) x hx
      have hcont_head : LinearContig σ {x | x ∈ partVerts head} :=
        contig_of_allContig (hc head (by simp))
      obtain ⟨m, hmrun, hmverts⟩ := isRun_restrict σ hLrun hsub_head hcont_head hne_head
      have hmrunArr : IsRun (arrangement σ) m := isRun_trans hLrun hmrun
      have hm_nod : m.Nodup := nodup_of_isRun hLnod hmrun
      have hcons_head : Consists σ head m :=
        ihh (hwf head (by simp)) (hc head (by simp)) (ho head (by simp)) hmrunArr hmverts
      obtain ⟨ms_t, hcd_t⟩ := iht htail
        (fun c hc' => hwf c (List.mem_cons_of_mem head hc'))
        (fun c hc' => hc c (List.mem_cons_of_mem head hc'))
        (fun c hc' => ho c (List.mem_cons_of_mem head hc')) hLrun
        (fun c hc' => hsub c (List.mem_cons_of_mem head hc'))
        (fun c hc' => hne c (List.mem_cons_of_mem head hc'))
      obtain ⟨hms_t, hrun_t, hnod_t, hdisj_t, hnodms_t, hal₁_t, hal₂_t, hne_t, halign_t⟩ := hcd_t
      let ms : List (List (Fin n)) := m :: ms_t
      have hm_not_ms_t : m ∉ ms_t := by
        intro hmt
        obtain ⟨c', hc', hmc'⟩ := hal₂_t m hmt
        obtain ⟨x, hx⟩ := hne_head
        exact (hhead c' hc' x hx) ((hmc' x).mp ((hmverts x).mpr hx))
      have hdisj_ms : ∀ b₁ ∈ ms, ∀ b₂ ∈ ms, b₁ ≠ b₂ → ListDisj b₁ b₂ := by
        intro b₁ hb₁ b₂ hb₂ hne'
        rcases List.mem_cons.mp hb₁ with hb₁' | hb₁'
        · subst b₁
          rcases List.mem_cons.mp hb₂ with hb₂' | hb₂'
          · subst b₂
            exact False.elim (hne' rfl)
          · obtain ⟨c', hc', hmc'⟩ := hal₂_t b₂ hb₂'
            intro x hx hx'
            exact (hhead c' hc' x ((hmverts x).mp hx)) ((hmc' x).mp hx')
        · rcases List.mem_cons.mp hb₂ with hb₂' | hb₂'
          · subst b₂
            obtain ⟨c', hc', hmc'⟩ := hal₂_t b₁ hb₁'
            intro x hx hx'
            exact (listDisj_symm (hhead c' hc') x ((hmc' x).mp hx)) ((hmverts x).mp hx')
          · exact hdisj_t b₁ hb₁' b₂ hb₂' hne'
      have hnod_ms : ms.Nodup := by
        rw [List.nodup_cons]
        exact ⟨hm_not_ms_t, hnodms_t⟩
      have hal₁ : ∀ c ∈ head :: tail, ∃ m' ∈ ms, ∀ x, x ∈ m' ↔ x ∈ partVerts c := by
        intro c hc'
        rcases List.mem_cons.mp hc' with rfl | hc''
        · exact ⟨m, by simp [ms], hmverts⟩
        · obtain ⟨m', hm', hm'v⟩ := hal₁_t c hc''
          exact ⟨m', List.mem_cons_of_mem m hm', hm'v⟩
      have hal₂ : ∀ m' ∈ ms, ∃ c ∈ head :: tail, ∀ x, x ∈ m' ↔ x ∈ partVerts c := by
        intro m' hm'
        rcases List.mem_cons.mp hm' with rfl | hm''
        · exact ⟨head, by simp, hmverts⟩
        · obtain ⟨c, hc', hm'v⟩ := hal₂_t m' hm''
          exact ⟨c, List.mem_cons_of_mem head hc', hm'v⟩
      have hne_m : m ≠ [] := by
        intro hnil
        obtain ⟨x, hx⟩ := hne_head
        have : x ∈ m := (hmverts x).mpr hx
        simp [hnil] at this
      refine ⟨ms, ?_⟩
      simp only [ChildData]
      refine ⟨?_, ?_, ?_, hdisj_ms, hnod_ms, hal₁, hal₂, ?_, ?_⟩
      · simp only [ConsistsList]
        exact ⟨m, ms_t, hcons_head, hms_t, rfl⟩
      · intro m' hm'
        rcases List.mem_cons.mp hm' with rfl | hm''
        · exact hmrun
        · exact hrun_t m' hm''
      · intro m' hm'
        rcases List.mem_cons.mp hm' with rfl | hm''
        · exact hm_nod
        · exact hnod_t m' hm''
      · intro m' hm'
        rcases List.mem_cons.mp hm' with rfl | hm''
        · exact hne_m
        · exact hne_t m' hm''
      · simpa [ms, Aligned] using (And.intro hmverts halign_t))
    p hwf hc ho

/-! ### Claim 2 (completeness): every non-crossing circular order gives an admissible answer -/

/-- **The answer permutation is admissible.**  If `p` is a sound part tree covering all
vertices, every subtree of which occupies a contiguous arc of the circle, and whose blocks
respect the outer-cycle order, then the permutation `arrangement σ` is one of the arrangements
that the block-cut recursion is allowed to produce. -/
theorem arrangement_valid (σ : CircOrder n) [NeZero n] (p : Part (Fin n))
    (hwf : GeoWF p) (hc : AllContig σ p) (ho : GeoOrder σ p)
    (hverts : ∀ x, x ∈ arrangement σ ↔ x ∈ partVerts p) :
    Part.Valid p (arrangement σ) := by
  have hcons : Consists σ p (arrangement σ) :=
    consists_of_geometry σ p hwf hc ho (isRun_self (arrangement σ)) hverts
  exact valid_of_consists σ p hcons

/-- **Claim 2, completeness direction.**  Under the same hypotheses, and assuming the tree is
also well formed in the sense of `Part.WF`, the greedy recursive construction is
lexicographically at most the permutation induced by *any* non-crossing circular order.  This
is the missing half of Claim 2: `Part.seq_min` only compared the greedy construction with
arrangements already known to be admissible, and `arrangement_valid` shows that every real
answer is admissible. -/
theorem seq_le_arrangement (σ : CircOrder n) [NeZero n] (p : Part (Fin n))
    (hwfP : Part.WF p) (hwf : GeoWF p) (hc : AllContig σ p) (ho : GeoOrder σ p)
    (hverts : ∀ x, x ∈ arrangement σ ↔ x ∈ partVerts p) :
    Part.seq p ≤ arrangement σ :=
  Part.seq_min hwfP (arrangement_valid σ p hwf hc ho hverts)

end Graperm
