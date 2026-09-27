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
  | .block cs =>
      let ss := seqList cs
      if ss.reverse.flatten < ss.flatten then ss.reverse.flatten else ss.flatten
end

/-- Well-formedness of a rooted block-cut tree.

This records exactly the graph-theoretic facts about the block-cut tree that the greedy
argument uses: distinct child parts live on **pairwise disjoint vertex sets**, and a round
vertex lies in none of its children.  Admissible sequences of distinct siblings therefore
have pairwise distinct first elements — the editorial's remark that "the parts being compared
have disjoint vertex sets, so their first elements cannot coincide". -/
def WF : Part V → Prop
  | .round v cs =>
      (∀ c ∈ cs, WF c) ∧
      (∀ c₁ ∈ cs, ∀ c₂ ∈ cs, c₁ ≠ c₂ →
        ∀ l₁, Valid c₁ l₁ → ∀ l₂, Valid c₂ l₂ → ∀ x ∈ l₁, x ∉ l₂) ∧
      (∀ c ∈ cs, ∀ l, Valid c l → v ∉ l)
  | .block cs =>
      cs ≠ [] ∧ (∀ c ∈ cs, WF c) ∧
      (∀ c₁ ∈ cs, ∀ c₂ ∈ cs, c₁ ≠ c₂ →
        ∀ l₁, Valid c₁ l₁ → ∀ l₂, Valid c₂ l₂ → ∀ x ∈ l₁, x ∉ l₂)

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
    (hdisj : cs.Pairwise (fun c₁ c₂ =>
      ∀ l₁, Valid c₁ l₁ → ∀ l₂, Valid c₂ l₂ → ∀ x ∈ l₁, x ∉ l₂))
    (hf : ∀ c ∈ cs, ∃ l, Valid c l ∧ f c ∈ l) : (cs.map f).Nodup := by
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

end Part

end Graperm
