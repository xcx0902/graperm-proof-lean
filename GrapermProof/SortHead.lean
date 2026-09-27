/-
# `GrapermProof.SortHead`

A concrete insertion sort of a list of *blocks* (nonempty lists of vertices) by their first
element.  Insertion sort is chosen over `List.mergeSort` because the optimality proof of
Claim 2 needs to peel off the minimal block, and insertion sort makes that step elementary.

The generic comparison lemmas live in `GrapermProof.SortOpt`; this file adds the sorting
algorithm itself and its structural properties.
-/
import GrapermProof.SortOpt

set_option linter.style.haveILetI false

namespace Graperm

variable {α : Type*}

/-- Insert a block into an already sorted (by first element) list of blocks. -/
def insertHead [Inhabited α] [LinearOrder α] (b : List α) :
    List (List α) → List (List α)
  | [] => [b]
  | c :: t => if headV b ≤ headV c then b :: c :: t else c :: insertHead b t

/-- Insertion sort of a list of blocks by first element. -/
def sortHead [Inhabited α] [LinearOrder α] : List (List α) → List (List α)
  | [] => []
  | b :: t => insertHead b (sortHead t)

variable [Inhabited α] [LinearOrder α]

theorem insertHead_perm (b : List α) (l : List (List α)) :
    (insertHead b l).Perm (b :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons c t ih =>
      rw [insertHead]
      split
      · exact List.Perm.refl _
      · exact (List.Perm.cons c ih).trans (List.Perm.swap b c t)

theorem sortHead_perm (l : List (List α)) : (sortHead l).Perm l := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons b t ih => exact (insertHead_perm b (sortHead t)).trans (List.Perm.cons b ih)

/-- Inserting a block whose head is minimal puts it at the front. -/
theorem insertHead_eq_cons {b : List α} {l : List (List α)}
    (h : ∀ x ∈ l, headV b ≤ headV x) : insertHead b l = b :: l := by
  induction l with
  | nil => rfl
  | cons c t ih =>
      rw [insertHead]
      split_ifs with hbc
      · rfl
      · exact absurd (h c (List.mem_cons_self ..)) hbc

theorem insertHead_pairwise {b : List α} {l : List (List α)}
    (hl : l.Pairwise (fun a c => headV a ≤ headV c)) :
    (insertHead b l).Pairwise (fun a c => headV a ≤ headV c) := by
  induction l with
  | nil => simp [insertHead]
  | cons c t ih =>
      rw [insertHead]
      split_ifs with hbc
      · refine List.Pairwise.cons ?_ hl
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hbc
        · exact le_trans hbc ((List.pairwise_cons.mp hl).1 x hx')
      · have hcb : headV c ≤ headV b := le_of_lt (not_le.mp hbc)
        refine List.Pairwise.cons ?_ (ih (List.pairwise_cons.mp hl).2)
        intro y hy
        rcases List.mem_cons.mp ((insertHead_perm b t).mem_iff.mp hy) with rfl | hy''
        · exact hcb
        · exact (List.pairwise_cons.mp hl).1 y hy''

theorem sortHead_pairwise (l : List (List α)) :
    (sortHead l).Pairwise (fun a c => headV a ≤ headV c) := by
  induction l with
  | nil => simp [sortHead]
  | cons b t ih => exact insertHead_pairwise ih

/-! ### Peeling off the minimal block -/

/-- Peeling the minimal-head block of a sorted list with pairwise distinct heads. -/
theorem sortHead_eq_head_erase {l : List (List α)} [DecidableEq α] {b : List α} (hb : b ∈ l)
    (hmin : ∀ x ∈ l, headV b ≤ headV x) (hnd : (l.map headV).Nodup) :
    sortHead l = b :: sortHead (l.erase b) := by
  induction l with
  | nil => exact absurd hb (by simp)
  | cons c t ih =>
      rw [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hct, hndt⟩ := hnd
      rw [sortHead]
      rcases List.mem_cons.mp hb with hbc | hb'
      · rw [hbc] at hmin ⊢
        rw [insertHead_eq_cons (l := sortHead t) (fun x hx =>
              hmin x (List.mem_cons_of_mem c ((sortHead_perm t).mem_iff.mp hx))),
          List.erase_cons_head]
      · have hbc_ne : headV b ≠ headV c := fun h =>
          hct (List.mem_map.mpr ⟨b, hb', h⟩)
        have hblt : headV b < headV c :=
          lt_of_le_of_ne (hmin c (List.mem_cons_self ..)) hbc_ne
        have hih := ih hb' (fun x hx => hmin x (List.mem_cons_of_mem c hx)) hndt
        have hbc' : c ≠ b := fun h => hbc_ne (by rw [h])
        rw [hih, List.erase_cons_tail (by rw [beq_iff_eq]; exact hbc')]
        rw [sortHead, insertHead, ite_eq_right (not_le.mpr hblt)]

end Graperm
