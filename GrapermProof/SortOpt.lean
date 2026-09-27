/-
# `GrapermProof.SortOpt`

Generic list-combinatorics lemmas underlying Claim 2 of the editorial: the greedy
"sort the children by first element and concatenate" / "pick the better of the two
directions" construction produces the lexicographically smallest concatenation.

Everything here is stated for an abstract `LinearOrder` type `α`; the tree-level
recursion in `GrapermProof.BlockTree` applies them with `α = V`.
-/
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Flatten
import Mathlib.Order.Basic
import Mathlib.Tactic

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Graperm

variable {α : Type*}

/-- First element of a list, defaulted via `Inhabited` when empty. -/
def headV [Inhabited α] (l : List α) : α := l.head!

theorem headV_cons [Inhabited α] (a : α) (l : List α) : headV (a :: l) = a :=
  List.head!_cons a l

theorem headV_mem [Inhabited α] {l : List α} (h : l ≠ []) : headV l ∈ l := by
  have e := List.cons_head!_tail h
  rw [← e]
  exact List.mem_cons_self ..

/-- Rotating one element to the front. -/
theorem perm_cons_append (a b : List α) (m : α) : (a ++ m :: b).Perm (m :: (a ++ b)) := by
  induction a with
  | nil => exact List.Perm.refl _
  | cons x t ih =>
      show (x :: (t ++ m :: b)).Perm (m :: ((x :: t) ++ b))
      rw [List.cons_append]
      exact (List.Perm.cons x ih).trans (List.Perm.swap m x (t ++ b))

variable [Inhabited α] [LinearOrder α]

/-- Two equal-length lists related by `List.Lex` stay related after appending. -/
theorem lex_append_append {x : List α} :
    ∀ {y : List α}, List.Lex (· < ·) x y → x.length = y.length →
      ∀ a b : List α, List.Lex (· < ·) (x ++ a) (y ++ b) := by
  induction x with
  | nil =>
      intro y h hlen a b
      cases y with
      | nil => exact absurd h (by intro hh; cases hh)
      | cons c t => simp at hlen
  | cons c t ih =>
      intro y h hlen a b
      cases y with
      | nil => exact absurd h (by intro hh; cases hh)
      | cons d u =>
          cases h with
          | rel hcd =>
              show List.Lex (· < ·) ((c :: t) ++ a) ((d :: u) ++ b)
              rw [List.cons_append, List.cons_append]
              exact List.Lex.rel hcd
          | cons htu =>
              have hlen' : t.length = u.length := Nat.succ.inj hlen
              show List.Lex (· < ·) ((c :: t) ++ a) ((c :: u) ++ b)
              rw [List.cons_append, List.cons_append]
              exact List.Lex.cons (ih htu hlen' a b)

/-- If two nonempty lists have strictly increasing first elements, so do their appends. -/
theorem lex_of_head_lt_append {x y u v : List α}
    (hx : x ≠ []) (hy : y ≠ []) (h : headV x < headV y) :
    List.Lex (· < ·) (x ++ u) (y ++ v) := by
  have e1 : x ++ u = x.head! :: (x.tail ++ u) := by
    conv_lhs => rw [← List.cons_head!_tail hx]
    rw [List.cons_append]
  have e2 : y ++ v = y.head! :: (y.tail ++ v) := by
    conv_lhs => rw [← List.cons_head!_tail hy]
    rw [List.cons_append]
  rw [e1, e2]
  exact List.Lex.rel h

/-- The `List` order is the `List.Lex` order of `<`. -/
theorem lt_iff_lex {a b : List α} : a < b ↔ List.Lex (· < ·) a b := List.lt_iff_lex_lt a b

/-- `List.Lex` implies `≤`. -/
theorem lex_le {a b : List α} (h : List.Lex (· < ·) a b) : a ≤ b :=
  le_of_lt (lt_iff_lex.mpr h)

/-! ### Injectivity of `headV` under a `map` -/

theorem nodup_map_eq {β : Type*} {f : α → β} {l : List α} (h : (l.map f).Nodup)
    {x y : α} (hx : x ∈ l) (hy : y ∈ l) (hxy : f x = f y) : x = y := by
  induction l with
  | nil => exact absurd hx (by simp)
  | cons a t ih =>
      rw [List.map_cons, List.nodup_cons] at h
      obtain ⟨hfa, hnd⟩ := h
      rcases List.mem_cons.mp hx with rfl | hx'
      · rcases List.mem_cons.mp hy with rfl | hy'
        · rfl
        · exact absurd (List.mem_map.mpr ⟨y, hy', hxy.symm⟩) hfa
      · rcases List.mem_cons.mp hy with rfl | hy'
        · exact absurd (List.mem_map.mpr ⟨x, hx', hxy⟩) hfa
        · exact ih hnd hx' hy'

/-! ### Sorting items by first element -/

/-- Boolean comparison of two items by their first element. -/
def byHeadLE (a b : List α) : Bool := decide (headV a ≤ headV b)

/-- The greedy item order: items sorted by first element (stable merge sort). -/
def sortedByHead (xs : List (List α)) : List (List α) := xs.mergeSort byHeadLE

theorem sortedByHead_perm (xs : List (List α)) : (sortedByHead xs).Perm xs :=
  List.mergeSort_perm xs byHeadLE

theorem byHeadLE_trans (a b c : List α) :
    byHeadLE a b = true → byHeadLE b c = true → byHeadLE a c = true := by
  rw [byHeadLE, byHeadLE, byHeadLE, decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff]
  exact fun h1 h2 => le_trans h1 h2

theorem byHeadLE_total (a b : List α) : (byHeadLE a b || byHeadLE b a) = true := by
  rw [byHeadLE, byHeadLE, Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff]
  exact le_total (headV a) (headV b)

/-- The sorted order is nondecreasing in the first element. -/
theorem sortedByHead_pairwise (xs : List (List α)) :
    (sortedByHead xs).Pairwise (fun a b => headV a ≤ headV b) :=
  List.Pairwise.imp (fun {_ _} h => by rwa [byHeadLE, decide_eq_true_iff] at h)
    (List.pairwise_mergeSort byHeadLE_trans byHeadLE_total xs)

/-! ### Pointwise comparison of lists of items -/

/-- Pointwise lexicographic bound on lists of equal-length items. -/
def PointLe : List (List α) → List (List α) → Prop
  | [], [] => True
  | x :: xs, y :: ys => x.length = y.length ∧ x ≤ y ∧ PointLe xs ys
  | _, _ => False

theorem flatten_le_flatten : ∀ {xs ys : List (List α)}, PointLe xs ys → xs.flatten ≤ ys.flatten
  | [], [], _ => le_refl []
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | x :: xs, y :: ys, h => by
      obtain ⟨hlen, hxy, htl⟩ := h
      have ih : xs.flatten ≤ ys.flatten := flatten_le_flatten htl
      rw [List.flatten_cons, List.flatten_cons]
      rcases eq_or_lt_of_le hxy with heq | hlt
      · rw [heq]
        rcases eq_or_lt_of_le ih with heq2 | hlt2
        · rw [heq2]
        · exact lex_le (List.Lex.append_left (· < ·) (lt_iff_lex.mp hlt2) y)
      · exact lex_le (lex_append_append (lt_iff_lex.mp hlt) hlen xs.flatten ys.flatten)

/-! ### Round-node optimality -/

/-- **Round-node optimality.** Sorting a list of nonempty items with pairwise distinct
first elements by first element and concatenating yields the lexicographically smallest
concatenation among all permutations of the items. -/
theorem flatten_sorted_min {S ys : List (List α)}
    (hperm : S.Perm ys) (hsorted : S.Pairwise (fun a b => headV a ≤ headV b))
    (hne : ∀ x ∈ ys, x ≠ []) (hnd : (ys.map headV).Nodup) :
    S.flatten ≤ ys.flatten := by
  induction S generalizing ys with
  | nil =>
      rw [List.Perm.eq_nil hperm.symm]
  | cons s0 S' ih =>
      have hys_ne : ys ≠ [] := by
        intro h
        rw [h] at hperm
        exact absurd (List.Perm.eq_nil hperm) (by simp)
      have hdecomp : ys.head! :: ys.tail = ys := List.cons_head!_tail hys_ne
      have hall : ∀ a' ∈ S', headV s0 ≤ headV a' := (List.pairwise_cons.mp hsorted).1
      have hm_mem : ys.head! ∈ ys := by rw [← hdecomp]; exact List.mem_cons_self ..
      have hs0_mem : s0 ∈ ys := hperm.mem_iff.mp (List.mem_cons_self ..)
      have hs0_le : headV s0 ≤ headV ys.head! := by
        rcases List.mem_cons.mp (hperm.symm.mem_iff.mp hm_mem) with h | h
        · rw [h]
        · exact hall _ h
      rcases eq_or_lt_of_le hs0_le with heq | hlt
      · have hidx : s0 = ys.head! := nodup_map_eq hnd hs0_mem hm_mem heq
        have hys_eq : ys = s0 :: ys.tail := by
          conv_lhs => rw [← hdecomp]
          rw [hidx]
        have hperm' : S'.Perm ys.tail := by
          rw [hys_eq] at hperm
          exact List.Perm.cons_inv hperm
        have hnd' : (ys.tail.map headV).Nodup := by
          rw [List.map_tail]
          exact hnd.tail
        have ihp := ih hperm' (List.Pairwise.of_cons hsorted)
          (fun x hx => hne x (List.mem_of_mem_tail hx)) hnd'
        rw [List.flatten_cons, ← hdecomp, List.flatten_cons, ← hidx]
        rcases eq_or_lt_of_le ihp with heq2 | hlt2
        · rw [heq2]
        · exact lex_le (List.Lex.append_left (· < ·) (lt_iff_lex.mp hlt2) s0)
      · have hs0_ne : s0 ≠ [] := hne s0 hs0_mem
        have hm_ne : ys.head! ≠ [] := hne _ hm_mem
        rw [List.flatten_cons, ← hdecomp, List.flatten_cons]
        exact lex_le (lex_of_head_lt_append hs0_ne hm_ne hlt)

/-! ### First element decides the order -/

/-- Two nonempty lists with distinct first elements are ordered exactly as their first
elements are.  This is the editorial's observation that "comparing only the first element
suffices", made precise. -/
theorem lt_iff_head!_lt {a b : List α} (ha : a ≠ []) (hb : b ≠ [])
    (hne : a.head! ≠ b.head!) : a < b ↔ a.head! < b.head! := by
  have ea : a = a.head! :: a.tail := (List.cons_head!_tail ha).symm
  have eb : b = b.head! :: b.tail := (List.cons_head!_tail hb).symm
  rw [ea, eb, List.cons_lt_cons_iff]
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact h
    · exact absurd h hne
  · exact Or.inl

theorem lt_iff_head_lt {a b : List α} (ha : a ≠ []) (hb : b ≠ [])
    (hne : headV a ≠ headV b) : a < b ↔ headV a < headV b :=
  lt_iff_head!_lt ha hb hne

/-- A `List.Lex` relation starting from a nonempty list never increases the first element. -/
theorem headV_le_of_lex {a b : List α} (ha : a ≠ []) (h : List.Lex (· < ·) a b) :
    headV a ≤ headV b := by
  induction h with
  | nil => exact absurd rfl ha
  | rel hab => exact le_of_lt hab
  | cons _ => exact le_of_eq (by simp [headV, List.head!_cons])

/-- The first element is monotone for the lexicographic order on lists. -/
theorem headV_le_of_le {a b : List α} (ha : a ≠ []) (h : a ≤ b) : headV a ≤ headV b := by
  rcases eq_or_lt_of_le h with heq | hlt
  · rw [heq]
  · exact headV_le_of_lex ha (lt_iff_lex.mp hlt)

/-- A concatenation of nonempty blocks over a nonempty family is nonempty. -/
theorem flatten_ne_nil {l : List (List α)} (h : l ≠ []) (hne : ∀ x ∈ l, x ≠ []) :
    l.flatten ≠ [] := by
  intro hf
  rw [List.flatten_eq_nil_iff] at hf
  exact hne l.head! (headV_mem h) (hf l.head! (headV_mem h))

/-! ### Block-node choice -/

/-- Choose the lex-smaller of the two possible concatenation directions at a block node. -/
def blockChoice (ss : List (List α)) : List α :=
  if ss.reverse.flatten < ss.flatten then ss.reverse.flatten else ss.flatten

theorem blockChoice_le_forward (ss : List (List α)) : blockChoice ss ≤ ss.flatten := by
  unfold blockChoice
  split
  · exact le_of_lt (by assumption)
  · exact le_refl _

theorem blockChoice_le_reverse (ss : List (List α)) : blockChoice ss ≤ ss.reverse.flatten := by
  unfold blockChoice
  split
  · exact le_refl _
  · exact le_of_not_gt (by assumption)

end Graperm
