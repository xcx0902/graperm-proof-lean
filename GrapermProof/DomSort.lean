/-
# `GrapermProof.DomSort`

The combinatorial heart of Claim 2: comparing the lexicographic order of two concatenations
of blocks.

`Dom B T` says that the blocks of `B` and `T` can be **matched up** (the matching is carried
explicitly as a list of pairs) so that each matched pair `(b, t)` has `b ≤ t` in the
lexicographic order on lists, `headV b ≤ headV t`, and equal lengths, both blocks being
nonempty.

The main lemma `Dom.sortHead_flatten_le` shows that sorting both lists by first element (with
pairwise distinct first elements) preserves the domination on the concatenations:

  `(sortHead B).flatten ≤ (sortHead T).flatten`.

This is what makes the greedy "sort the children by first element and concatenate" optimal.
The proof needs to peel the minimal block off both lists, which is why the matching is
carried as a list of pairs rather than a positional relation.
-/
import GrapermProof.SortHead

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Graperm

variable {α : Type*}

/-- Re-inserting an erased element recovers a permutation. -/
theorem perm_cons_erase' [BEq α] [LawfulBEq α] {l : List α} {a : α} (h : a ∈ l) :
    (a :: l.erase a).Perm l := by
  induction l with
  | nil => exact absurd h (by simp)
  | cons c t ih =>
      rw [List.erase_cons]
      split_ifs with hca
      · rw [← beq_iff_eq.mp hca]
      · have hcal : c ≠ a := fun h' => hca (by rw [h', beq_self_eq_true])
        have ha' : a ∈ t := by
          rcases List.mem_cons.mp h with h' | h'
          · exact absurd h'.symm hcal
          · exact h'
        exact (List.Perm.swap c a (t.erase a)).trans (List.Perm.cons c (ih ha'))

/-- Erasing a list element and mapping to a quotient: only one occurrence of the image
disappears. -/
theorem erase_map_perm {β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) {a : α} {l : List α} (ha : a ∈ l) :
    ((l.erase a).map f).Perm ((l.map f).erase (f a)) := by
  induction l with
  | nil => exact absurd ha (by simp)
  | cons c t ih =>
      rw [List.erase_cons]
      split_ifs with hca
      · have hfac : (f c == f a) = true := by rw [beq_iff_eq, beq_iff_eq.mp hca]
        rw [List.map_cons, List.erase_cons, ite_eq_left hfac]
      · have hcal : c ≠ a := fun h' => hca (by rw [h', beq_self_eq_true])
        have ha' : a ∈ t := by
          rcases List.mem_cons.mp ha with h' | h'
          · exact absurd h'.symm hcal
          · exact h'
        simp only [List.map_cons, List.erase_cons]
        by_cases hfa : (f c == f a) = true
        · rw [ite_eq_left hfa, beq_iff_eq.mp hfa]
          exact (List.Perm.cons (f a) (ih ha')).trans
            (perm_cons_erase' (List.mem_map.mpr ⟨a, ha', rfl⟩))
        · rw [ite_eq_right hfa]
          exact List.Perm.cons (f c) (ih ha')

/-- Pointwise domination of two lists of blocks, up to a matching. -/
def Dom [Inhabited α] [LinearOrder α] (B T : List (List α)) : Prop :=
  ∃ P : List (List α × List α),
    (P.map Prod.fst).Perm B ∧ (P.map Prod.snd).Perm T ∧
    ∀ p ∈ P, p.1 ≠ [] ∧ p.2 ≠ [] ∧ p.1 ≤ p.2 ∧ headV p.1 ≤ headV p.2 ∧
      p.1.length = p.2.length

variable [Inhabited α] [LinearOrder α]

theorem Dom.length_eq {B T : List (List α)} (h : Dom B T) : B.length = T.length := by
  obtain ⟨P, hP1, hP2, -⟩ := h
  rw [← hP1.length_eq, ← hP2.length_eq, List.length_map, List.length_map]

/-- `Dom` is preserved when the same list of blocks is appended to both sides. -/
theorem Dom.append (X : List (List α)) {B T : List (List α)} (hd : Dom B T)
    (hX : ∀ x ∈ X, x ≠ []) : Dom (B ++ X) (T ++ X) := by
  obtain ⟨P, hP1, hP2, hPc⟩ := hd
  have hfst : (X.map (fun x => (x, x))).map Prod.fst = X := by
    simp [List.map_map, Function.comp_def]
  have hsnd : (X.map (fun x => (x, x))).map Prod.snd = X := by
    simp [List.map_map, Function.comp_def]
  refine ⟨P ++ X.map (fun x => (x, x)), ?_, ?_, ?_⟩
  · rw [List.map_append, hfst]
    exact hP1.append (List.Perm.refl X)
  · rw [List.map_append, hsnd]
    exact hP2.append (List.Perm.refl X)
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hPc p hp
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
      exact ⟨hX x hx, hX x hx, le_rfl, le_rfl, rfl⟩

/-- `a ++ x ≤ a ++ y` whenever `x ≤ y`. -/
theorem append_le_append_left {a x y : List α} (h : x ≤ y) : a ++ x ≤ a ++ y := by
  rcases eq_or_lt_of_le h with h | h
  · rw [h]
  · exact le_of_lt (lt_iff_lex.mpr (List.Lex.append_left (· < ·) (lt_iff_lex.mp h) a))

variable [DecidableEq α]

/-- Erasing the **matched pair** of minimal blocks preserves `Dom`. -/
theorem Dom.erase_min {B T : List (List α)} (hd : Dom B T)
    (hB : (B.map headV).Nodup) (hT : (T.map headV).Nodup) (hne : B ≠ [])
    (heq : headV (headV (sortHead B)) = headV (headV (sortHead T))) :
    Dom (B.erase (headV (sortHead B))) (T.erase (headV (sortHead T))) := by
  obtain ⟨P, hP1, hP2, hPc⟩ := hd
  have hPne : P ≠ [] := by
    intro h
    rw [h] at hP1
    exact hne (List.Perm.eq_nil hP1.symm)
  have hneT : T ≠ [] := by
    intro h
    exact hPne (List.map_eq_nil_iff.mp (List.Perm.eq_nil (h ▸ hP2)))
  have hb0mem : headV (sortHead B) ∈ B := minH_mem hne
  have ht0mem : headV (sortHead T) ∈ T := minH_mem hneT
  obtain ⟨q, hqP, hq2⟩ : ∃ q ∈ P, q.2 = headV (sortHead T) := by
    obtain ⟨q, hq, hq2⟩ := List.mem_map.mp (hP2.symm.mem_iff.mp ht0mem)
    exact ⟨q, hq, hq2⟩
  have hq1mem : q.1 ∈ B := hP1.mem_iff.mp (List.mem_map.mpr ⟨q, hqP, rfl⟩)
  have hq1 : q.1 = headV (sortHead B) := by
    refine nodup_map_eq hB hq1mem hb0mem ?_
    refine le_antisymm ?_ ?_
    · rw [heq, ← hq2]; exact (hPc q hqP).2.2.2.1
    · exact minH_le (l := B) hq1mem
  refine ⟨P.erase q, ?_, ?_, ?_⟩
  · refine (erase_map_perm Prod.fst hqP).trans ?_
    rw [hq1]
    exact List.Perm.erase _ hP1
  · refine (erase_map_perm Prod.snd hqP).trans ?_
    rw [hq2]
    exact List.Perm.erase _ hP2
  · intro p hp
    exact hPc p (List.mem_of_mem_erase hp)

/-- **Domination is preserved by sorting** (auxiliary, by strong induction on the length). -/
theorem Dom.sortHead_flatten_le_aux (n : ℕ) :
    ∀ (B T : List (List α)), B.length = n → Dom B T → (B.map headV).Nodup →
      (T.map headV).Nodup → (sortHead B).flatten ≤ (sortHead T).flatten :=
  Nat.strongRecOn (motive := fun n => ∀ (B T : List (List α)), B.length = n → Dom B T →
      (B.map headV).Nodup → (T.map headV).Nodup →
      (sortHead B).flatten ≤ (sortHead T).flatten) n (fun n ih => by
    intro B T hlen hd hB hT
    by_cases hBnil : B = []
    · subst hBnil
      obtain ⟨P, hP1, hP2, -⟩ := hd
      have hPnil : P = [] := List.map_eq_nil_iff.mp (List.Perm.eq_nil hP1)
      subst hPnil
      have hTnil : T = [] := List.Perm.eq_nil hP2.symm
      subst hTnil
      simp [sortHead]
    · obtain ⟨P, hP1, hP2, hPc⟩ := hd
      have hsBne : sortHead B ≠ [] := sortHead_ne_nil hBnil
      have hPne : P ≠ [] := by
        intro h; rw [h] at hP1; exact hBnil (List.Perm.eq_nil hP1.symm)
      have hneT : T ≠ [] := by
        intro h; exact hPne (List.map_eq_nil_iff.mp (List.Perm.eq_nil (h ▸ hP2)))
      have hsTne : sortHead T ≠ [] := sortHead_ne_nil hneT
      have hle : headV (headV (sortHead B)) ≤ headV (headV (sortHead T)) := by
        obtain ⟨q, hqP, hq2⟩ := List.mem_map.mp (hP2.symm.mem_iff.mp (minH_mem hneT))
        have hq1mem : q.1 ∈ B := hP1.mem_iff.mp (List.mem_map.mpr ⟨q, hqP, rfl⟩)
        calc headV (headV (sortHead B)) ≤ headV q.1 := minH_le hq1mem
          _ ≤ headV q.2 := (hPc q hqP).2.2.2.1
          _ = headV (headV (sortHead T)) := by rw [hq2]
      rcases eq_or_lt_of_le hle with heq | hlt
      · obtain ⟨q, hqP, hq2⟩ := List.mem_map.mp (hP2.symm.mem_iff.mp (minH_mem hneT))
        have hq1mem : q.1 ∈ B := hP1.mem_iff.mp (List.mem_map.mpr ⟨q, hqP, rfl⟩)
        have hq1 : q.1 = headV (sortHead B) := by
          refine nodup_map_eq hB hq1mem (minH_mem hBnil) ?_
          refine le_antisymm ?_ ?_
          · rw [heq, ← hq2]; exact (hPc q hqP).2.2.2.1
          · exact minH_le (l := B) hq1mem
        by_cases hbte : headV (sortHead B) = headV (sortHead T)
        · have hd' : Dom (B.erase (headV (sortHead B))) (T.erase (headV (sortHead T))) :=
            Dom.erase_min ⟨P, hP1, hP2, hPc⟩ hB hT hBnil heq
          have hB' : ((B.erase (headV (sortHead B))).map headV).Nodup :=
            (List.Perm.nodup_iff (erase_map_perm headV (minH_mem hBnil))).mpr
              (List.Nodup.erase _ hB)
          have hT' : ((T.erase (headV (sortHead T))).map headV).Nodup :=
            (List.Perm.nodup_iff (erase_map_perm headV (minH_mem hneT))).mpr
              (List.Nodup.erase _ hT)
          have htailB : (sortHead B).tail = sortHead (B.erase (headV (sortHead B))) := by
            conv_lhs =>
              rw [sortHead_eq_head_erase (b := headV (sortHead B)) (minH_mem hBnil)
                (fun x hx => minH_le hx) hB]
            rw [List.tail_cons]
          have htailT : (sortHead T).tail = sortHead (T.erase (headV (sortHead T))) := by
            conv_lhs =>
              rw [sortHead_eq_head_erase (b := headV (sortHead T)) (minH_mem hneT)
                (fun x hx => minH_le hx) hT]
            rw [List.tail_cons]
          have hlt_len : (B.erase (headV (sortHead B))).length < n := by
            rw [List.length_erase_of_mem (minH_mem hBnil), ← hlen]
            exact Nat.sub_lt (List.length_pos_iff.mpr hBnil) (by norm_num)
          have ihp := ih _ hlt_len (B.erase (headV (sortHead B)))
            (T.erase (headV (sortHead T))) rfl hd' hB' hT'
          rw [← List.cons_head!_tail hsBne, ← List.cons_head!_tail hsTne,
            List.flatten_cons, List.flatten_cons,
            show (sortHead B).head! = (sortHead T).head! from hbte, htailB, htailT]
          exact append_le_append_left ihp
        · have hq_lt : q.1 < q.2 :=
            lt_of_le_of_ne (hPc q hqP).2.2.1 (fun h => hbte (hq1.symm.trans (h.trans hq2)))
          have hlenq : q.1.length = q.2.length := (hPc q hqP).2.2.2.2
          have hsortB : sortHead B = q.1 :: (sortHead B).tail := by
            rw [hq1]; exact (List.cons_head!_tail hsBne).symm
          have hsortT : sortHead T = q.2 :: (sortHead T).tail := by
            rw [hq2]; exact (List.cons_head!_tail hsTne).symm
          rw [hsortB, hsortT, List.flatten_cons, List.flatten_cons]
          exact le_of_lt (lt_iff_lex.mpr (lex_append_append (lt_iff_lex.mp hq_lt) hlenq
            (sortHead B).tail.flatten (sortHead T).tail.flatten))
      · have hb0ne : headV (sortHead B) ≠ [] := by
          obtain ⟨p, hp, hp1⟩ := List.mem_map.mp (hP1.symm.mem_iff.mp (minH_mem hBnil))
          rw [← hp1]; exact (hPc p hp).1
        have ht0ne : headV (sortHead T) ≠ [] := by
          obtain ⟨p, hp, hp2⟩ := List.mem_map.mp (hP2.symm.mem_iff.mp (minH_mem hneT))
          rw [← hp2]; exact (hPc p hp).2.1
        rw [← List.cons_head!_tail hsBne, ← List.cons_head!_tail hsTne,
          List.flatten_cons, List.flatten_cons]
        exact le_of_lt (lt_iff_lex.mpr (lex_of_head_lt_append hb0ne ht0ne hlt)))

/-- **Domination is preserved by sorting.** -/
theorem Dom.sortHead_flatten_le {B T : List (List α)} (hd : Dom B T)
    (hB : (B.map headV).Nodup) (hT : (T.map headV).Nodup) :
    (sortHead B).flatten ≤ (sortHead T).flatten :=
  Dom.sortHead_flatten_le_aux B.length B T rfl hd hB hT

/-- `Dom` only depends on the `Perm` class of its right argument. -/
theorem Dom.perm_right {B T T' : List (List α)} (hd : Dom B T) (h : T.Perm T') :
    Dom B T' := by
  obtain ⟨P, hP1, hP2, hPc⟩ := hd
  exact ⟨P, hP1, hP2.trans h, hPc⟩

/-- **Sorted domination gives a genuine lexicographic bound on the concatenation.**

If `S`'s blocks can each be matched to a block of `T` that dominates it (`Dom S T`), the heads
on both sides are pairwise distinct and no block is empty, then the greedy sorted concatenation
of `S` is at most the concatenation of `T` (whatever order the latter comes in). -/
theorem Dom.sortHead_flatten_le_flatten {S T : List (List α)} (hd : Dom S T)
    (hndS : (S.map headV).Nodup) (hneT : ∀ x ∈ T, x ≠ []) (hndT : (T.map headV).Nodup) :
    (sortHead S).flatten ≤ T.flatten :=
  le_trans (Dom.sortHead_flatten_le hd hndS hndT)
    (flatten_sorted_min (sortHead_perm T) (sortHead_pairwise T) hneT hndT)

/-! ### The positional version

For the *block* nodes the children occur in a fixed order, so no re-matching is allowed and
we use the strictly positional relation `Dom2`. -/

/-- Positional domination of two aligned lists of blocks. -/
def Dom2 : List (List α) → List (List α) → Prop
  | [], [] => True
  | b :: B, t :: T => b ≠ [] ∧ t ≠ [] ∧ b ≤ t ∧ headV b ≤ headV t ∧
      b.length = t.length ∧ Dom2 B T
  | _, _ => False

theorem Dom2.toDom : ∀ {B T : List (List α)}, Dom2 B T → Dom B T
  | [], [], _ => ⟨[], List.Perm.refl [], List.Perm.refl [], by simp⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | b :: B, t :: T, h => by
      obtain ⟨hb, ht, hbt, hhead, hlen, hrest⟩ := h
      obtain ⟨P, hP1, hP2, hPc⟩ := Dom2.toDom hrest
      exact ⟨(b, t) :: P, by rw [List.map_cons]; exact List.Perm.cons b hP1,
        by rw [List.map_cons]; exact List.Perm.cons t hP2,
        by
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact ⟨hb, ht, hbt, hhead, hlen⟩
          · exact hPc p hp'⟩

/-- Concatenating a positionally dominated family is monotone. -/
theorem Dom2.flatten_le : ∀ {B T : List (List α)}, Dom2 B T → B.flatten ≤ T.flatten
  | [], [], _ => le_refl []
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | b :: B, t :: T, h => by
      obtain ⟨hb, ht, hbt, hhead, hlen, hrest⟩ := h
      rw [List.flatten_cons, List.flatten_cons]
      rcases eq_or_lt_of_le hbt with hbt' | hbt'
      · rw [← hbt']; exact append_le_append_left (Dom2.flatten_le hrest)
      · exact le_of_lt (lt_iff_lex.mpr (lex_append_append (lt_iff_lex.mp hbt') hlen
          B.flatten T.flatten))

theorem Dom2.refl_of_ne : ∀ {X : List (List α)}, (∀ x ∈ X, x ≠ []) → Dom2 X X
  | [], _ => trivial
  | _ :: _, h => ⟨h _ (List.mem_cons_self ..), h _ (List.mem_cons_self ..), le_rfl, le_rfl, rfl,
      Dom2.refl_of_ne (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

theorem Dom2.append' (X Y : List (List α)) (hXY : Dom2 X Y) :
    ∀ {B T : List (List α)}, Dom2 B T → Dom2 (B ++ X) (T ++ Y)
  | [], [], h => hXY
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | b :: B, t :: T, h => by
      obtain ⟨hb, ht, hbt, hhead, hlen, hrest⟩ := h
      exact ⟨hb, ht, hbt, hhead, hlen, Dom2.append' X Y hXY hrest⟩

theorem Dom2.reverse : ∀ {B T : List (List α)}, Dom2 B T → Dom2 B.reverse T.reverse
  | [], [], _ => trivial
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | b :: B, t :: T, h => by
      obtain ⟨hb, ht, hbt, hhead, hlen, hrest⟩ := h
      have h' := Dom2.append' [b] [t] ⟨hb, ht, hbt, hhead, hlen, trivial⟩ (Dom2.reverse hrest)
      rw [List.reverse_cons, List.reverse_cons]
      exact h'

end Graperm
