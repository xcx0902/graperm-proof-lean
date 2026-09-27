/-
# `GrapermProof.BlockTree`

Claim 2 of the editorial: the recursive construction on the *block-cut tree*（圆方树）is
lexicographically optimal.

We model the rooted block-cut tree of a connected component abstractly:

* `Part.round v cs` — a *round* vertex `v` (a cut vertex, or the root) together with the
  list `cs` of the blocks hanging below it;
* `Part.block cs` — a *square* vertex, i.e. a block, whose children `cs` are the round
  vertices of the block other than its parent, listed in the order they appear along the
  block's outer cycle (from the parent).

Both the admissibility predicate `valid` and the greedy construction `seq` are defined by
recursion on this tree.
-/
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Flatten
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic

set_option linter.style.haveILetI false

namespace Graperm

/-- A node of the rooted block-cut tree.  `round v cs`: the round vertex `v` with the blocks
`cs` below it.  `block cs`: a block whose non-parent vertices are `cs`, in outer-cycle order. -/
inductive Part (V : Type*) where
  | round : V → List (Part V) → Part V
  | block : List (Part V) → Part V
  deriving Inhabited

namespace Part

variable {V : Type*}

/-- The set of vertices occurring in a part. -/
def vset [DecidableEq V] : Part V → Finset V
  | .round v cs => insert v ((cs.map vset).foldr (· ∪ ·) ∅)
  | .block cs => (cs.map vset).foldr (· ∪ ·) ∅

/-- Well-formedness of a rooted block-cut tree: below a round vertex the vertex sets of its
children are pairwise disjoint and avoid the vertex itself; this propagates downwards. -/
def WF [DecidableEq V] : Part V → Prop
  | .round v cs =>
      (∀ c ∈ cs, WF c) ∧ (∀ c ∈ cs, v ∉ c.vset) ∧
        (∀ c₁ ∈ cs, ∀ c₂ ∈ cs, c₁ ≠ c₂ → Disjoint c₁.vset c₂.vset)
  | .block cs =>
      (∀ c ∈ cs, WF c) ∧ (∀ c₁ ∈ cs, ∀ c₂ ∈ cs, c₁ ≠ c₂ → Disjoint c₁.vset c₂.vset)

/-- Head of a nonempty list, used as the key ("first output vertex"). -/
def headV [Inhabited V] (l : List V) : V := l.head!

mutual
/-- The sequences that are admissible for a list of parts, one per child. -/
def validList : List (Part V) → Set (List (List V))
  | [] => {[]}
  | c :: rest => { ms | ∃ m ∈ valid c, ∃ ms' ∈ validList rest, ms = m :: ms' }

/-- The arrangements that are **admissible** for a part, i.e. produced by the block-cut tree
recursion with arbitrary legal choices.

* at a round vertex: the child parts (each admissible for its block) may be arranged in any
  order, and the vertex itself may be placed anywhere between them;
* at a block: the child parts must be concatenated in outer-cycle order, either forwards or
  backwards. -/
def valid : Part V → Set (List V)
  | .round v cs =>
      { l | ∃ (cs' : List (Part V)), cs'.Perm cs ∧
            ∃ (ms : List (List V)), ms ∈ validList cs' ∧
            ∃ (k : ℕ), k ≤ ms.length ∧
              l = (ms.take k).flatten ++ [v] ++ (ms.drop k).flatten }
  | .block cs =>
      { l | (∃ ms ∈ validList cs, l = ms.flatten) ∨
            (∃ ms ∈ validList cs, l = ms.reverse.flatten) }
end

variable [Inhabited V] [LinearOrder V]

mutual
/-- The greedy sequences of a list of parts. -/
def seqList : List (Part V) → List (List V)
  | [] => []
  | c :: rest => seq c :: seqList rest

/-- The greedy (lexicographically smallest) arrangement of a part.  At a round vertex the
child parts and the singleton vertex are sorted by first element and concatenated; at a block
the better of the two outer-cycle directions is taken. -/
def seq : Part V → List V
  | .round v cs =>
      ((seqList cs ++ [[v]]).mergeSort (fun a b => decide (headV a ≤ headV b))).flatten
  | .block cs =>
      let ss := seqList cs
      match ss with
      | [] => []
      | s0 :: _ =>
          if decide (headV s0 ≤ headV ss.reverse.head!) then ss.flatten else ss.reverse.flatten
end

end Part

end Graperm
