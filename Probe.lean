import Mathlib.Data.List.Basic
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Lex
import Mathlib.Order.Basic
import Mathlib.Tactic

example {α : Type*} [LinearOrder α] : LinearOrder (List α) := inferInstance

#check @List.map_eq_nil_iff
#check @List.length_eq_zero_iff
#check @List.Perm.nodup_iff
#check @List.Perm.nodup
#check @List.Nodup.erase
#check @lt_of_le_of_ne
#check @le_antisymm
#check @eq_or_lt_of_le
#check @List.Perm.append
#check @List.mem_of_mem_erase
#check @List.mem_append
#check @List.map_append
#check @List.map_map
#check @List.flatten_cons
#check @List.append_le_append_right
#check @Nat.strongRecOn
#check @List.length_erase_of_mem
#check @List.getLast
