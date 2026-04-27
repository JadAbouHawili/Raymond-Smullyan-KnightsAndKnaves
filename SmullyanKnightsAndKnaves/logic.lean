import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic.Have

theorem notleft_right {P Q : Prop} (h : P ∨ Q)(notleft : ¬P) : Q := by
  exact Or.resolve_left h notleft

theorem notright_left {P Q : Prop} (h : P ∨ Q)(notright : ¬Q) : P := by
  exact Or.resolve_right h notright

#check Finset.eq_iff_card_ge_of_superset
  #check Finset.eq_iff_card_le_of_subset
  #check Finset.subset_iff_eq_of_card_le
  #check Finset.eq_of_subset_of_card_le
