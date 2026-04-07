import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic.Have

theorem notleft_right {P Q : Prop} (Or : P ∨ Q)(notleft : ¬P) : Q := by
  cases Or
  contradiction
  assumption

theorem notright_left {P Q : Prop} (Or : P ∨ Q)(notright : ¬Q) : P := by
  cases Or
  assumption
  contradiction

-- two sets of the same cardinality are subsets which means they are equal
#check Finset.eq_iff_card_ge_of_superset
  #check Finset.eq_iff_card_le_of_subset
  #check Finset.subset_iff_eq_of_card_le
  #check Finset.eq_of_subset_of_card_le
theorem eq_of_subset_card_eq {K : Type} {A B : Finset K} (h1 : A ⊆ B) (h2 : A.card = B.card) : A = B := by
  exact Finset.eq_of_subset_of_card_le h1 (by grind)
