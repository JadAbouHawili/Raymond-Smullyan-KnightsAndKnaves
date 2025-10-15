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
