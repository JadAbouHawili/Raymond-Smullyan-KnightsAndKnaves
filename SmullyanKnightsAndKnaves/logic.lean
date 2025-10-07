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

--theorem XorToOr
--{Knight : Finset Inhabitant } {Knave : Finset Inhabitant} (A : Inhabitant)
--(h : Knight ∩ Knave = ∅ ) : Xor' (A ∈ Knight) (A ∈ Knave) ↔ A ∈ Knight ∨ A ∈ Knave := by
--  constructor
--  unfold Xor' at *
--  · intro h'
--    rcases h' with h_1|h_2
--    · exact Or.inl (h_1.left)
--    · exact Or.inr (h_2.left)
--
--  · intro h'
--    unfold Xor'
--    rcases h' with h_1|h_2
--    · left
--      constructor
--      assumption
--      exact inleft_notinright h h_1
--    · right
--      constructor
--      assumption
--      exact inright_notinleft h h_2
