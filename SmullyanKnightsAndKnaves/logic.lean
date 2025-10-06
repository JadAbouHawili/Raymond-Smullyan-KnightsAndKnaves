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
theorem XorToOr {K : Type} {A : K} (S : Set K) (S' : Set K) (h : S ∩ S' = ∅) : Xor' (A ∈ S) (A ∈ S') ↔ A ∈ S ∨ A ∈ S' := by
  rw [xor_iff_or_and_not_and] 
  rw [not_and_or]
  constructor
  intro a1
  · have : A ∈ S ↔ A ∉ S' := by{
    constructor
    · intro h1
      intro h2
      have := Set.mem_inter h1 h2
      rw [h] at this
      contradiction
    · intro h1
      simp [h1] at a1
      assumption
      }
    simp [this]
    apply em'
  · intro a1
    constructor
    assumption
    rcases a1 with ha1|ha2
    simp [ha1]
    intro
    -- contradiction should handle this
    try contradiction
    sorry
    sorry
