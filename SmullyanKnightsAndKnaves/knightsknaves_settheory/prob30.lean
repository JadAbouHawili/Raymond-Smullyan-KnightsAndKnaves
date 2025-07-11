import SmullyanKnightsAndKnaves.knightsknaves
import SmullyanKnightsAndKnaves.dsl_knights_knaves

/-
Problem 30:
Suppose A says, "Either I am a knave or else two plus two
equals five." What would you conclude?
-/
-- included in dsl_2plus2
open settheory_approach
example
{inst : DecidableEq Inhabitant}
{stA : A ∈ Knight  ↔ (A ∈ Knave ∨ (2+2=5) ) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∨ (2+2=5) ) }
  :False  := by

  {
  -- simp at stAn , closes the goal
  simp at stA
  exact IamKnave stA

  }

example
{inst : DecidableEq Inhabitant}
{stA : A ∈ Knight  ↔ (A ∈ Knave ∨ (2+2=5) ) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∨ (2+2=5) ) }
  :False  := by
  {
  /-
doing the manipulations instead of letting simp do all the work
  -/
  have TwoPlusTwo : 2+2 ≠ 5 := by 
    intro
    contradiction
  have TwoPlusTwoFalse := eq_false TwoPlusTwo
  rw [TwoPlusTwoFalse] at stA
  rw [or_false] at stA
  exact IamKnave stA
}

example
{inst : DecidableEq Inhabitant}
{stA : A ∈ Knight  ↔ (A ∈ Knave ∨ (2+2=5) ) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∨ (2+2=5) ) }
  :False  := by
  if AKnight : A ∈ Knight then
    have cont := stA.mp AKnight
    if AKnave : A ∈ Knave then 
      contradiction
    else 
      have := notleft_right cont AKnave
      contradiction
  else 
    set_knight_to_knave at AKnight
    have := stAn.mp AKnight
    exact this (by left ; assumption)
