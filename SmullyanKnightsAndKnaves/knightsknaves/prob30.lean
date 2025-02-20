import SmullyanKnightsAndKnaves.knightsknaves

/-
Problem 30:
Suppose A says, "Either I am a knave or else two plus two 
equals five." What would you conclude?
-/
example
{Inhabitant : Type}
{A : Inhabitant}
{inst : DecidableEq Inhabitant}
{Knight : Finset Inhabitant}
{Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{stA : A ∈ Knight  ↔ (A ∈ Knave ∨ (2+2=5) ) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∨ (2+2=5) ) }
  :False  := by

  {
  simp at stAn

  --cases h1
  --· have cont := stA.mp h_1
  --  cases cont
  --  · exact disjoint h h_1 h_2
  --  · contradiction
  --· have : A ∈ Knave ∨ 2 + 2=5 := by left ; assumption
  --  have nor := stAn.mp h_1 
  --  contradiction

  }

example
{Inhabitant : Type}
{A : Inhabitant}
{inst : DecidableEq Inhabitant}
{Knight : Finset Inhabitant}
{Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
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
  -- manipulate stAn and close the goal
  have TwoPlusTwoFalse := eq_false TwoPlusTwo
  rw [TwoPlusTwoFalse] at stA
  rw [or_false] at stA
  exact IamKnave h h1 stA
  --rw [TwoPlusTwoFalse] at stAn
  --exact iff_not_self stAn
}

example
{Inhabitant : Type}
{A : Inhabitant}
{inst : DecidableEq Inhabitant}
{Knight : Finset Inhabitant}
{Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{stA : A ∈ Knight  ↔ (A ∈ Knave ∨ (2+2=5) ) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∨ (2+2=5) ) }
  :False  := by
  -- exhausing all cases, if else style
  if AKnight : A ∈ Knight then
    have cont := stA.mp AKnight
    if AKnave : A ∈ Knave then 
      rw [inright_notinleftIff h1 h] at AKnave
      contradiction
    else 
      have := notleft_right cont AKnave
      contradiction
  else 
    rw [notinleft_inrightIff h1 h] at AKnight
    have := stAn.mp AKnight
    exact this (by left ; assumption)
