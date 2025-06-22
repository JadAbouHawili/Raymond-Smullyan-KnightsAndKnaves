import SmullyanKnightsAndKnaves.dsl_knights_knaves

/-
Problem 29:
Suppose A says, "Either I am a knave or B is a knight."
What are A and B?
-/
open Islander
example {P : Prop} (h : P)(h' : ¬P) : 2=2 := by 
  contradiction
example
{stA : A said (A.isKnave ∨ B.isKnight)}
: A.isKnight ∧ B.isKnight := by 
  have AKnight : A.isKnight
  knight_to_knave
  intro AKnave
  have cont := knave_said stA AKnave
  push_neg at cont
  have := cont.left
  contradiction

  knave_to_knight at stA
  simp [AKnight] at stA
  have BKnight := knight_said stA AKnight 
  constructor
  repeat assumption

