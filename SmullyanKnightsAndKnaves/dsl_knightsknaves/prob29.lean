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
{A B : Islander}
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

example
  {Inhabitant : Type}
  {A B : Inhabitant}
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{stA : A ∈ Knight  ↔ (A ∈ Knave ∨ B ∈ Knight) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∨ B ∈ Knight) }
  : A ∈ Knight ∧ B ∈ Knight := by
  {
    have AnKnave : A ∉ Knave := by
      intro AKnave
      have Or : A ∈ Knave ∨ B ∈ Knight := by
      {
        left
        assumption
      }

      have := stAn.mp AKnave
      contradiction

    have AKnight := notright_left h1 AnKnave
    have BKnight := stA.mp AKnight
    constructor
    assumption
    exact notleft_right BKnight AnKnave
  }


