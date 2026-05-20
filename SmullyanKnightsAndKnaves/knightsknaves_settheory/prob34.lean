import SmullyanKnightsAndKnaves.knightsknaves_3

/-
We again have three inhabitants, A, B, and C, each of whom
is a knight or a knave. Two people are said to be of the same
type if they are both knights or both knaves. A and B make
the following statements:
A: B is a knave.
B: A and C are of the same type.
What is C?
-/


open Inhabitant

/-
not ideal
-/
example
{stA : A ∈ Knight  ↔ (B ∈ Knave) }
{stAn : A ∈ Knave ↔ ¬ (B ∈ Knave) }
{stB: B ∈ Knight ↔ (A ∈ Knight ∧ C ∈ Knight ∨ A ∈ Knave ∧ C ∈ Knave) }
{stBn: B ∈ Knave ↔ ¬ (A ∈ Knight ∧ C ∈ Knight ∨ A ∈ Knave ∧ C ∈ Knave) }
  : C ∈ Knave  := by
  {
   knight_or_knave A with AKnight AKnave
   · have BKnave := stA.mp AKnight
     have BCnotsametype := stBn.mp BKnave
     simp only [not_or,not_and_or] at BCnotsametype
     have AC:= BCnotsametype.left
     simp [AKnight] at AC
     knave_interp at AC
     assumption

   · have BKnight := stAn.mp AKnave
     knight_interp at BKnight
     have AC := stB.mp BKnight
     knave_interp at AC
     simp [AKnave] at AC
     assumption
  }

/-
A: B is a knave.
B: A and C are of the same type.

ideal
-/
example
{stA : A ∈ Knight  ↔ (B ∈ Knave) }
{stB: B ∈ Knight ↔ (A ∈ Knight ↔ C ∈ Knight) }
  : C ∈ Knave  := by
    knight_or_knave A with AKnight AKnave

    have BKnave := stA.mp AKnight 
    knave_interp at stB 
    have notAsameC := stB.mp BKnave
    knave_interp at AKnight 
    simp [AKnight] at notAsameC
    assumption

    knave_interp at stA 
    have BnKnave := stA.mp AKnave 
    knave_interp at stB
    simp [BnKnave] at stB
    rw [not_iff_not] at stB 
    have := stB.mp AKnave
    assumption
