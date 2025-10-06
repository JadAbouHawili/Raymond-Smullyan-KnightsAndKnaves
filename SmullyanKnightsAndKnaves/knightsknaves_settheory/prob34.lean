import SmullyanKnightsAndKnaves.knightsknaves
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
open settheory_approach

variable [DecidableEq Inhabitant]
example
{stA : A ∈ Knight  ↔ (B ∈ Knave) }
{stAn : A ∈ Knave ↔ ¬ (B ∈ Knave) }
{stB: B ∈ Knight ↔ (A ∈ Knight ∧ C ∈ Knight ∨ A ∈ Knave ∧ C ∈ Knave) }
{stBn: B ∈ Knave ↔ ¬ (A ∈ Knight ∧ C ∈ Knight ∨ A ∈ Knave ∧ C ∈ Knave) }
  : C ∈ Knave  := by
  {
   set_knight_or_knave A with AKnight AKnave
   · have BKnave := stA.mp AKnight
     have BCnotsametype := stBn.mp BKnave
     rw [not_or] at BCnotsametype
     rw [not_and_or] at BCnotsametype
     rw [not_and_or] at BCnotsametype
     have AC:= BCnotsametype.left
     rw [inright_notinleftIff]

     rw [inleft_notinrightIff] at AKnight
     rw [notinleft_inrightIff] at AC
     exact notleft_right AC AKnight
   · have BKnight := stAn.mp AKnave
     rw [notinright_inleftIff] at BKnight
     have AC := stB.mp BKnight
     rcases AC with h_1|h_2
     · rw [inright_notinleftIff] at AKnave
       exfalso
       exact AKnave h_1.left
     · exact h_2.right
  }
