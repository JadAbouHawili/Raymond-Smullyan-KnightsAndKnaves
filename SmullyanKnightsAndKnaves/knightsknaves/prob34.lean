import SmullyanKnightsAndKnaves.knightsknaves
import SmullyanKnightsAndKnaves.dsl_knights_knaves

example
  {Inhabitant : Type}
  {A B C : Inhabitant}
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave :Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{Or : ∀(x : Inhabitant), x ∈ Knight ∨ x ∈ Knave}
{stA : A ∈ Knight  ↔ (B ∈ Knave) }
{stAn : A ∈ Knave ↔ ¬ (B ∈ Knave) }
{stB: B ∈ Knight ↔ (A ∈ Knight ∧ C ∈ Knight ∨ A ∈ Knave ∧ C ∈ Knave) }
{stBn: B ∈ Knave ↔ ¬ (A ∈ Knight ∧ C ∈ Knight ∨ A ∈ Knave ∧ C ∈ Knave) }
  : C ∈ Knave  := by
  {
   rcases Or A with AKnight|AKnave
   · have BKnave := stA.mp AKnight
     have BCnotsametype := stBn.mp BKnave
     rw [not_or] at BCnotsametype
     rw [not_and_or] at BCnotsametype
     rw [not_and_or] at BCnotsametype
     have AC:= BCnotsametype.left
     rw [inright_notinleftIff (Or C) h]

     rw [inleft_notinrightIff (Or A) h] at AKnight
     rw [notinleft_inrightIff (Or A) h] at AC
     exact notleft_right AC AKnight
   · have BKnight := stAn.mp AKnave
     rw [notinright_inleftIff (Or B) h] at BKnight
     have AC := stB.mp BKnight
     rcases AC with h_1|h_2
     · rw [inright_notinleftIff (Or A) h] at AKnave
       exfalso
       exact AKnave h_1.left
     · exact h_2.right
  }
