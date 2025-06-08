
import SmullyanKnightsAndKnaves.knightsknaves
variable { K : Type}
example [inst : DecidableEq K] (A B C : K)
--  (AneB : A ≠ B)
--  (BneC : B ≠ C)
--  (AneC : A ≠ C)
  (Knight : Finset K ) (Knave : Finset K)
  {Normal : Finset K}
--{hK : Finset Knight}
--{hKn : Finset Knave}
--{hN : Finset Normal}
--{finKnight : Fintype Knight}
--{finKnave : Fintype Knave}
--{finNormal : Fintype Normal}
--{OneKnight : Finset.card ( Knight) =1 }
--{OneKnave : Finset.card Knave =1 }
--{OneNormal : Finset.card Normal =1 }
{hKKn : Knight ∩ Knave = ∅ }
{hKN : Knight ∩ Normal = ∅ }
{hKnN : Knave ∩ Normal = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave ∨ A ∈ Normal }
{h2 : B ∈ Knight ∨ B ∈ Knave ∨ B ∈ Normal }
{h3 : C ∈ Knight ∨ C ∈ Knave ∨ C ∈ Normal}
{stA : A ∈ Knight → (B ∈ Knight) } 
{stAn : A ∈ Knave → ¬ (B ∈ Knight) }
{stB : B ∈ Knight → (A ∉ Knight)}
{stBn : B ∈ Knave → ¬(A ∉ Knight)}
-- Prove that at least one of them is telling the truth, but is not 
--a knight. 
: (A ∉ Knight ∧ B ∈ Knight) ∨ (B ∉ Knight ∧ A ∉ Knight) := by 
  have AnKnight : A ∉ Knight := by
    intro AKnight
    have := stA AKnight
    have := stB this
    contradiction

  rcases h2 with BKnight|BKnaveNormal
  · left
    constructor
    assumption
    assumption
  · rcases BKnaveNormal with BKnave|BNormal 
    · have := stBn BKnave
      contradiction

    · have :=inright_notinleft hKnN BNormal
      right
      constructor
      have := inright_notinleft hKN BNormal
      assumption
      assumption
