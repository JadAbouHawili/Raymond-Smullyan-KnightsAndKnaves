import SmullyanKnightsAndKnaves.knightsknaves

/-
Again three people A, B, and C. A says "B and C are of the 
same type." Someone then asks C, "Are A and B of the 
same type?" 
What does C answer? 
-/
-- statement of the problem makes the goal impossible to formalize and represent
example
  {Inhabitant : Type}
  {A B C : Inhabitant}
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{Or : ∀(x : Inhabitant), x ∈ Knight ∨ x ∈ Knave}
{stA : A ∈ Knight  ↔ (B ∈ Knight ∧ C ∈ Knight ∨ B ∈ Knave ∧ C ∈ Knave) }
{stAn : A ∈ Knave ↔ ¬ (B ∈ Knight ∧ C ∈ Knight ∨ B ∈ Knave ∧ B ∈ Knave) }
-- this type doesn't work, it can't work, find a way to modify the problem
  : A ∈ Knight ∧ B ∈ Knight ∨ A ∈ Knave ∧ B ∈ Knave := by

  {
    rcases (Or A) with AKnight|AKnave
    · have BCsame := stA.mp AKnight
      rcases (Or C) with CKnight|CKnave 
      · have CnKnave := inleft_notinright h CKnight 
      -- A and B are same type
        simp [CKnight,CnKnave] at BCsame
        left
        constructor
        assumption
        assumption


      · -- A and B are of different type
        sorry
    · sorry
  }


