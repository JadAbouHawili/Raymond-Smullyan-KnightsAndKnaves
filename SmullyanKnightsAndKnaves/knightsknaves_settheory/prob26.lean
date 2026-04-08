import SmullyanKnightsAndKnaves.knightsknaves_3
open Inhabitant

#check IamKnaveIffFalse
example
{hB : B ∈ Knight ↔ (A ∈ Knight ↔ A ∈ Knave)}
{hC : C ∈ Knight ↔ B ∈ Knave}
: B ∈ Knave ∧ C ∈ Knight := by
  --rw [IamKnaveIffFalse] at hB
  have BKnave : B ∈ Knave
  knight_interp
  intro BKnight
  have hA := hB.mp BKnight
  exact IamKnave hA

  have CKnight := hC.mpr BKnave

  constructor
  assumption
  assumption
