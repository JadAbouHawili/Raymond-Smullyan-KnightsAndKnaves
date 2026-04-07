import SmullyanKnightsAndKnaves.knightsknaves_3
open Inhabitant

example
{hB : B ∈ Knight ↔ (C ∈ Knight ↔ C ∈ Knave)}
{hC : C ∈ Knight ↔ B ∈ Knave}
: B ∈ Knave ∧ C ∈ Knight := by
  have BKnave : B ∈ Knave
  knight_interp
  intro BKnight
  have hA := hB.mp BKnight
  exact IamKnave hA

  have CKnight := hC.mpr BKnave

  constructor
  assumption
  assumption
