import SmullyanKnightsAndKnaves.knightsknaves
import SmullyanKnightsAndKnaves.knightsknaves_3

open settheory_approach

variable [DecidableEq Inhabitant]
example
{hB : B ∈ Knight ↔ (C ∈ Knight ↔ C ∈ Knave)}
{hC : C ∈ Knight ↔ B ∈ Knave}
: B ∈ Knave ∧ C ∈ Knight := by
  have BKnave : B ∈ Knave
  #check inright_notinleftIff
  set_knave_to_knight 
  intro BKnight
  have hA := hB.mp BKnight
  exact IamKnave hA

  have CKnight := hC.mpr BKnave

  constructor
  assumption
  assumption
