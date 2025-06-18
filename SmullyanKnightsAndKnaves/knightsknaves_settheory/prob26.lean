import SmullyanKnightsAndKnaves.knightsknaves

open settheory_approach

  #check disjoint
  #check DecidableEq 
  #check inst
  #check Inhabitant
example
{inst : DecidableEq Inhabitant}
{A B C : Inhabitant}
{hB : B ∈ Knight ↔ (A ∈ Knight ↔ A ∈ Knave)}
{hC : C ∈ Knight ↔ B ∈ Knave}
: B ∈ Knave ∧ C ∈ Knight := by
  have BKnave : B ∈ Knave
  #check inright_notinleftIff
  set_knave_to_knight B
  intro BKnight
  have hA := hB.mp BKnight
  exact IamKnave hA

  have CKnight := hC.mpr BKnave

  constructor
  assumption
  assumption
