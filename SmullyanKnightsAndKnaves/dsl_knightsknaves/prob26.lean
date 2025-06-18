-- included as dsl_prob26
import SmullyanKnightsAndKnaves.dsl_knights_knaves
open Islander
example {A B C : Islander}
{hB : B said (A said A.isKnave)}
{hC : C said B.isKnave}
: B.isKnave and C.isKnight := by
  have BKnave : B.isKnave
  knave_to_knight
  intro BKnight
  have hA := knight_said hB BKnight
  exact dsl_iamknave hA

  have CKnight := said_knight hC BKnave

  constructor
  assumption
  assumption
