--import SmullyanKnightsAndKnaves.knightsknaves
import SmullyanKnightsAndKnaves.knightsknaves_3

--open settheory_approach

--variable [DecidableEq Inhabitant]
open Inhabitant


#check Finset.mem_insert
#check Finset.mem_insert_self
#check Finset.mem_insert
#check Finset.mem_insert_of_mem
#check Finset.mem_erase

macro "mem_mem" : tactic =>
  `(tactic|
  repeat
  (
   first
   | apply Finset.mem_insert_self
   | apply Finset.mem_insert_of_mem
  )

  )
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
