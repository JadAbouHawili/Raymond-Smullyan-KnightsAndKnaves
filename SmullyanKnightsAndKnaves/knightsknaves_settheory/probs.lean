import SmullyanKnightsAndKnaves.knightsknaves

open Inhabitant
example
  -- A says B is a knight
  -- B says that A and B are of different type
  (stA : A ∈ Knight ↔ B ∈ Knight)
  (stB : B ∈ Knight ↔ A ∈ Knave)
  : A ∈ Knave ∧ B ∈ Knight := by
    rw [stB] at stA
    have:= IamKnaveIffFalse.mp stA
    contradiction

------------------------------------------------------------------------------------------------------------------------------------

--You have met a group of 3 islanders. Their names are Oberon, Tracy, and Wendy.
--
--    Tracy says: Wendy is untruthful.
--    Oberon says: Tracy is a knight and I am a knave.
--    Wendy says: Oberon is a knave.  Solution :     Because Oberon said 'Tracy is a knight and I am a knave,' we know Oberon is not making a true statement. (If it was true, the speaker would be a knight claiming to be a knave, which cannot happen.) Therefore, Oberon is a knave and Tracy is a knave.
--    All islanders will call a member of the opposite type a knave. So when Tracy says that Wendy is a knave, we know that Wendy and Tracy are opposite types. Since Tracy is a knave, then Wendy is a knight.
--For these reasons we know the knaves were Tracy and Oberon, and the only knight was Wendy.

example
  {Tracy Oberon Wendy: Inhabitant}
{stT : Tracy ∈ Knight  ↔ (Wendy ∈ Knave) }
{stO: Oberon ∈ Knight ↔ (Tracy ∈ Knight ∧ Oberon ∈ Knave) }
{stW : Wendy ∈ Knight ↔ Oberon ∈ Knave}
  : Tracy ∈ Knave ∧ Oberon ∈ Knave ∧ Wendy ∈ Knight := by
  {
    have OberonKnave : Oberon ∈ Knave := by {
      knight_interp
      intro OberonKnight
      have ⟨a,b⟩  := stO.mp OberonKnight
      apply disjoint OberonKnight
      assumption
    }
    have WendyKnight := stW.mpr OberonKnave
    have TracyKnave : Tracy ∈ Knave := by {
      knight_interp at stT
      knight_interp
      exact stT.mpr WendyKnight
    }

    constructor
    assumption
    constructor
    assumption
    assumption
  }
