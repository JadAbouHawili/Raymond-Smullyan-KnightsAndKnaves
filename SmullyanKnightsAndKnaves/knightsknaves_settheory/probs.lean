import SmullyanKnightsAndKnaves.knightsknaves
open settheory_approach
#check 2=2
#check Finset.card_eq_one
example
{inst : DecidableEq Inhabitant}

  -- A says B is a knight
  -- B says that A and B are of different type
  (stA : A ∈ Knight ↔ B ∈ Knight)
  (stB : B ∈ Knight ↔ A ∈ Knave)
  (styn : B ∈ Knave ↔ ¬( (B ∈ Knight ∧ A ∈ Knave) ∨ (B ∈ Knave ∧ A ∈ Knight )) )
  : A ∈ Knave ∧ B ∈ Knight := by
    {

    --rw [not_or] at styn
    --rw [not_and_or] at styn
    --rw [not_and_or] at styn
    -- assuming x knight, we get y knight, then we get x and y are different type which is contradiction. so x knave which means y not knight i.e y knave.

    have AKnave : A ∈ Knave
    set_knave_to_knight
    intro AKnight
    have BKnight := stA.mp AKnight
    have AKnave := stB.mp BKnight
    contradiction_hyp AKnight AKnave

    have BKnight := stB.mpr AKnave
    constructor ; repeat assumption
    }

example
  {x y : Inhabitant}
  {inst : DecidableEq Inhabitant}
  (h2 : y ∈ Knight ∨ y ∈ Knave)
  -- x says y is a knight
  -- y says that x and y are of different type
  (stx : x ∈ Knight ↔ y ∈ Knight)
  (sty : y ∈ Knight ↔ x ∈ Knight ∧ y ∈ Knave ∨ x ∈ Knave ∧ y ∈ Knight)
  : x ∈ Knave ∧ y ∈ Knave := by

  rw [not_iff_not.symm] at stx

  rw [notinleft_inrightIff] at stx
  rw [notinleft_inrightIff] at stx
  rw [stx]
  simp

  have this:=h2

  rcases h2  with h_1|h_1
  rw [sty] at h_1
  rw [stx] at h_1
  nth_rw 1 [stx.symm] at h_1
  rw [inright_notinleftIff]  at h_1
  rw [inright_notinleftIff]  at h_1
  rcases h_1 with ⟨a,b⟩|⟨a',b'⟩
  contradiction
  contradiction

  assumption



--You have met a group of 3 islanders. Their names are Oberon, Tracy, and Wendy.
--
--    Tracy says: Wendy is untruthful.
--    Oberon says: Tracy is a knight and I am a knave.
--    Wendy says: Oberon is a knave.  Solution :     Because Oberon said 'Tracy is a knight and I am a knave,' we know Oberon is not making a true statement. (If it was true, the speaker would be a knight claiming to be a knave, which cannot happen.) Therefore, Oberon is a knave and Tracy is a knave.
--    All islanders will call a member of the opposite type a knave. So when Tracy says that Wendy is a knave, we know that Wendy and Tracy are opposite types. Since Tracy is a knave, then Wendy is a knight.
--For these reasons we know the knaves were Tracy and Oberon, and the only knight was Wendy.

open settheory_approach
example
  {Tracy Oberon Wendy: Inhabitant}
  {inst : DecidableEq Inhabitant}
{stT : Tracy ∈ Knight  ↔ (Wendy ∈ Knave) }
{stTn : Tracy ∈ Knave  ↔ ¬(Wendy ∈ Knave) }
{stO: Oberon ∈ Knight ↔ (Tracy ∈ Knight ∧ Oberon ∈ Knave) }
{stOn: Oberon ∈ Knave ↔ ¬(Tracy ∈ Knight ∧ Oberon ∈ Knave) }
{stW : Wendy ∈ Knight ↔ Oberon ∈ Knave}
{stWn : Wendy ∈ Knave ↔ ¬ (Oberon ∈ Knave)}
  : Tracy ∈ Knave ∧ Oberon ∈ Knave ∧ Wendy ∈ Knight := by
  {
    have OberonKnave : Oberon ∈ Knave := by {
      by_contra OberonKnight
      rw [notinright_inleftIff] at OberonKnight
      have := stO.mp OberonKnight
      exact disjoint OberonKnight this.right
    }
    have WendyKnight := stW.mpr OberonKnave
    have TracyKnave : Tracy ∈ Knave := by {
      rw [inleft_notinrightIff] at WendyKnight
      exact stTn.mpr WendyKnight
    }

    constructor
    assumption
    constructor
    assumption
    assumption
  }
