import SmullyanKnightsAndKnaves.knightsknaves
import SmullyanKnightsAndKnaves.knightsknaves_3

set_option push_neg.use_distrib true

open settheory_approach

variable [Fintype Inhabitant]
variable [DecidableEq Inhabitant]
--A:All of us are knaves.
--B: Exactly one of us is a knave.
example
{stA : A ∈ Knight ↔ (allKnave) }
{stAn : A ∈ Knave ↔ ¬ (allKnave) }
{stB: B ∈ Knight ↔ oneKnave }
{stBn: B ∈ Knave ↔ ¬ (oneKnave) }
  : A ∈ Knave ∧ C ∈ Knight := by
  {
  have AKnave : A ∈ Knave := by
    by_contra AKnight
    set_knave_to_knight at AKnight
    have knaves := stA.mp AKnight
    have AKnave := knaves.left
    contradiction

  have notallknaves := stAn.mp AKnave
  constructor
  assumption
  set_knight_or_knave B with BKnight BKnave
  ·
    have oneKn := stB.mp BKnight 
    unfold oneKnave at oneKn
    simp [AKnave,BKnight,knight_notknaveIff] at oneKn
    set_knight_to_knave 
    assumption
  ·
    unfold allKnave at notallknaves
    simp [AKnave,BKnave] at notallknaves
    set_knight_to_knave
    assumption
  }

-- if A subset B then card A <= card B
example (A B : Finset Inhabitant) (h : A ⊆ B) : A.card ≤ B.card := by
  exact Finset.card_le_card h


-- two sets of the same cardinality are subsets which means they are equal
theorem eq_of_subset_card_eq {A B : Finset Inhabitant} (h1 : A ⊆ B) (h2 : A.card = B.card) : A = B := by
  #check Finset.eq_iff_card_ge_of_superset
  #check Finset.eq_iff_card_le_of_subset
  #check Finset.subset_iff_eq_of_card_le
  have := Finset.eq_iff_card_ge_of_superset h1
  simp [h2] at this
  symm at this
  assumption

--A:All of us are knaves.
--B: Exactly one of us is a knave.
example 
{stA : A ∈ Knight ↔ Knave.card =3}
{stAn : A ∈ Knave ↔ Knave.card ≠ 3}
{stB : B ∈ Knight ↔ Knave.card = 1}
{stBn : B ∈ Knave ↔ Knave.card ≠ 1}
: A ∈ Knave ∧ C ∈ Knight := by
  -- create a custom tactic that would transform stA into stAn and vice versa
  have AKnave : A ∈ Knave
  set_knave_to_knight
  intro AKnight
  have allKnave := stA.mp AKnight
  have Knavesubset: Knave ⊆ {A,B,C}
  by_universe
  have KnaveAll: Knave = {A,B,C}
  apply eq_of_subset_card_eq Knavesubset
  -- doing simp would just work
  simp only [allKnave]
  symm
  rw [Finset.card_eq_three] 
  use A
  use B
  use C
  simp [AneB,AneC,BneC]

  have AKnave : A ∈ Knave
  rw [KnaveAll] ; mem_finset
  contradiction

  constructor
  assumption

  set_knight_to_knave
  intro CKnave
  set_knight_or_knave B with BKnight BKnave
  have oneKnave := stB.mp BKnight
  rw [Finset.card_eq_one] at oneKnave 
  have ⟨a,ha⟩ := oneKnave 
  rw [ha] at AKnave
  rw [ha] at CKnave
  mem_finset at AKnave
  mem_finset at CKnave
  rw [←CKnave] at AKnave
  contradiction
  /-
  have knaveSub : {A,C} ⊆ Knave
  intro x h
  mem_finset at h
  rcases h with h|h
  rw [h] ; assumption
  rw [h] ; assumption

  have : 2 ≤ Knave.card 
  #check Finset.card_le_card
  have := Finset.card_le_card knaveSub
  have : ({A,C} : Finset Inhabitant).card = 2
  rw [Finset.card_eq_two]
  use A
  use C
  constructor
  exact AneC
  trivial
  rw [←this] ; assumption
  
  rw[oneKnave] at this ; contradiction
  -/

  have : Knave.card=3
  rw [Finset.card_eq_three]
  use A,B,C
  simp
  #check eq_of_subset_card_eq
  apply Finset.Subset.antisymm
  by_universe
  intro x h
  mem_finset at h
  rcases h with h|h|h <;> simp only [h, AKnave, BKnave, CKnave]
  have := stAn.mp AKnave
  contradiction

example
{stA : A ∈ Knight  ↔ (Knave= ({A,B,C} : Finset Inhabitant)) }
{stAn : A ∈ Knave ↔ ¬ (Knave = {A,B,C}) }
{stB : B ∈ Knight ↔ Knave = {A} ∨ Knave = {B} ∨ Knave = {C}}
{stBn : B ∈ Knave ↔ ¬ (Knave = {A} ∨ Knave = {B} ∨ Knave = {C})}
  : A ∈ Knave ∧ C ∈ Knight := by
  have AKnave : A ∈ Knave
  set_knave_to_knight
  intro AKnight
  have allKnave := stA.mp AKnight
  have AKnave : A ∈ Knave
  rw [allKnave]
  mem_finset
  contradiction

  have notallKnave := stAn.mp AKnave

  constructor
  assumption

  set_knight_or_knave B with BKnight BKnave
  · have oneKnave := stB.mp BKnight
    set_knight_to_knave
    intro CKnave
    #check Finset.eq_iff_card_ge_of_superset
    #check Finset.eq_of_subset_of_card_le
    rcases oneKnave with s|s|s 
    rw [s] at CKnave
    mem_finset at CKnave
    contradiction

    rw [s] at CKnave
    mem_finset at CKnave
    contradiction

    rw [s] at AKnave
    mem_finset at AKnave
    contradiction

  ·
    set_knight_to_knave
    intro CKnave
    apply notallKnave
    apply Finset.Subset.antisymm
    · by_universe

    ·
      intro a
      intro h
      mem_finset at h
      -- take cases and done
      rcases h with h|h|h <;> (rw [h] ; assumption) --simp only [h, AKnave, BKnave, CKnave]
