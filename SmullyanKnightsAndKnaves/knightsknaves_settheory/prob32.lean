---- adapat to problems with only 2 inhabitants

--"
--Suppose instead, A and B say the following:
--A: All of us are knaves.
--B: Exactly one of us is a knave.
--Can it be determined what B is? Can it be determined what C is?
--"
import SmullyanKnightsAndKnaves.knightsknaves

-- exactly one of us is a knave
-- this can be represented as Knave = {A} ∨ Knave = {B} ∨ Knave = {C}
set_option push_neg.use_distrib true

open settheory_approach

--A:All of us are knaves.
--B: Exactly one of us is a knave.
variable [DecidableEq Inhabitant]
example
{stA : A ∈ Knight ↔ (allKnave) }
{stAn : A ∈ Knave ↔ ¬ (allKnave) }
{stB: B ∈ Knight ↔ oneKnave }
{stBn: B ∈ Knave ↔ ¬ (oneKnave) }
  : A ∈ Knave ∧ C ∈ Knight := by
  {
--A: All of us are knaves.
--B: Exactly one of us is a knave.
  have AKnave : A ∈ Knave := by
    by_contra AKnight
    set_knave_to_knight at AKnight
    have knaves := stA.mp AKnight
    contradiction

  have notallknaves := stAn.mp AKnave
  constructor
  assumption
  set_knight_or_knave B with BKnight BKnave
  ·
    have oneKn := stB.mp BKnight 
    unfold oneKnave at oneKn
    simp [AKnave,BKnight,inleft_notinrightIff] at oneKn
    set_knight_to_knave 
    assumption
  ·
    unfold allKnave at notallknaves
    simp [AKnave,BKnave] at notallknaves
    set_knight_to_knave
    assumption
  }

#check not_eq_singleton_of_not_mem

theorem not_eq_singleton_already_full 
{K : Type}
{A B: K}
{Knave : Finset K}
(AneB : A ≠ B)
(AKnave : A ∈ Knave)

: Knave ≠ {B} := by
        intro knaveB 
        rw [knaveB] at AKnave
        #check Finset.mem_singleton
        rw [Finset.mem_singleton] at AKnave
        contradiction

#check card_eq_one_iff_singletons
#check card_eq

example
{stA : A ∈ Knight  ↔ (Knave= {A,B,C}) }
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
  is_mem
  contradiction

  have notallKnave := stAn.mp AKnave

  constructor
  assumption
  set_knight_or_knave B with BKnight BKnave
  · have oneKnave := stB.mp BKnight
    -- replace rcases with just proving negation of the other disjuncts and simplifying
    rcases oneKnave with h|h|h

    set_knight_to_knave
    intro CKnave
    rw [h] at CKnave
    contradiction

    set_knight_to_knave
    intro CKnave
    rw [h] at CKnave
    contradiction


    set_knight_to_knave
    intro CKnave
    rw [h] at CKnave
    contradiction
  · have notsingleknave := stBn.mp BKnave
    simp at notsingleknave 
    set_knight_to_knave
    intro CKnave
    contradiction

#check Finset.ssubset_iff_subset_ne.mpr 

#check full2
#check Finset.card_eq_two
