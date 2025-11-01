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

example
{stA : A ∈ Knight  ↔ (Knave= ({A,B,C} : Finset Inhabitant)) }
{stAn : A ∈ Knave ↔ ¬ (Knave = {A,B,C}) }
{stB : B ∈ Knight ↔ Knave = {A} ∨ Knave = {B} ∨ Knave = {C}}
{stBn : B ∈ Knave ↔ ¬ (Knave = {A} ∨ Knave = {B} ∨ Knave = {C})}
{all2: 
 ∀ (x : Inhabitant), x = A or x = B or x = C}
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
    set_knight_to_knave
    intro CKnave
    rcases oneKnave with s|s|s 
    rw [s] at CKnave
    simp at CKnave
    symm at CKnave
    contradiction

    rw [s] at CKnave
    simp at CKnave
    symm at CKnave
    contradiction

    rw [s] at AKnave
    simp at AKnave
    contradiction

  ·
    set_knight_to_knave
    intro CKnave
    apply notallKnave
    apply Finset.Subset.antisymm
    · by_universe
      assumption
       


    · -- trivial
      #check C
      intro a
      intro h
      mem_set at h
      -- take cases and done

      -- special angle bracket notation would rewrite, why is that
      --rcases h with h1|h2|h3

      sorry
