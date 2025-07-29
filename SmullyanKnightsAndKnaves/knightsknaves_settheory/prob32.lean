import SmullyanKnightsAndKnaves.knightsknaves
import SmullyanKnightsAndKnaves.knightsknaves_3

set_option push_neg.use_distrib true
set_option trace.Meta.Tactic.simp true
set_option trace.Meta.Tactic.contradiction true
--set_option trace.Meta.synthInstance true

open settheory_approach
#check all
#help option

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
--A: All of us are knaves.
--B: Exactly one of us is a knave.
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

    #check Nat.two_le_iff
    rw [s] at AKnave
    simp at AKnave
    contradiction

    /-
    works , but knave.card = 3 has issues. i could just give a theorem as an exit
    have : 2 ≤ Knave.card  := by
        have : {A,C} ⊆ Knave := by
          intro a aIn
          rw [Finset.mem_insert] at aIn
          rw [Finset.mem_singleton] at aIn
          rcases aIn with h|h
          rw [h] ; assumption
          rw [h] ; assumption
        #check Finset.card_le_card
        have := Finset.card_le_card this
        have last : ({A,C}:Finset Inhabitant).card = 2 := by
          rw [Finset.card_eq_two] 
          use A
          use C
          constructor 
          exact AneC
          rfl
        rw [last] at this
        assumption
        /-
        second approach must be studied , i was trying second approach to get away from using AneC but there is no way around that...
        -/
    have : 2 ≤ Knave.card  := by
        #check Nat.two_le_iff
        #check Nat.two_le_iff  Knave.card
        rw[ Nat.two_le_iff  Knave.card]
        constructor
        · exact Finset.card_ne_zero_of_mem AKnave
        · intro cardone
          rw [cardone] at this
          contradiction
    rcases oneKnave with single|single|single
    ·
      rw [single] at CKnave
      rw [Finset.mem_singleton] at CKnave
      symm at CKnave
      #check AneC
      -- contradiction doesn't work without this step
      have : A ≠ C := AneC
      contradiction
    · sorry
    · sorry
-/

  · --have notsingleknave := stBn.mp BKnave

    --simp at notsingleknave 
    set_knight_to_knave
    intro CKnave
    #check Finset.Subset.antisymm
    apply notallKnave
    apply Finset.Subset.antisymm
    · -- needs a tactic that would just do it...
      #check univ_iff_all
      --have := univ_iff_all.mpr all
      --rw [univ_iff_all.symm] at all 
      --#check Eq.symm all
      -- custom tactic and have it hide Fintype Inhabitant...
      -- make a by universe tactic
      apply set_subset_univ 
      assumption
      exact all

    · -- trivial
      #check C
      intro a
      intro h
      mem_set at h
      -- take cases and done
      sorry
