-- file which contains knights and knaves problems we made up.

import SmullyanKnightsAndKnaves.knightsknaves
import SmullyanKnightsAndKnaves.knightsknaves_3
/-
"
A : All of us are knights
B: Exactly one of us is a knave
"
-/

#check mem_of_eq_singleton
#check Set.eq_singleton_iff_unique_mem
#check Finset.eq_singleton_iff_unique_mem
open settheory_approach
example {K : Type} {S : Set K}
{A : K}
{h : {A} = S}
: A ∈ S := by
  exact (Set.eq_singleton_iff_unique_mem.mp h.symm).left

example
  {inst : DecidableEq Inhabitant}
{all2 : ∀ (x : Inhabitant), x = A ∨ x = B}
{stA : A ∈ Knight ↔ (Knight={A,B}) }
{stAn : A ∈ Knave ↔ ¬ (Knight={A,B}) }
{stB: B ∈ Knight ↔  (Knave={A} ∨ Knave={B}) }
{stBn: B ∈ Knave ↔  ¬ (Knave={A} ∨ Knave={B}) }
  : A ∈ Knave := by

  {
    rcases KorKn with BKnight|BKnave
    · have oneknave := stB.mp BKnight
      rcases oneknave with KA|KB
      · exact mem_of_eq_singleton KA
      · #check mem_of_eq_singleton
        have BKnave := mem_of_eq_singleton KB
        exfalso
        contradiction
    · by_contra AKnight
      set_knave_to_knight at AKnight
      have KAB := stA.mp AKnight
--      #check Finset.eq_of_not_mem_of_mem_insert
      #check Finset.erase_eq_iff_eq_insert
      #check Finset.insert_eq
      -- Knight = {A,B} ∧ all ↔ A ∈ Knight ∧ B ∈ Knight 
      -- Knight = {A,B} → A ∈ Knight ∧ B ∈ Knight

      have : Knight={A,B} → B ∈ Knight := by
        intro h'
        rw [h']
        exact mem2_iff_or_finset.mpr (all2 B)

      #check Finset.insert_eq_of_mem
      have BKnight := this KAB
      contradiction
  }

-- given a proof of p, goal is changed to ¬p
--absurd

/-
A says B is a knight
B says all of us are knights
C says A  is a kngiht or B is a knight
-/
example 
{inst : DecidableEq Inhabitant}
{Or : ∀(x : Inhabitant), x ∈ Knight ∨ x ∈ Knave}
{stA : A ∈ Knight ↔ (B ∈ Knight) }
{stAn : A ∈ Knave ↔ ¬ (B ∈ Knight) }
{stB : B ∈ Knight ↔ A ∈ Knight ∧ B ∈ Knight ∧ C ∈ Knight}
{stBn : B ∈ Knave ↔ ¬ (A ∈ Knight ∧ B ∈ Knight ∧ C ∈ Knight)}
{stC : C ∈ Knight ↔ A ∈ Knight ∨ B ∈ Knight}
{stCn : C ∈ Knave ↔ ¬ (A ∈ Knight ∨ B ∈ Knight)}
: A ∈ Knight ∧ B ∈ Knight ∧ C ∈ Knight ∨ A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave:= by 
  have stB2 := stB
  nth_rw 1 [stA.symm] at stB2 

  set_knight_or_knave A with h_1 h_2
  · left
    exact stB2.mp h_1
  · have BnKnight := stAn.mp h_2
    simp [BnKnight] at stCn
    have AKnave := h_2
    set_knave_to_knight at h_2
    have CKnave := stCn.mpr h_2
    right
    set_knight_to_knave at BnKnight
    exact And.intro AKnave (And.intro BnKnight CKnave)
