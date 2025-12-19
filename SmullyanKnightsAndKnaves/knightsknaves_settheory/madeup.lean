-- file which contains knights and knaves problems we made up.

import SmullyanKnightsAndKnaves.knightsknaves
import SmullyanKnightsAndKnaves.knightsknaves_3
/-
"
A : All of us are knights
B: Exactly one of us is a knave
"
-/

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
    rcases KorKn B with BKnight|BKnave
    · have oneknave := stB.mp BKnight
      rcases oneknave with KA|KB
      · rw [KA]
        mem_finset
      · 
        have BKnave : B ∈ Knave 
        rw [KB]
        mem_finset
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
        mem_finset
      have BKnight := this KAB
      contradiction
}
#check Finset.insert_eq_of_mem

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


variable [DecidableEq Inhabitant]
variable [Fintype Inhabitant]

/-
A says B is a knight
B says all of us are knights
C says A  is a kngiht or B is a knight
-/
example
{stA : A ∈ Knight ↔ (B ∈ Knight) }
{stAn : A ∈ Knave ↔ ¬ (B ∈ Knight) }
{stB : B ∈ Knight ↔Knight={A,B,C}}
{stBn : B ∈ Knave ↔ ¬Knight={A,B,C}
}
{stC : C ∈ Knight ↔ A ∈ Knight ∨ B ∈ Knight}
{stCn : C ∈ Knave ↔ ¬ (A ∈ Knight ∨ B ∈ Knight)}
: Knight={A,B,C} ∨ Knave={A,B,C}:= by
  set_knight_or_knave A with AKnight AKnave 
  have BKnight := stA.mp AKnight
  simp [AKnight] at stC
  left
  apply Finset.Subset.antisymm
  by_universe
  intro x h
  mem_finset at h
  rcases h with h|h|h <;>  (rw [h]; assumption)

  have BKnave := stAn.mp AKnave
  set_knave_to_knight at AKnave
  simp [AKnave,BKnave] at stCn
  right
  apply Finset.Subset.antisymm
  by_universe
  intro x h
  mem_finset at h
  set_knight_to_knave at AKnave
  set_knight_to_knave at BKnave
  rcases h with h|h|h <;>  (rw [h]; assumption)
