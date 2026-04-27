-- file which contains knights and knaves problems we made up.

import SmullyanKnightsAndKnaves.knightsknaves_3
/-
"
A : All of us are knights
B: Exactly one of us is a knave
"
-/

open Inhabitant

#check Set.eq_singleton_iff_unique_mem
#check Finset.eq_singleton_iff_unique_mem
#check Set.nonempty_iff_eq_singleton
#check Finset.nonempty_iff_eq_singleton_default
#check Set.nonempty_iff_eq_singleton_default
example {K : Type} {S : Set K}
{A : K}
{h : S = {A}}
: A ∈ S := (Set.eq_singleton_iff_unique_mem.mp h).left

#check and_imp
#check imp_and
#check Set.mem_singleton_iff
example {K : Type} {S : Set K}
{A : K}
: S = {A} →
 A ∈ S := by
 grind only [Set.eq_singleton_iff_unique_mem]


#check Finset.eq_singleton_iff_unique_mem
example {K : Type} {S : Finset K}
{A : K}
{h :  S = {A}}
: A ∈ S := by
  #check Finset.coe_eq_singleton
  simp only [Finset.coe_eq_singleton.symm] at *
  #check Finset.coe_eq_singleton
  simp? at *
  #check Finset.toFinset_coe
  grind only [Finset.eq_singleton_iff_unique_mem]

example
{stA : A ∈ Knight ↔ (Knight={A,B}) }
{stB: B ∈ Knight ↔  (Knave={A} ∨ Knave={B}) }
  : A ∈ Knave := by

  {
    rcases KorKn B with BKnight|BKnave
    · have oneknave := stB.mp BKnight
      rcases oneknave with KA|KB
      · rw [KA]
        simp
      · 
        have BKnave : B ∈ Knave 
        rw [KB]
        simp
        exfalso
        contradiction
    · by_contra AKnight
      knight_interp at AKnight
      have KAB := stA.mp AKnight
--      #check Finset.eq_of_not_mem_of_mem_insert
      #check Finset.erase_eq_iff_eq_insert
      #check Finset.insert_eq
      -- Knight = {A,B} ∧ all ↔ A ∈ Knight ∧ B ∈ Knight 
      -- Knight = {A,B} → A ∈ Knight ∧ B ∈ Knight

      have : Knight={A,B} → B ∈ Knight := by
        intro h'
        rw [h']
        simp
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

  knight_or_knave A with h_1 h_2
  · left
    exact stB2.mp h_1
  · have BnKnight := stAn.mp h_2
    simp [BnKnight] at stCn
    have AKnave := h_2
    knight_interp at h_2
    have CKnave := stCn.mpr h_2
    right
    knave_interp at BnKnight
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
  knight_or_knave A with AKnight AKnave 
  have BKnight := stA.mp AKnight
  simp [AKnight] at stC
  left
  apply Finset.Subset.antisymm
  by_universe
  intro x h
  simp at h
  all_cases_satisfy_goal h

  have BKnave := stAn.mp AKnave
  knight_interp at AKnave
  simp [AKnave,BKnave] at stCn
  right
  apply Finset.Subset.antisymm
  by_universe
  intro x h
  simp at h
  knave_interp at AKnave
  knave_interp at BKnave
  all_cases_satisfy_goal h
