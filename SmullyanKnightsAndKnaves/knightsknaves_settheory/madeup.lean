import SmullyanKnightsAndKnaves.knightsknaves_3

open Inhabitant

#check Set.eq_singleton_iff_unique_mem
#check Finset.eq_singleton_iff_unique_mem
#check Finset.nonempty_iff_eq_singleton_default

#check Set.mem_singleton_iff
#check Finset.eq_singleton_iff_unique_mem
#check Finset.coe_eq_singleton
#check Finset.coe_eq_singleton
#check Finset.toFinset_coe

#check Finset.erase_eq_iff_eq_insert
#check Finset.insert_eq
#check Finset.insert_eq_of_mem

/-
A says B is a knight
B says all of us are knights
C says A  is a knight or B is a knight
-/
example
{stA : A ∈ Knight ↔ (B ∈ Knight) }
{stB : B ∈ Knight ↔ A ∈ Knight ∧ B ∈ Knight ∧ C ∈ Knight}
{stC : C ∈ Knight ↔ A ∈ Knight ∨ B ∈ Knight}
: A ∈ Knight ∧ B ∈ Knight ∧ C ∈ Knight ∨ A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave:= by
  have stB2 := stB
  nth_rw 1 [stA.symm] at stB2 

  knight_or_knave A with h_1 h_2
  · left
    exact stB2.mp h_1
  · knave_interp at stA
    have BnKnight := stA.mp h_2
    knave_interp at stC
    simp [BnKnight] at stC
    have AKnave := h_2
    have CKnave := stC.mpr h_2
    right
    exact And.intro AKnave (And.intro BnKnight CKnave)
