import SmullyanKnightsAndKnaves.knightsknaves_3

/-
(theorem that would rewrite Knave.card=3 to Knave = {A,B,C} which reduces to that style of representing the problem)
-/
/-
    works , but knave.card = 3 has issues. i could just give a theorem as an exit
-/

open Inhabitant


#check eq_or_ssubset_of_subset
#check subset_iff_ssubset_or_eq


example {S S' : Finset Inhabitant} (h : S ⊆ S') (h' : S ≠ S') : S ⊂ S' ∨ S = S' := by
  exact subset_iff_ssubset_or_eq.mp h

example {S S' : Finset Inhabitant} : S ⊆ S' ↔   S ⊂ S' ∨ S = S' := by
  exact subset_iff_ssubset_or_eq

   #check HasSubset.Subset.ssubset_of_ne 
   #check Finset.card_eq_succ_iff_cons
   #check Finset.ssubset_iff_subset_ne

example
{stA : A ∈ Knight  ↔ (Knave= {A,B,C}) }
{stAn : A ∈ Knave ↔ ¬ (Knave = {A,B,C}) }
{three : A ∈ Knight ↔ (Knave : Finset Inhabitant).card=3 }
{stB : B ∈ Knight ↔ (Knave : Finset Inhabitant).card=1 }
{AneC : A ≠ C}
(all : ∀ (x : Inhabitant), x = A ∨ x = B ∨ x = C)
  : A ∈ Knave ∧ C ∈ Knight := by
  #check Finset.card_eq_iff_eq_univ
  have : ((Knave : Finset Inhabitant).card = 3) ↔ (Knave = ({A,B,C} : Finset Inhabitant) ) := by
    #check eq_of_subset_of_card_eq 
    --have : Finset.univ ={A,B,C} := by rfl
    --have : Fintype.card Inhabitant = 3 := by exact Nat.eq_of_beq_eq_true rfl
    --rw [←this]
    --rw [Finset.card_eq_iff_eq_univ] 
    --rfl

    constructor
    intro card3
    #check Finset.eq_univ_of_card 
    have : {A,B,C} = (Finset.univ : Finset Inhabitant) := rfl
    rw [this]
    exact (Finset.card_eq_iff_eq_univ Knave).mp card3

  have AKnave : A ∈ Knave
  knight_interp
  intro AKnight
  have c := three.mp AKnight
  rw [Finset.card_eq_three] at c
  have ⟨x,y,z,xney,xnez,ynez,knaveEq⟩ := c 
  have : A ∈ Knave
  rw [knaveEq]
  repeat rw [Finset.mem_insert]
  rw [Finset.mem_singleton]
  sorry
  have : Knave ={A,B,C}

  sorry
  sorry
  constructor
  assumption
  knave_interp
  intro CKnave
  knight_or_knave B with BKnight BKnave
  · have one := stB.mp BKnight
    rw [Finset.card_eq_one] at one
    have ⟨a,singleton⟩ := one 
    rw [singleton] at AKnave 
    rw [singleton] at CKnave 
    rw [Finset.mem_singleton] at CKnave
    rw [Finset.mem_singleton] at AKnave
    rw [←CKnave] at AKnave
    contradiction
  ·
    have : Knave = {A,B,C}

    sorry
    #check Nat.two_le_iff
    sorry


#check Finset.card_ne_zero_of_mem

#check Finset.ssubset_iff_subset_ne.mpr

#check Finset.card_eq_two

#check Nat.two_le_iff
