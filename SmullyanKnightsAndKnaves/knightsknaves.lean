import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic.Have

import SmullyanKnightsAndKnaves.logic
import SmullyanKnightsAndKnaves.settheory


    #check Finset.mem_insert
    #check Finset.mem_insert_of_mem
    #check Finset.mem_of_mem_inter_left
#check Finset.singleton_subset_iff
#check Finset.subset_of_eq
#check Finset.mem_singleton
#check Set.eq_singleton_iff_unique_mem

#check Set.mem_singleton_iff
#check Set.subset_insert_iff_of_not_mem

#check Finset.mem_singleton
#check Finset.mem_singleton_self

-----------

-- coe
#check Set.toFinset

#check Finset.toSet 

    #check Finset.coe_inj
    #check Finset.coe_inter
    #check Finset.coe_empty
#check Set.mem_toFinset

--      #check Finset.instCoeTCFinsetSet
      #check Finset.mem_coe
      #check Finset.coe_inj
      #check Finset.mem_coe.mpr 
      #check Finset.mem_coe.symm 
      #check Finset.mem_def.mp 
        #check Set.mem_toFinset
        #check Set.toFinset
#check Finset.coe_inj.symm
#check Finset.coe_inter
#check Finset.coe_empty

-- two options
#check Finset.toSet -- natural way
#check Set.toFinset -- needs fintype instance
#check Fintype
-- to sort out

#check Set.mem_univ
--theorem univ_iff_all
--{K : Type}
--  (inst : Fintype K) (inst2 : DecidableEq K) {A B C : K}   : Finset.univ = ({A,B,C} : Finset K) ↔  ∀ (x : K), x = A ∨ x = B ∨ x = C:= by
example {K : Type} (A B C: K) ( all : ∀(x : K), x = A ∨ x = B ∨ x = C) : @Set.univ K = {A,B,C} := by
  
 -- unfold Set.univ

  exact (Set.eq_univ_of_univ_subset fun ⦃a⦄ a_1 => all a).symm

  --apply Set.ext 
  --intro x
  --constructor
  --sorry
  --sorry

  --· intro xUniv
  --  by_contra
  --· exact fun a => trivial
---------------------------
example {K : Type} {A B C : K} (S : Set K) (h : S ⊆ {A,B,C}) (h': A ∉ S) : S ⊆ {B,C} := by
  exact (Set.subset_insert_iff_of_not_mem h').mp h

-- ----------------------

#check Finset.eq_iff_card_ge_of_superset
-- A ∈ S and S.card=1 , so S={A}
example {K : Type}
{A : K} {S : Finset K } 
{L : Finset K} {sub : S ⊆ L} : S.card ≤ L.card := by 
  exact Finset.card_le_card sub


#check Insert
#check Set.univ



-- can use to intuitively explain other things like x ∈ {A} means x=A etc.. start from it and then say more generally ...
-- mem1_iff_or for x ∈ {A}
-- mem2_iff_or for x ∈ {A,B} , can use repeat rw way

-- try using Set.univ as an axiom instead and see if there are any advantages
#check Finset.univ

#check Finset.mem_union
-------------
-- using simp , experiment with simp_rw

#check not_iff_not
#check not_iff
#check not_iff_self



#check Set.mem_compl
  #check Set.mem_compl_iff
  #check Set.inter_eq_compl_compl_union_compl





--theorem mem_iff_or_finset 
--
--{K : Type}
--{inst : DecidableEq K} 
--{A B C: K} {x : K} : x ∈ ({A,B,C} : Finset K) ↔  x = A ∨ x =B ∨ x = C := by


theorem IamKnave
{Inhabitant : Type}
  {A : Inhabitant}
  [inst : DecidableEq Inhabitant]
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
(h : Knight ∩ Knave = ∅ )
(h1 : A ∈ Knight ∨ A ∈ Knave )
(stA : A ∈ Knight  ↔ (A ∈ Knave) )
  : False := by

  {
    rcases h1 with AKnight|AKnave

    · have := stA.mp AKnight
      exact disjoint h AKnight this

    · have := stA.mpr AKnave
      exact disjoint h this AKnave
  }

theorem IamKnaveIffFalse
{Inhabitant : Type}
{A : Inhabitant}
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
  (h : (Knight ∩ Knave) = ∅)
  (Or : (A ∈ Knight ∨ A ∈ Knave))
: False ↔  (A ∈ Knight  ↔ (A ∈ Knave))  
   := by
    constructor
    exact fun a => a.elim
    exact IamKnave h Or 

--inductive type interpretation?
--variable (Inhabitant : Type)
--#check (Sum Inhabitant Inhabitant)
--variable (A : Sum Knight Knave)
--variable (B : Knight)

