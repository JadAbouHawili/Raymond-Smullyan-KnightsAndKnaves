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
      contradiction

    · have := stA.mpr AKnave
      contradiction
      --exact disjoint h this AKnave
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

#check univ_iff_all
theorem all_univ_subset
{Inhabitant : Type}
{inst2 : Fintype Inhabitant}
{inst : DecidableEq Inhabitant}
{A B C : Inhabitant}
{Knight : Finset Inhabitant}
{all : ∀ (x : Inhabitant), x = A ∨ x = B ∨ x = C}
: Knight ⊆ ({A,B,C} : Finset Inhabitant) := by 
    #check univ_iff_all  
    #check set_subset_univ
    have Ueq : Finset.univ ={A,B,C}:= (univ_iff_all).mpr all
    --have := univ_iff_all 
    rw [←Ueq]
    #check Finset.subset_univ
    exact Finset.subset_univ Knight
    --exact set_subset_univ
    /-
    have : Knight ⊆ {A,B,C} := by 
      intro x
      intro xK
      rcases all x with h_1|h_1
      · rw [h_1]
        exact Finset.mem_insert_self A {B, C}
      · rcases h_1 with h_2|h_2
        · rw [h_2]
          apply Finset.mem_insert_of_mem
          exact Finset.mem_insert_self B {C}
        · rw [h_2] 
          apply Finset.mem_insert_of_mem
          apply Finset.mem_insert_of_mem
          exact Finset.mem_singleton.mpr rfl
    assumption
    -/

#check inleft_notinrightIff
-- theorem used in simp would need arguments passed to it, change so that theorems used require fewer arguments
namespace Inhabitant
variable {Inhabitant : Type}
variable {Knight Knave : Finset Inhabitant}
def Knight2 := Finset Type
example : 2=2 := by 
  rfl
-- *
macro "set_knight_to_knave" "at" t1:Lean.Parser.Tactic.locationWildcard : tactic =>
do`(tactic| simp [inleft_notinrightIff] at $t1)
-- goal
macro "set_knight_to_knave" : tactic =>
do`(tactic| simp [inleft_notinrightIff])
-- hypothesis
macro "set_knight_to_knave" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic| simp [inleft_notinrightIff] at $t1)
--     (rw [inleft_notinrightIff] at BKnave <;> try assumption) ; simp at BKnave
#check inleft_notinrightIff
-- this would work for one hypothesis but what about for *,everything?
macro "set_knight_to_knave2" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic|
rw [inleft_notinrightIff] at $t1 <;> try assumption )

-- doesnt work
macro "set_knight_to_knave_newest" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic|
    (simp [inleft_notinrightIff] at $t1 ; try assumption) )
-- *
macro "set_knave_to_knight" "at" t1:Lean.Parser.Tactic.locationWildcard : tactic => 
do`(tactic| simp [inright_notinleftIff] at $t1)
macro "set_knave_to_knight" : tactic =>
do`(tactic| simp [inright_notinleftIff])
-- hypothesis
macro "set_knave_to_knight" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic| simp [inright_notinleftIff] at $t1)
end Inhabitant
