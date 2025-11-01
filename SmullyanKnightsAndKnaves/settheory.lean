import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Basic

import SmullyanKnightsAndKnaves.logic

infixr:35 " and " => And
infixr:30 " or  "  => Or

macro "mem_finset": tactic =>
  do`(tactic| repeat simp only [Finset.mem_insert,Finset.mem_singleton] )

macro "mem_finset" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
  do`(tactic| repeat simp only [Finset.mem_insert,Finset.mem_singleton] at $t1)

macro "mem_set": tactic =>
  do`(tactic| repeat simp only [Set.mem_insert,Set.mem_singleton] )
macro "mem_set" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
  do`(tactic| repeat simp only [Set.mem_insert,Set.mem_singleton] at $t1)


macro "is_mem2" : tactic =>
  do`(tactic| first |(apply Finset.mem_singleton_self) | (apply Finset.mem_insert_self) | apply Finset.mem_insert_of_mem)

--  a ∈ {a}
#check Finset.mem_singleton_self
-- a ∈ insert a s
#check Finset.mem_insert_self
-- a ∈ s → a ∈ insert b s
#check Finset.mem_insert_of_mem

macro "is_mem" : tactic =>
  do`(tactic | repeat is_mem2)


#check Finset.mem_inter.mpr
theorem disjoint_finset
{K : Type}
{inst : DecidableEq K}  {left : Finset K} {right : Finset K}
{A : K}
(h : left ∩ right = ∅ )
(hk : A ∈ left)
(hkn : A ∈ right)  : False := by 
  have := Finset.mem_inter_of_mem hk hkn
  rw [h] at this
  contradiction


macro_rules
| `(tactic| contradiction) => 
  do `(tactic |solve  | ( apply disjoint_finset ; repeat assumption ) )
theorem disjoint_set
{K : Type}
{left : Set K} {right : Set K}
{A : K}
(h : left ∩ right = ∅ )
(hk : A ∈ left)
(hkn : A ∈ right)  : False := by
  have := Set.mem_inter hk hkn
  rw [h] at this
  contradiction

macro_rules
| `(tactic| contradiction) => 
  do `(tactic |solve  | ( apply disjoint_set ; repeat assumption ) )


theorem inleft_notinright_finset
{K : Type}
{S S' : Finset K}
{inst : DecidableEq K}
{A : K}
(h : S ∩ S' = ∅ )
(h' : A ∈ S) : A ∉ S' := by
  intro a
  have := Finset.mem_inter_of_mem h' a
  rw [h] at this
  contradiction

theorem notinleft_inright
{K : Type}
{S S' : Finset K}
{A : K}
(SorS' : A ∈ S ∨ A ∈ S')
(h' : A ∉ S) : A ∈ S' := by
  exact notleft_right SorS' h'

theorem inright_notinleft_finset
{K : Type}
{S S' : Finset K}
{inst : DecidableEq K}
{A : K}
(h : S ∩ S' = ∅ )
(h' : A ∈ S') : A ∉ S := by
  intro a
  have := Finset.mem_inter_of_mem h' a
  rw [Finset.inter_comm] at h
  rw [h] at this
  contradiction

theorem notinright_inleft
{K : Type}
{S S' : Finset K}
{A : K}
(SorS' : A ∈ S ∨ A ∈ S')
(h' : A ∉ S') : A ∈ S := by
  exact notright_left SorS' h'

-------------------
theorem inleft_notinrightIff

{K : Type}
{S S' : Finset K}
{A : K}
{inst : DecidableEq K}
(h : S ∩ S' = ∅ )
(SorS' : A ∈ S ∨ A ∈ S')
: A ∈ S ↔  ¬(A ∈ S') := by
  constructor
  · exact inleft_notinright_finset h
  · exact notinright_inleft SorS'

theorem notinleft_inrightIff
{K : Type}
{S S' : Finset K}
{A : K}
{inst : DecidableEq K}
(h : S ∩ S' = ∅ )
(SorS' : A ∈ S ∨ A ∈ S')
: A ∉ S ↔  A ∈ S' := by
  constructor
  · exact notinleft_inright SorS'
  · exact inright_notinleft_finset h

theorem inright_notinleftIff
{K : Type}
{S S' : Finset K}
{A : K}
{inst : DecidableEq K}
(h : S ∩ S' = ∅ )
(SorS' : A ∈ S ∨ A ∈ S')
: A ∈ S' ↔  A ∉ S := by
  constructor
  · exact inright_notinleft_finset h
  · exact notleft_right SorS'

theorem notinright_inleftIff
{K : Type}
{S S' : Finset K}
{A : K}
{inst : DecidableEq K}
(h : S ∩ S' = ∅ )
(SorS' : A ∈ S ∨ A ∈ S')
 : A ∉ S' ↔  A ∈ S := by
  constructor
  · exact notinright_inleft SorS'
  · exact inleft_notinright_finset h

theorem univ_iff_all {K : Type} {inst : Fintype K} {inst2 : DecidableEq K} {A B C : K}   : Finset.univ = ({A,B,C} : Finset K) ↔  ∀ (x : K), x = A ∨ x = B ∨ x = C:= by 
--  #check Finset.toSet Finset.univ
--  #check Finset.coe_inj
--  rw [Finset.coe_inj.symm]
--  #check Finset.coe_inj
--  #check Finset.toSet
--  have : Finset.univ = {A,B,C} ↔ Set.univ = {A,B,C} := by 
--    constructor
--    · intro Fu
--      rw [Fu]
--    · sorry

  constructor
  · intro U
    intro x
    #check Finset.mem_univ
    have : x ∈ Finset.univ := Finset.mem_univ x 
    rw [U] at this
    #check instDecidableEqBool
    #check Finset.mem_insert_of_mem
    #check Finset.mem_insert
    rw [Finset.mem_insert] at this
    rw [Finset.mem_insert] at this
    rw [Finset.mem_singleton] at this
    assumption
  · intro U
    apply Finset.ext
    intro a
    constructor
    · intro aU
      rcases U a with h|h
      · rw [h]
        exact Finset.mem_insert_self A {B, C}
      · rcases h with h_1|h_1
        · rw [h_1]  
          #check Finset.mem_insert_of_mem
          apply Finset.mem_insert_of_mem
          exact Finset.mem_insert_self B {C}
        · rw [h_1]
          apply Finset.mem_insert_of_mem
          apply Finset.mem_insert_of_mem
          exact Finset.mem_singleton.mpr rfl

    · exact fun a_1 => Finset.mem_univ a


theorem set_subset_univ  
{Inhabitant : Type}
{inst : DecidableEq Inhabitant}
{A B C : Inhabitant}

{all2 : ∀ (x : Inhabitant), x = A ∨ x = B ∨ x = C}
 {S : Finset Inhabitant}
 {inst : Fintype Inhabitant}
: S ⊆ ({A,B,C} : Finset Inhabitant) := by 
  have all := all2
  #check univ_iff_all
  rw [(univ_iff_all).symm] at all
  rw [←all]
  exact Finset.subset_univ S

macro "by_universe" : tactic =>
  `(tactic| (apply set_subset_univ; assumption))

