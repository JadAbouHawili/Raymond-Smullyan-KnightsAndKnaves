import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Basic

import SmullyanKnightsAndKnaves.logic

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.DeriveFintype

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic



open Finset

#check eq_univ_iff_forall


section

variable {K : Type} [DecidableEq K] 
variable (A B C : K)
variable (all : ∀ x : K, x = A ∨ x = B ∨ x = C)
----example :
--  (Finset.univ : Finset K) = ({A,B,C} : Finset K) := by
--  ext x
--  simp [Finset.mem_univ, all]


-- construct an actual instance using the axiom
instance : Fintype K :=
{ elems := ({A, B, C} : Finset K),
  complete := by
    intro x
    rcases all x with rfl | rfl | rfl
    <;> simp }
example : Finset K := by
  let foo := instFintype_smullyanKnightsAndKnaves A B C all -- add instance manually because
                                    -- typeclass inference won't do it
  let bar : Finset K := Finset.univ
  have : Finset.univ = {A,B,C} := by
    /-
    just having variable [Fintype K]
    ext x
    simp
    exact all x
    -/
    rfl

  exact bar
end






--works
section
-- would solve problems?
class HasThreeElems (K : Type*) where
  A : K
  B : K
  C : K
  all : ∀ x : K, x = A ∨ x = B ∨ x = C

variable {K : Type*} [DecidableEq K] [HasThreeElems K]

-- needed instances [decidableeq] [HasThreeElems] , previously there where implicit variables like {A,B,C,all} that didn't allow ynthesis because the system couldn't find them...
instance : Fintype K :=
  ⟨({HasThreeElems.A, HasThreeElems.B, HasThreeElems.C} : Finset K),
   by
     intro x
     simp [HasThreeElems.all]⟩

open HasThreeElems
example :
    (Finset.univ : Finset K)
      = ({A, B, C} : Finset K) := by
  rfl 
  -- works
  --ext x
  --simp [HasThreeElems.all]
end

infixr:35 " and " => And
infixr:30 " or  "  => Or


variable {K : Type} {A : K} 
[DecidableEq K]

theorem disjoint_finset
{left right : Finset K}
(h : left ∩ right = ∅ )
(hk : A ∈ left)
(hkn : A ∈ right)  : False := by
  have := Finset.mem_inter_of_mem hk hkn
  rw [h] at this
  contradiction

theorem inleft_notinright_finset
{S S' : Finset K}
{A : K}
(h : S ∩ S' = ∅ )
(h' : A ∈ S) : A ∉ S' := by
  intro a
  have := Finset.mem_inter_of_mem h' a
  rw [h] at this
  contradiction
#print inleft_notinright_finset

theorem notinleft_inright
{S S' : Finset K}
{A : K}
(SorS' : A ∈ S ∨ A ∈ S')
(h' : A ∉ S) : A ∈ S' := by
  exact notleft_right SorS' h'

theorem inright_notinleft_finset
{S S' : Finset K}
(h : S ∩ S' = ∅ )
(h' : A ∈ S') : A ∉ S := by
  intro a
  have := Finset.mem_inter_of_mem h' a
  rw [Finset.inter_comm] at h
  rw [h] at this
  contradiction

theorem notinright_inleft
{S S' : Finset K}
(SorS' : A ∈ S ∨ A ∈ S')
(h' : A ∉ S') : A ∈ S := by
  exact notright_left SorS' h'

-------------------
theorem inleft_notinrightIff
{S S' : Finset K}
(h : S ∩ S' = ∅ )
(SorS' : A ∈ S ∨ A ∈ S')
: A ∈ S ↔  ¬(A ∈ S') := by
  constructor
  · exact inleft_notinright_finset h
  · exact notinright_inleft SorS'

theorem notinleft_inrightIff
{S S' : Finset K}
(h : S ∩ S' = ∅ )
(SorS' : A ∈ S ∨ A ∈ S')
: A ∉ S ↔  A ∈ S' := by
  constructor
  · exact notinleft_inright SorS'
  · exact inright_notinleft_finset h

theorem inright_notinleftIff
{S S' : Finset K}
(h : S ∩ S' = ∅ )
(SorS' : A ∈ S ∨ A ∈ S')
: A ∈ S' ↔  A ∉ S := by
  constructor
  · exact inright_notinleft_finset h
  · exact notleft_right SorS'

theorem notinright_inleftIff
{S S' : Finset K}
(h : S ∩ S' = ∅ )
(SorS' : A ∈ S ∨ A ∈ S')
 : A ∉ S' ↔  A ∈ S := by
  constructor
  · exact notinright_inleft SorS'
  · exact inleft_notinright_finset h

theorem set_subset_univ2
{A B : K}
 {S : Finset K}
(all : ∀ (x : K), x = A ∨ x = B )
: S ⊆ ({A,B} : Finset K) := by
  intro x h ; simp ;  exact all x

theorem set_subset_univ3
{A B C : K}
 {S : Finset K}
(all : ∀ (x : K), x = A ∨ x = B ∨ x = C)
: S ⊆ ({A,B,C} : Finset K) := by
  intro x h ; simp ;  exact all x
