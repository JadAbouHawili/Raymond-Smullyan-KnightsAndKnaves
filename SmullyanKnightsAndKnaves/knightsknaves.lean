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

namespace settheory_approach


axiom  Inhabitant : Type
axiom Knight : Finset Inhabitant
axiom Knave : Finset Inhabitant
--axiom inst : DecidableEq Inhabitant
--variable ( inst : DecidableEq Inhabitant)
axiom inst : DecidableEq Inhabitant

variable [DecidableEq Inhabitant]
axiom dis : Knight ∩ Knave = ∅ 
axiom KorKn {A : Inhabitant}: A ∈ Knight ∨ A ∈ Knave 

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

macro_rules
| `(tactic| contradiction) => 
  do `(tactic |solve  | ( apply not_both  ; repeat assumption) )
theorem IamKnave
  {A : Inhabitant}
(stA : A ∈ Knight  ↔ (A ∈ Knave) )
  : False := by

  {
    rcases KorKn with AKnight|AKnave

    · have := stA.mp AKnight
      contradiction

    · have := stA.mpr AKnave
      contradiction
      --exact disjoint h this AKnave
  }

theorem IamKnaveIffFalse
{A : Inhabitant}
  (Or : (A ∈ Knight ∨ A ∈ Knave))
: False ↔  (A ∈ Knight  ↔ (A ∈ Knave))  
   := by
    constructor
    exact fun a => a.elim
    exact IamKnave  

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

-- theorem used in simp would need arguments passed to it, change so that theorems used require fewer arguments
--namespace settheory_approach
--
--axiom Inhabitant : Type
--axiom inst222 : DecidableEq Type
--axiom inst : DecidableEq Inhabitant
--axiom inst1 : DecidableEq Inhabitant
--axiom inst2 : Fintype Inhabitant
--axiom Knight : Finset Inhabitant
--axiom Knave : Finset Inhabitant
--axiom inst22 : DecidableEq Inhabitant
--axiom inst22222 : Fintype Inhabitant
--set_option diagnostics true
--#check inst1
----variable {inst32 : DecidableEq Inhabitant}
--def inst0 : DecidableEq Inhabitant := sorry
--variable [s : DecidableEq Inhabitant]
--#check Knight ∩ Knave
--example {A : Inhabitant} {h : A ∈ Knight}
----{inst222 : DecidableEq Inhabitant}
--{hKKn : Knight ∩ Knave = ∅ }
--: 2=2 := by
--  rfl
--#check inleft_notinrightIff
--#check inleft_notinright
--
---- *
--macro "knight_to_knave" "at" t1:Lean.Parser.Tactic.locationWildcard : tactic =>
--do`(tactic| simp [inleft_notinrightIff] at $t1)
---- goal
--macro "knight_to_knave" : tactic =>
--do`(tactic| simp [inleft_notinrightIff])
---- hypothesis
--macro "knight_to_knave" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
--do`(tactic| simp [inleft_notinrightIff] at $t1)
----     (rw [inleft_notinrightIff] at BKnave <;> try assumption) ; simp at BKnave
--#check inleft_notinrightIff
---- this would work for one hypothesis but what about for *,everything?
--macro "knight_to_knave2" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
--do`(tactic|
--rw [inleft_notinrightIff] at $t1 <;> try assumption )
--
---- *
--macro "knave_to_knight" "at" t1:Lean.Parser.Tactic.locationWildcard : tactic => 
--do`(tactic| simp [inright_notinleftIff] at $t1)
--macro "knave_to_knight" : tactic =>
--do`(tactic| simp [inright_notinleftIff])
---- hypothesis
--macro "knave_to_knight" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
--do`(tactic| simp [inright_notinleftIff] at $t1)
--end settheory_approach

-- environment

theorem inleft_notinright
{A : Inhabitant}
(h : Knight ∩ Knave = ∅ )
(h' : A ∈ Knight) : A ∉ Knave := by
  intro a 
  #check Finset.mem_inter_of_mem
  have := Finset.mem_inter_of_mem h' a
  rw [h] at this
  contradiction

theorem notinleft_inright
{A : Inhabitant}
(h' : A ∉ Knight) : A ∈ Knave := by
  exact notleft_right KorKn h'

theorem inright_notinleft
{A : Inhabitant}
(h : Knight ∩ Knave = ∅ )
(h' : A ∈ Knave) : A ∉ Knight := by
  intro a 
  have := Finset.mem_inter_of_mem h' a
  rw [Finset.inter_comm] at h
  rw [h] at this
  contradiction

theorem notinright_inleft
{A : Inhabitant}
(h' : A ∉ Knave) : A ∈ Knight := by
  exact notright_left KorKn h'

-------------------
theorem inleft_notinrightIff
{A : Inhabitant}
: A ∈ Knight ↔  ¬(A ∈ Knave) := by
  constructor
  · exact inleft_notinright dis
  · exact notinright_inleft
  
theorem notinleft_inrightIff
{A : Inhabitant}
: A ∉ Knight ↔  A ∈ Knave := by
  constructor
  · exact notinleft_inright
  · exact inright_notinleft dis

theorem inright_notinleftIff
  {A : Inhabitant}
: A ∈ Knave ↔  A ∉ Knight := by
  constructor
  · exact inright_notinleft dis
  · exact notleft_right KorKn

theorem notinright_inleftIff
  {A : Inhabitant}
 : A ∉ Knave ↔  A ∈ Knight := by
  constructor
  · exact notinright_inleft
  · exact inleft_notinright dis


theorem disjoint_without
{A : Inhabitant}
(Aleft : A ∈ Knight)
(Aright : A ∈ Knave)  : False := by 
  have := Finset.mem_inter_of_mem Aleft Aright
  rw [dis] at this
  contradiction

axiom either (A : Inhabitant): A ∈ Knight ∨ A ∈ Knave 
-- *
macro "set_knight_to_knave" t2:term "at"  t1:Lean.Parser.Tactic.locationWildcard : tactic =>
do`(tactic| simp [inleft_notinrightIff] at $t1)

macro "set_knight_to_knave" t2:term : tactic =>
do`(tactic| simp [inleft_notinrightIff])
-- hypothesis
macro "set_knight_to_knave" t2:term "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic| 
simp [inleft_notinrightIff] at $t1)

-- *
macro "set_knave_to_knight" t2:term "at"  t1:Lean.Parser.Tactic.locationWildcard : tactic =>
do`(tactic| simp [inright_notinleftIff] at $t1)
-- goal
macro "set_knave_to_knight" t2:term : tactic =>
do`(tactic| simp [inright_notinleftIff])
-- hypothesis
macro "set_knave_to_knight" t2:term "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic| 
simp [inright_notinleftIff] at $t1)

macro "set_knight_or_knave" t1:term  : tactic =>
do`(tactic| cases (either $t1)  )

macro "set_knight_or_knave" t1:term "with" t2:rcasesPat t3:rcasesPat  : tactic =>
do`(tactic| obtain $t2|$t3 := (either $t1)  )
end settheory_approach
