-- exclusive setup for levels with three inhabitants
import SmullyanKnightsAndKnaves.knightsknaves_foundation

inductive Inhabitant
| A
| B
| C
deriving DecidableEq , Fintype

-- call these Knight internal then do local notation
namespace hidden
axiom Knight : Finset Inhabitant
axiom Knave : Finset Inhabitant

axiom  KorKn : ∀ x : Inhabitant, x ∈ Knight ∨ x ∈ Knave
axiom dis : Knight ∩ Knave = ∅
end hidden

noncomputable instance world : World Inhabitant :=  by
  exact ⟨hidden.Knight,
  hidden.Knave,
  hidden.dis,
  hidden.KorKn⟩

open Inhabitant

macro_rules
| `(tactic| contradiction) =>
  do `(tactic |solve  | ( exfalso ; apply @disjoint Inhabitant  ; repeat assumption) )


theorem all : ∀x : Inhabitant , x = .A ∨ x = .B ∨ x = .C := by
  intro x
  cases x <;> aesop


def oneKnight  : Prop:=   (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight)

def oneKnave  : Prop:=   (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knight) ∨ (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knight) ∨ (A ∈ Knight ∧ B ∈ Knight ∧ C ∈ Knave)

def allKnave : Prop := A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave

/-
--#check Finset.subset_insert_iff_of_not_mem
--hypothesis
macro "remove_top" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic |  rw[ Finset.subset_insert_iff_of_notMem] at $t1 <;> try assumption)
--goal
macro "remove_top" : tactic =>
do`(tactic |  rw[ Finset.subset_insert_iff_of_notMem] <;> try assumption)

-/
#check Set.toFinset_eq_univ 
#check Multiset.bijective_iff_map_univ_eq_univ
#check Finset
  #check Set.toFinset_univ
  #check Finset.coe_univ
  #check Finset.coe_inj
  #check Finset.toSet


#check Finset.mem_insert_of_mem
#check Finset.mem_insert
#check Set.univ

#check SetLike

#check Set.toFinset_insert
#check Set.toFinset_singleton
#check Finset.val_inj
example {K : Type} [DecidableEq K] [Fintype K] :Finset.univ = {A,B,C} ↔ Set.univ = {A,B,C} := by 
  nth_rw 2 [eq_comm]
  #check Set.toFinset_eq_univ 
  rw [Set.toFinset_eq_univ.symm]
  simp
  exact eq_comm

#check set_subset_univ
example
 {S : Finset Inhabitant}
: S ⊆ ({A,B,C} : Finset Inhabitant) := by
  intro x h
  simp
  exact all x

macro "by_universe" : tactic =>
  `(tactic| (apply set_subset_univ ; intro x ; exact all x))

macro "all_cases_satisfy_goal3" t1:Lean.Parser.Tactic.elimTarget : tactic =>
  `(tactic|
  rcases $t1 with h|h|h <;> (rw[h] ; assumption)
    )
