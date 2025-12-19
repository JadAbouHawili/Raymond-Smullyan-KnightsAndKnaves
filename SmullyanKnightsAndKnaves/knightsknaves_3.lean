-- exclusive setup for levels with three inhabitants
import SmullyanKnightsAndKnaves.knightsknaves
namespace settheory_approach
variable [DecidableEq Inhabitant]
variable [Fintype Inhabitant]
axiom C : Inhabitant
axiom AneC : A ≠ C 

axiom BneC : B ≠ C

def oneKnight  : Prop:=   (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight)

def oneKnave  : Prop:=   (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knight) ∨ (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knight) ∨ (A ∈ Knight ∧ B ∈ Knight ∧ C ∈ Knave)

def allKnave : Prop := A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave

macro_rules
| `(tactic| contradiction) => 
  do `(tactic |solve  | ( exfalso ; apply AneC ; assumption ))


macro_rules
| `(tactic| contradiction) => 
  do `(tactic |solve  | ( exfalso ; apply AneC.symm ; assumption ))

macro_rules
| `(tactic| contradiction) => 
  do `(tactic |solve  | (exfalso ; apply BneC ; assumption ))

macro_rules
| `(tactic| contradiction) => 
  do `(tactic |solve  | (exfalso ; apply BneC.symm ; assumption ))


axiom all : ∀ (x : Inhabitant), x = A ∨ x = B ∨ x = C


#check Finset.subset_insert_iff_of_not_mem
--hypothesis
macro "remove_top" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic |  rw[ Finset.subset_insert_iff_of_not_mem] at $t1 <;> try assumption)
--goal
macro "remove_top" : tactic =>
do`(tactic |  rw[ Finset.subset_insert_iff_of_not_mem] <;> try assumption)


theorem univ2_iff_all {K : Type} {inst : Fintype K} {inst2 : DecidableEq K} {A B C : K}   : Finset.univ = ({A,B,C} : Finset K) ↔  ∀ (x : K), x = A ∨ x = B ∨ x = C:= by
  have : (Finset.univ : Finset K).toSet = Set.univ := Finset.coe_univ
  have this2: (Set.univ : Set K).toFinset = Finset.univ := Set.toFinset_univ
  #check Finset.coe_inj
  --rw [Finset.coe_inj.symm]
--  #check Finset.coe_inj
--  #check Finset.toSet
  have : Finset.univ = {A,B,C} ↔ Set.univ = {A,B,C} := by 
    constructor
    · intro Fu
      rw [Fu] at this
      symm
      simp at this
      assumption
    · intro Su
      rw [Finset.coe_inj.symm]
      simp
      assumption
  rw [this]
  rw [Set.ext_iff]
  mem_set
  simp

#check instDecidableEqBool
#check Finset.mem_insert_of_mem
#check Finset.mem_insert
-- this is useful if im using Finset.univ , doesn't occur in the game
theorem univ_iff_all
: Finset.univ = ({A,B,C} : Finset Inhabitant) ↔  ∀ (x : Inhabitant), x = A ∨ x = B ∨ x = C:= by 

/-shortest solution
  rw [Finset.ext_iff]
  simp
-/
  constructor
  · intro U
/-
    rw[ Finset.ext_iff] at U
    mem_finset at U
    simp at U
    assumption
-/
    intro x
    have : x ∈ Finset.univ := by mem_finset
    rw [U] at this
    mem_finset at this
    assumption
  · intro U
    rw [Finset.ext_iff]
    mem_finset
    simp
    assumption
    /-taking cases , not desirable,do not remove
    ext a
    constructor
    · intro aU
      rcases U a with h|h
      · rw [h]
        mem_finset
      · rcases h with h_1|h_1
        · rw [h_1]
          mem_finset
        · rw [h_1]
          mem_finset

    · exact fun a_1 => Finset.mem_univ a
    -/

theorem set_subset_univ
 {S : Finset Inhabitant}
: S ⊆ ({A,B,C} : Finset Inhabitant) := by
  intro x
  intro h
  mem_finset
  exact all x
  /-
  have := univ_iff_all.mpr all
  rw [←this]
  exact Finset.subset_univ S
  -/

macro "by_universe" : tactic =>
  `(tactic| (apply set_subset_univ))
end settheory_approach
