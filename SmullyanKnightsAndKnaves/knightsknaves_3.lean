-- exclusive setup for levels with three inhabitants
import SmullyanKnightsAndKnaves.knightsknaves
namespace settheory_approach
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

variable [DecidableEq Inhabitant]



#check Finset.subset_insert_iff_of_not_mem
--hypothesis
macro "remove_top" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic |  rw[ Finset.subset_insert_iff_of_not_mem] at $t1 <;> try assumption)
--goal
macro "remove_top" : tactic =>
do`(tactic |  rw[ Finset.subset_insert_iff_of_not_mem] <;> try assumption)

end settheory_approach
