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
  do `(tactic |solve  | ( apply AneC ; assumption ))

macro_rules
| `(tactic| contradiction) => 
  do `(tactic |solve  | ( apply BneC ; assumption ))

axiom all : ∀ (x : Inhabitant), x = A ∨ x = B ∨ x = C

variable [DecidableEq Inhabitant]
theorem set_full3 { S : Finset Inhabitant} (hA : A ∈ S) (hB : B ∈ S) (hC : C ∈ S) 

{all : ∀ (x : Inhabitant), x = A ∨ x = B ∨ x = C}
: S = {A,B,C}
:= by
    apply full3
    exact all
    repeat assumption

#check singleton_iff_card_eq_one
theorem singleton_iff_card_eq_one3 {S : Finset Inhabitant}

{all : ∀ (x : Inhabitant), x = A ∨ x = B ∨ x = C}
: S = {A} ∨ S = {B} ∨ S = {C} ↔ S.card = 1 := by
    constructor
    intro eq
    rw [Finset.card_eq_one]
    rcases eq with h|h|h
    use A ; use B ; use C

    intro Scard
    rw [Finset.card_eq_one] at Scard
    have ⟨a,singleton⟩ := Scard
    rcases all a with h|h|h

    rw [h] at singleton
    left
    assumption

    rw [h] at singleton
    right ; left
    assumption

    rw [h] at singleton
    right ; right
    assumption


theorem all_in_one
  {S : Finset Inhabitant} 
  {all : ∀(x : Inhabitant), x = A ∨ x = B ∨ x = C}
  (hA : A ∈ S)
  (hB : B ∈ S)
  (hC : C ∈ S)
  : S = {A,B,C}
  := by 
    #check Finset.eq_of_subset_of_card_le 
    exact (everyone_in_set_eq all).mp ⟨hA,hB,hC⟩ 

#check Finset.univ_subset_iff
#check Finset.subset_univ
theorem set_subset_univ  
 {S : Finset Inhabitant}
 {inst : Fintype Inhabitant}
: S ⊆ {A,B,C} := by 
  have all := all
  rw [(univ_iff_all).symm] at all
  rw [←all]
  exact Finset.subset_univ S

macro "by_universe" : tactic =>
  `(tactic| (apply set_subset_univ; assumption))

end settheory_approach
