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

axiom Inhabitant : Type
axiom Knight : Finset Inhabitant
axiom Knave : Finset Inhabitant
axiom inst : DecidableEq Inhabitant
axiom A : Inhabitant
axiom B : Inhabitant
axiom C : Inhabitant
axiom AneB : A ≠ B
axiom AneC : A ≠ C
axiom BneC : B ≠ C

variable [DecidableEq Inhabitant]
axiom dis : Knight ∩ Knave = ∅
axiom KorKn {A : Inhabitant}: A ∈ Knight ∨ A ∈ Knave

axiom all : ∀ (x : Inhabitant), x = A ∨ x = B ∨ x = C
axiom not_both
  {A : Inhabitant}
  (AKnight : A ∈ Knight) (AKnave : A ∈ Knave)  : False

def oneKnight  : Prop:=   (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight)

def oneKnave  : Prop:=   (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knight) ∨ (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knight) ∨ (A ∈ Knight ∧ B ∈ Knight ∧ C ∈ Knave)

def allKnave : Prop := A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave

theorem all_in_one
  {inst : DecidableEq Inhabitant}
  {A B C : Inhabitant}
  {S : Finset Inhabitant} 
  {all : ∀(x : Inhabitant), x = A ∨ x = B ∨ x = C}
  (hA : A ∈ S)
  (hB : B ∈ S)
  (hC : C ∈ S)
  : S = {A,B,C}
  := by 
    #check Finset.eq_of_subset_of_card_le 
    exact (everyone_in_set_eq all).mp ⟨hA,hB,hC⟩ 
theorem set_full3 { S : Finset Inhabitant} (hA : A ∈ S) (hB : B ∈ S) (hC : C ∈ S) : S = {A,B,C} := by
    apply full3
    exact all
    repeat assumption

#check singleton_iff_card_eq_one
theorem singleton_iff_card_eq_one3 {S : Finset Inhabitant}: S = {A} ∨ S = {B} ∨ S = {C} ↔ S.card = 1 := by
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

theorem disjoint
{A : Inhabitant}
(Aleft : A ∈ Knight)
(Aright : A ∈ Knave)  : False := by 
  have := Finset.mem_inter_of_mem Aleft Aright
  rw [dis] at this
  contradiction

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
-------------
-- using simp , experiment with simp_rw

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
  do `(tactic |solve  | ( exfalso ; apply not_both  ; repeat assumption) )
theorem IamKnave
{A : Inhabitant}
(stA : A ∈ Knight  ↔ (A ∈ Knave) )
  : False := by

  {
    rcases @KorKn A with AKnight|AKnave
    · have := stA.mp AKnight
      contradiction

    · have := stA.mpr AKnave
      contradiction
  }
example (h : C ∈ Knight) (h' : C ∈ Knave) : False  := by 
  contradiction

theorem IamKnaveIffFalse
: False ↔  (A ∈ Knight  ↔ (A ∈ Knave))
   := by
    constructor
    exact fun a => a.elim
    exact IamKnave

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

axiom either (A : Inhabitant): A ∈ Knight ∨ A ∈ Knave

-- *
macro "set_knight_to_knave" "at"  t1:Lean.Parser.Tactic.locationWildcard : tactic =>
do`(tactic| simp [inleft_notinrightIff] at $t1)
-- goal
macro "set_knight_to_knave" : tactic =>
do`(tactic| simp [inleft_notinrightIff])
-- hypothesis
macro "set_knight_to_knave" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic| 
simp [inleft_notinrightIff] at $t1)

-- *
macro "set_knave_to_knight" "at"  t1:Lean.Parser.Tactic.locationWildcard : tactic =>
do`(tactic| simp [inright_notinleftIff] at $t1)
-- goal
macro "set_knave_to_knight" : tactic =>
do`(tactic| simp [inright_notinleftIff])
-- hypothesis
macro "set_knave_to_knight" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic| 
simp [inright_notinleftIff] at $t1)

macro "set_knight_or_knave" t1:term  : tactic =>
do`(tactic| cases (either $t1)  )

macro "set_knight_or_knave" t1:term "with" t2:rcasesPat t3:rcasesPat  : tactic =>
do`(tactic| obtain $t2|$t3 := (either $t1)  )
end settheory_approach
