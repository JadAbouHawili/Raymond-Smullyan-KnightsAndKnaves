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

--works
section

-- for x : K , enables cases x
-- say we have K.A : K , how to get K.A ∈ knight ∨ K.A ∈ Knave

inductive K
| A
| B
| C
deriving DecidableEq , Fintype


set_option pp.all true in
#print K
#check K.noConfusionType 
#check K.casesOn
#check K.casesOn
#check Eq

#check Fintype K
#synth (Fintype K)
#check (Finset.univ : Finset K)

open K

example : A ≠ B := by exact not_eq_of_beq_eq_false rfl

example : Finset.univ = ({A,B,C} : Finset K) := by
  rfl

theorem all : ∀x : K , x = A ∨ x = B ∨ x = C := by
  intro x
  cases x <;> aesop

axiom Knight : Finset K
axiom Knave : Finset K

#check xor
#check Xor'



example : (∀ (x : K), Xor' (x ∈ Knight) (x ∈ Knave)) → Knight ∩ Knave = ∅ := by
  intro h
  grind
#check xor_def
  theorem disjoint_iff_xor : (Knight ∩ Knave = ∅  ∧ (∀x:K, x ∈ Knight ∨ x ∈ Knave) )↔  ∀(x : K), Xor' (x ∈ Knight)  (x ∈ Knave) := by
  constructor
  · intro ⟨h1,h2⟩  x 
    unfold Xor' 
    cases h2 x
    left
    constructor
    assumption
    intro
    sorry
    sorry
  intro h
  constructor
  by_contra 
  simp at this
  have : ∃ x: K , x ∈ Knight ∩ Knave := by 
    simp [Finset.nonempty_iff_ne_empty.symm] at this
    exact Finset.nonempty_def.mp this 
  have ⟨x,h'⟩ := this
  have h := h x 
  unfold Xor' at h 
  simp at h'
  grind 
  sorry

#check Finset.nonempty_iff_ne_empty
#check Finset.nonempty_of_ne_empty

-- is the only advantage just doing cases x... and also that decidableeq and fintype not visible 
-- it seems like the only change is:
-- axiom K
-- axiom A
-- axiom B
-- axiom C
axiom dis : Knight ∩ Knave = ∅

axiom KorKn : ∀(x : K), x ∈ Knight ∨ x ∈ Knave


---- hypothesis
--macro "knave_interp" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
--do`(tactic| (rw [not_iff_not.symm] at $t1 ; simp only[knight_notknaveIff,not_not] at $t1)
--)
--
---- hypothesis
--macro "knight_interp" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
--do`(tactic| (rw [not_iff_not.symm] at $t1 ; simp only[knave_notknightIff,not_not] at $t1)

/-

-- hypothesis
macro "knight_interp" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic| (rw [not_iff_not.symm] at $t1 ; simp only[knave_notknightIff,not_not] at $t1)
)

axiom either (A : Inhabitant): A ∈ Knight ∨ A ∈ Knave

-- redundant
-- *
macro "set_knight_to_knave" "at"  t1:Lean.Parser.Tactic.locationWildcard : tactic =>
  do`(tactic| simp only [knight_notknaveIff,not_not] at $t1)
-- goal
macro "set_knight_to_knave" : tactic =>
  do`(tactic| simp only [knight_notknaveIff,not_not])
-- hypothesis
macro "set_knight_to_knave" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic|
  simp only [knight_notknaveIff,not_not] at $t1)
-/


example : Knight ∪ Knave = {A,B,C} → A ∈ Knight ∪ Knave := by
  intro h
  rw [h]
  rw [Finset.mem_insert]
  #check reduceCtorEq 
  simp?
  --left ; rfl

example
{stA : A ∈ Knight ↔ Knave = {A,B,C}}
{stAn : A ∈ Knave ↔ Knave ≠ {A,B,C}}
{stB : B ∈ Knight ↔ Knight = {A} ∨ Knight = {B} ∨ Knight = {C} }
{stBn : B ∈ Knave ↔ ¬(Knight = {A} ∨ Knight = {B} ∨ Knight = {C}) }
-- need
{all2:  Knight ∪ Knave = {A,B,C}}
: A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave := by
-- A : all of us are knaves
-- B : exactly one of us is a knight

  have AKnave : A ∈ Knave
  by_contra h
  have : A ∈ Knight := by
    have := KorKn A 
    --exact?
    apply Or.resolve_right
    assumption
    assumption

example {P Q : Prop} (h : ¬Q) (h' : P ∨ Q) : P := by
  exact Or.resolve_right h' h
     







--variable {K : Type} [DecidableEq K]
--variable (A B C : K)
--variable (all : ∀ x : K, x = A ∨ x = B ∨ x = C)
--
--
--#check K
--#check DecidableEq K
--#synth DecidableEq K
--#check (inferInstance : DecidableEq K)

--variable [DecidableEq K]
--variable (A B C : K)
--#check (↥ ·)
variable (all : ∀ x : K, x = A ∨ x = B ∨ x = C)
#check A

#check K
#check instFintypeK
#check (Finset.univ : Finset K)

#check instFintypeK


--instance instFin
/-
variable [instFintypeK A B C all]

theorem univ2_iff_all :
    (Finset.univ : Finset K) = ({A,B,C} : Finset K) ↔
      ∀ x : K, x = A ∨ x = B ∨ x = C := by
  …

variable [instFintypeK A B C all]
--theorem univ2_iff_all : Finset.univ = ({A,B,C} : Finset K) := by
theorem univ2_iff_all {K : Type} [Fintype K] {inst2 : DecidableEq K} {A B C : K}   : Finset.univ = ({A,B,C} : Finset K) ↔  ∀ (x : K), x = A ∨ x = B ∨ x = C:= by
  -- i want to prove that Finset.univ = {A,B,C} by using instfintypek and not fintype k

  -- solution , no need for coercions and so on. nonetheless look into and understand coercions then remove them from here...
  --rw [Finset.ext_iff]
  --simp
  --simp

  #check Finset.instSetLike
  --#check Finset.coe
  have this: (Finset.univ : Finset K).toSet = Set.univ := Finset.coe_univ
  #check Finset.toSet
  #check Finset.instSetLike.coe
  #check Finset.coe_univ
  #check Fintype.finsetEquivSet
  let setuniv := Finset.instSetLike.coe (Finset.univ : Finset K)
  have coe_univ : ↑(univ : Finset K) = (Set.univ : Set K) := by ext; simp? [Set.mem_univ,iff_true]
  #check coe_univ
  have : setuniv = Set.univ := by unfold setuniv ; exact coe_univ
  --#check SetLike.coe
  --unfold setuniv at this -- can i get to this result directly?

  have this3 : (Finset.univ : Finset K) ≃ @Set.univ K:= by exact Equiv.subtypeEquivProp this
  #check Subtype
  #check Fintype.finsetEquivSet
  #check Finset.univ ≃ Set.univ
  have: (Finset.univ : Finset K)≃ (Set.univ : Set K) := by
--↥
    apply Fintype.finsetEquivSet





  have this2: (Set.univ : Set K).toFinset = Finset.univ := by exact Set.toFinset_univ
  #check Finset.coe_inj
  --rw [Finset.coe_inj.symm]
--  #check Finset.coe_inj
--  #check Finset.toSet
  #check SetLike
  #check Finset.coe_eq_univ
  have : Finset.univ = {A,B,C} ↔ Set.univ = {A,B,C} := by
    constructor
    · intro Fu
      rw [Fu] at this
      symm
      simp at this
      assumption
    · intro Su
      rw [Finset.coe_inj.symm]
      #check Finset.coe_univ
      simp?
      assumption
  --rw [this]
  #check Finset.ext_iff




-/

end
