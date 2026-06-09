import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.ApplyFun
import Lean.Parser.Tactic

import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic.Have

import SmullyanKnightsAndKnaves.logic

-- hide all this from the user

axiom Islander : Type

namespace Islander
axiom A : Islander
axiom B : Islander
axiom C : Islander

axiom isKnight : Islander → Prop

axiom isKnave : Islander → Prop

axiom isKnight_or_isKnave (A : Islander) : A.isKnight ∨ A.isKnave

axiom not_isKnight_and_isKnave (A : Islander) : ¬ (A.isKnight ∧ A.isKnave)

axiom Said : Islander → Prop → Prop

theorem notisKnight_isKnave {A : Islander} : ¬A.isKnight → A.isKnave := by
  intro h
  exact Or.resolve_left (isKnight_or_isKnave A) h
theorem notisKnave_isKnight {A : Islander} : ¬A.isKnave → A.isKnight := by
  intro h
  exact Or.resolve_right (isKnight_or_isKnave A) h

macro_rules
| `(tactic| contradiction) => 
  do `(tactic |solve  | (exfalso ; apply not_isKnight_and_isKnave ; constructor ; assumption ; assumption   ) )

theorem isKnight_notisKnave {A : Islander} : A.isKnight → ¬A.isKnave := by
  intro AKnight  AKnave
  contradiction
theorem isKnave_notisKnight {A : Islander} : A.isKnave → ¬A.isKnight := by
  intro h ha ; contradiction

theorem isKnight_notisKnaveIff {A : Islander} : A.isKnight ↔ ¬A.isKnave := by
  exact ⟨isKnight_notisKnave , notisKnave_isKnight⟩ 
theorem isKnave_notisKnightIff {A : Islander} : A.isKnave ↔ ¬A.isKnight := by
  exact ⟨isKnave_notisKnight , notisKnight_isKnave⟩

--------------
-- number affects where brackets will be needed
notation A " said " P:200 => Said A P
infixr:35 " and " => And
infixr:30 " or  "  => Or

axiom knight_said {A : Islander} {P : Prop} : (A said P) → A.isKnight → P
axiom said_knight {A : Islander} {P : Prop} : (A said P) →  P → A.isKnight 

theorem knave_said {A : Islander} {P : Prop} : (A said P) →  A.isKnave → ¬P := by
  intro AsaidP AKnave hP
  have := said_knight AsaidP hP
  contradiction
theorem notknight_said {A : Islander} {P : Prop} : (A said P) → ¬A.isKnight → ¬P := by
  intro h h' hP
  have := said_knight h hP
  contradiction
theorem said_knave {A : Islander} {P : Prop} : A said P →  ¬P → A.isKnave := by 
  intro AsaidP nP
  apply notisKnight_isKnave 
  intro AKnight
  have hP := knight_said AsaidP AKnight
  contradiction

section tactics
-- make custom tactics for finset.card stuff...

macro "knight_or_knave" t1:term "with" t2:rcasesPat t3:rcasesPat : tactic => do`(tactic| obtain ($t2 | $t3) := isKnight_or_isKnave $t1)

macro "knight_or_knave" t1:term  : tactic => do`(tactic| cases isKnight_or_isKnave $t1)

-- *
macro "knight_to_knave" "at" t1:Lean.Parser.Tactic.locationWildcard : tactic =>
do`(tactic| simp [isKnight_notisKnaveIff] at $t1)
-- goal
macro "knight_to_knave" : tactic =>
do`(tactic| simp [isKnight_notisKnaveIff])
-- hypothesis
macro "knight_to_knave" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic| simp [isKnight_notisKnaveIff] at $t1)

-- *
macro "knave_to_knight" "at" t1:Lean.Parser.Tactic.locationWildcard : tactic => 
do`(tactic| simp [isKnave_notisKnightIff] at $t1)
--goal
macro "knave_to_knight" : tactic =>
do`(tactic| simp [isKnave_notisKnightIff])
-- hypothesis
macro "knave_to_knight" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic| simp only [isKnave_notisKnightIff,not_not] at $t1)

end tactics

def allKnights {A B C : Islander}:= A.isKnight ∧ B.isKnight ∧ C.isKnight
def allKnaves {A B C : Islander} := A.isKnave ∧ B.isKnave ∧ C.isKnave
def oneisknight {A B C : Islander} := (A.isKnight ∧ B.isKnave ∧ C.isKnave)  ∨(A.isKnave ∧  B.isKnight ∧ C.isKnave) ∨ (A.isKnave ∧ B.isKnave ∧  C.isKnight)
def exactlyOneIsKnave {A B C : Islander} : Prop := (A.isKnave and B.isKnight and C.isKnight) ∨ (A.isKnight and B.isKnave and C.isKnight) ∨ (A.isKnight and B.isKnight and C.isKnave)
end Islander

open Islander

/-
A is a knight. A says that B is a knave. Prove that B is a knave.
-/
example {A B : Islander} (hA : A.isKnight) (hAB : A said B.isKnave) : B.isKnave := by
  exact knight_said hAB hA

theorem dsl_iamknave {A : Islander} (hAKn : A said A.isKnave): False := by
  knight_or_knave A with hA hnA
  · have hnA := knight_said hAKn hA
    apply @not_isKnight_and_isKnave A
    constructor
    assumption ; assumption
  · have hnA2 := knave_said hAKn hnA
    contradiction
