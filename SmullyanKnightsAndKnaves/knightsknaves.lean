import SmullyanKnightsAndKnaves.settheory

namespace settheory_approach

open Lean Elab Tactic
axiom Inhabitant : Type
axiom Knight : Finset Inhabitant
axiom Knave : Finset Inhabitant
axiom inst : DecidableEq Inhabitant
axiom A : Inhabitant
axiom B : Inhabitant
axiom AneB : A ≠ B

variable [DecidableEq Inhabitant]
axiom dis : Knight ∩ Knave = ∅
axiom KorKn {A : Inhabitant}: A ∈ Knight ∨ A ∈ Knave

theorem disjoint
{A : Inhabitant}
(AKnight : A ∈ Knight)
(AKnave : A ∈ Knave)  : False := by
  exact disjoint_finset dis AKnight AKnave

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
  do `(tactic |solve  | ( exfalso ; apply disjoint  ; repeat assumption) )

macro_rules
| `(tactic| contradiction) =>
  do `(tactic |solve  | ( apply AneB ; assumption ))

macro_rules
| `(tactic| contradiction) =>
  do `(tactic |solve  | ( apply AneB.symm ; assumption ))

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
    --#check set_subset_univ
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



-- generalize to set theory using disjoint axiom , use here without disjoint axiom
theorem knight_notknave
{A : Inhabitant}
(h' : A ∈ Knight) : A ∉ Knave := by
  exact inleft_notinright_finset dis h'

theorem notknight_knave
{A : Inhabitant}
(h' : A ∉ Knight) : A ∈ Knave := by
  exact notleft_right KorKn h'

theorem knave_notknight
{A : Inhabitant}
(h' : A ∈ Knave) : A ∉ Knight := by
  exact inright_notinleft_finset dis h'

omit [DecidableEq Inhabitant] in
theorem notknave_knight
{A : Inhabitant}
(h' : A ∉ Knave) : A ∈ Knight := by
  exact notright_left KorKn h'


-------------------
theorem knight_notknaveIff
{A : Inhabitant}
: A ∈ Knight ↔  ¬(A ∈ Knave) := by
  constructor
  · exact knight_notknave
  · exact notknave_knight

theorem notknight_knaveIff
{A : Inhabitant}
: A ∉ Knight ↔  A ∈ Knave := by
  constructor
  · exact notknight_knave
  · exact knave_notknight

theorem knave_notknightIff
  {A : Inhabitant}
: A ∈ Knave ↔  A ∉ Knight := by
  constructor
  · exact knave_notknight
  · exact notknight_knave

theorem notknave_knightIff
  {A : Inhabitant}
 : A ∉ Knave ↔  A ∈ Knight := by
  constructor
  · exact notknave_knight
  · exact knight_notknave

#check not_eq_singleton_of_not_mem

#check card_eq_one_iff_singletons
#check card_eq
theorem not_eq_singleton_already_full
{K : Type}
{A B: K}
{Knave : Finset K}
(AneB : A ≠ B)
(AKnave : A ∈ Knave)

: Knave ≠ {B} := by
        intro knaveB
        rw [knaveB] at AKnave
        #check Finset.mem_singleton
        rw [Finset.mem_singleton] at AKnave
        contradiction

axiom either (A : Inhabitant): A ∈ Knight ∨ A ∈ Knave

-- Alternative: elab version for more control
--elab "contradiction_hyp " t1:term ", " t2:term : tactic => do
--  let goal ← getMainGoal
--  let notBothApp ← `(not_both $t1 $t2)
--  let expr ← elabTerm notBothApp none
--  goal.assign expr


--macro "contradiction_hyp" t1:ident  t2:ident : tactic =>
--  do`(tactic| exact not_both $t1 $t2)


-- Alternative syntax using elab for more control
--elab "not_both_exact " t1:term " " t2:term : tactic => do
--  let goal ← getMainGoal
--  let t1Expr ← elabTerm t1 none
--  let t2Expr ← elabTerm t2 none
--  let notBothExpr ← elabTerm (← `(not_both $t1 $t2)) none
--  goal.assign notBothExpr

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

-- *
macro "set_knave_to_knight" "at"  t1:Lean.Parser.Tactic.locationWildcard : tactic =>
  do`(tactic| simp only [knave_notknightIff,not_not] at $t1)
-- goal
macro "set_knave_to_knight" : tactic =>
  do`(tactic| simp only [knave_notknightIff,not_not])
-- hypothesis
macro "set_knave_to_knight" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic|
  simp only[knave_notknightIff,not_not] at $t1)

macro "set_knight_or_knave" t1:term  : tactic =>
do`(tactic| cases (either $t1)  )

macro "set_knight_or_knave" t1:term "with" t2:rcasesPat t3:rcasesPat  : tactic =>
do`(tactic| obtain $t2|$t3 := (either $t1)  )


end settheory_approach
