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
axiom KorKn : ∀(x : Inhabitant), x ∈ Knight ∨ x ∈ Knave

theorem disjoint
{A : Inhabitant}
(AKnight : A ∈ Knight)
(AKnave : A ∈ Knave)  : False := by
  exact disjoint_finset dis AKnight AKnave


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


-- generalize to set theory using disjoint axiom , use here without disjoint axiom
theorem knight_notknave
{A : Inhabitant}
(h' : A ∈ Knight) : A ∉ Knave := by
  exact inleft_notinright_finset dis h'

theorem notknight_knave
{A : Inhabitant}
(h' : A ∉ Knight) : A ∈ Knave := by
  exact notleft_right (KorKn A) h'

theorem knave_notknight
{A : Inhabitant}
(h' : A ∈ Knave) : A ∉ Knight := by
  exact inright_notinleft_finset dis h'

omit [DecidableEq Inhabitant] in
theorem notknave_knight
{A : Inhabitant}
(h' : A ∉ Knave) : A ∈ Knight := by
  exact notright_left (KorKn A) h'


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

axiom either (A : Inhabitant): A ∈ Knight ∨ A ∈ Knave

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
