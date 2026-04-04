
import SmullyanKnightsAndKnaves.settheory

universe u

@[pp_nodot]
class World (Inhabitant : Type u) [DecidableEq Inhabitant] where
  Knight : Finset Inhabitant
  Knave : Finset Inhabitant
  dis : Knight ∩ Knave = ∅
  KorKn : ∀ x : Inhabitant, x ∈ Knight ∨ x ∈ Knave

variable {Inhabitant : Type}
[DecidableEq Inhabitant]
[W: World Inhabitant]
#check W.Knight
--local notation "Knight" => W.Knight
--local notation "Knave" => W.Knave
--local notation "KorKn" => W.KorKn
--local notation "dis" => W.dis

noncomputable def Knight := W.Knight
noncomputable def Knave := W.Knave
noncomputable def  dis := W.dis
noncomputable def  KorKn : ∀ x : Inhabitant, x ∈ Knight ∨ x ∈ Knave := W.KorKn

#check dis
#check Knight


#check Finset.instUnion
instance : OrOp Prop  :=
  ⟨fun a b ↦ Or a b⟩ 
#check xor_def

example : (Xor' (2=2) (2=2)) ↔ (2=2 ↔ 2≠2) := by 
  exact xor_iff_iff_not 
-- open World is no good

theorem disjoint
{A : Inhabitant}
(AKnight : A ∈ Knight)
(AKnave : A ∈ Knave)  : False := by
  exact disjoint_finset W.dis AKnight AKnave

-- needs to be repeated in every file...
macro_rules
| `(tactic| contradiction) =>
  do `(tactic |solve  | ( exfalso ; apply @disjoint Inhabitant  ; repeat assumption) )

macro_rules
| `(tactic| contradiction) =>
  do `(tactic |solve  | ( apply AneB ; assumption ))

macro_rules
| `(tactic| contradiction) =>
  do `(tactic |solve  | ( apply AneB.symm ; assumption ))

theorem IamKnave
{A : Inhabitant}
(stA : A ∈ W.Knight  ↔ (A ∈ W.Knave) )
  : False := by

  {
    rcases KorKn A with AKnight|AKnave
    · have := stA.mp AKnight
      contradiction

    · have := stA.mpr AKnave
      contradiction
  }

theorem IamKnaveIffFalse
{A : Inhabitant}
: False ↔  (A ∈ W.Knight  ↔ (A ∈ W.Knave))
   := by
    constructor
    exact fun a => a.elim
    exact IamKnave

theorem knight_notknave
{A : Inhabitant}
(h' : A ∈ W.Knight) : A ∉ W.Knave := by
  exact inleft_notinright_finset W.dis h'

theorem notknight_knave
{A : Inhabitant}
(h' : A ∉ W.Knight) : A ∈ W.Knave := by
  exact notleft_right (KorKn A) h'

theorem knave_notknight
{A : Inhabitant}
(h' : A ∈ Knave) : A ∉ Knight := by
  exact inright_notinleft_finset W.dis h'

theorem notknave_knight
{A : Inhabitant}
(h' : A ∉ Knave) : A ∈ Knight := by
  exact notright_left (KorKn A) h'


-------------------
--@[simp]
theorem knight_notknaveIff
{A : Inhabitant}
: A ∈ W.Knight ↔  ¬(A ∈ W.Knave) := by
  constructor
  · exact knight_notknave
  · exact notknave_knight

theorem notknight_knaveIff
{A : Inhabitant}
: A ∉ W.Knight ↔  A ∈ W.Knave := by
  constructor
  · exact notknight_knave
  · exact knave_notknight

theorem knave_notknightIff
  {A : Inhabitant}
: A ∈ Knave ↔  A ∉ Knight := by
  constructor
  · apply @knave_notknight Inhabitant
  · exact notknight_knave

theorem notknave_knightIff
  {A : Inhabitant}
 : A ∉ W.Knave ↔  A ∈ W.Knight := by
  constructor
  · exact notknave_knight
  · exact knight_notknave


-- hypothesis
/--
doc string for knave_interp
interpret things in terms of knaves
-/
macro "knave_interp" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic| ( (try rw [not_iff_not.symm] at $t1) ; simp only[knight_notknaveIff,not_not] at $t1)
)
/--
doc string for knave_interp
interpret things in terms of knaves
-/
-- goal , usually goal doesn't have Iff
macro "knave_interp" : tactic =>
do`(tactic| ((try rw [not_iff_not.symm]) ; simp only[knight_notknaveIff,not_not] )
)
/--
doc string for knave_interp
interpret things in terms of knaves
-/
-- *
macro "knave_interp" "at"  t1:Lean.Parser.Tactic.locationWildcard : tactic =>
do`(tactic| ( (try rw [not_iff_not.symm] at $t1) ; simp only[knight_notknaveIff,not_not] at $t1)
)


#check knave_notknightIff
-- hypothesis
macro "knight_interp" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic| ((try rw [not_iff_not.symm] at $t1 ); simp only[knave_notknightIff,not_not] at $t1)
)
-- goal , usually goal doesn't have Iff
macro "knight_interp" : tactic =>
do`(tactic| ((try rw [not_iff_not.symm]) ; simp only[knave_notknightIff,not_not] )
)
-- *
macro "knight_interp" "at"  t1:Lean.Parser.Tactic.locationWildcard : tactic =>
do`(tactic| ( (try rw [not_iff_not.symm] at $t1) ; simp only[knave_notknightIff,not_not] at $t1))


---- hypothesis
-- old , to be deleted
--macro "knight_interp" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
--do`(tactic| (rw [not_iff_not.symm] at $t1 ; simp only[knave_notknightIff,not_not] at $t1)
--)


-- redundant
-- *
macro "set_knight_to_knave" "at"  t1:Lean.Parser.Tactic.locationWildcard : tactic =>
  do`(tactic| simp only [knight_notknaveIff,not_not] at $t1)
-- goal , replaced by knave_interp
macro "set_knight_to_knave" : tactic =>
  do`(tactic| simp only [knight_notknaveIff,not_not])
-- hypothesis
macro "set_knight_to_knave" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic|
  simp only [knight_notknaveIff,not_not] at $t1)
#check KorKn
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
do`(tactic| cases (KorKn $t1)  )

macro "set_knight_or_knave" t1:term "with" t2:rcasesPat t3:rcasesPat  : tactic =>
do`(tactic| obtain $t2|$t3 := (KorKn $t1)  )
