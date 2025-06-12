import SmullyanKnightsAndKnaves.dsl_knights_knaves


-- prob 28
--A: 'At least one of us is a knave.'
--What are A and B?
--`A` says 'I am a knave or `B` is a knave'.

open Islander
example 
{A B : Islander}
{stA : A said (A.isKnave or B.isKnave)}
: A.isKnight and B.isKnave := by 
--Let's start with proving that `A` is a knight. (use `have`)
  have AKnight : A.isKnight 
 -- Change the goal to `¬isKnave A` using the `knight_to_knave` tactic
  knight_to_knave
-- Assume `isKnave A`
  intro AKnave

-- Let's first prove `isKnave A ∨ isKnave B`. Type `∨` by \\or.
  have orexp: isKnave A or isKnave B
-- Choose which side to prove, `left` or `right`?
  left
  assumption
  -- `A`'s statement is true, so `A` is a knight.
  have AKnight := said_knight stA orexp
--But we already knew that `A` is a knave, `contradiction`.
  contradiction

-- `A` is a knight, so we can conclude `A`'s statement.

  have orexp := knight_said stA AKnight
  /-
`{orexp}` can be simplified, using `simp` and the fact that `A` is a knight and that knights are not knaves.

  First, change `isKnave A` in `{orexp}` to `¬isKnight A` then use `simp` and the fact that `A` is a knight to simplify `{orexp}`
  -/
  knave_to_knight at orexp
  simp [AKnight] at orexp

-- Now close the goal
  knight_to_knave at orexp
  constructor
  assumption ; assumption

