import SmullyanKnightsAndKnaves.knightsknaves

import Lean
-- prob28
-- included in game as dsl_iknaveorknave

--Raymond Smullyan, what is the name of this book, problem 28

#check Finset.subset_of_eq
#check Finset.ssubset_iff_subset_ne
#check Finset.subset_iff

open Inhabitant

example
  (stA : A ∈ Knight ↔ (Knave:Finset Inhabitant).card ≥ 1)
  : A ∈ Knight ∧ B ∈ Knave:= by

  have AKnight : A ∈ Knight 
  · knave_interp
    intro AKnave
    knave_interp at stA
    simp at stA
    have := stA.mp AKnave
    rw [this] at AKnave
    contradiction
  have knaveNotEmpty := stA.mp AKnight
  simp at knaveNotEmpty
  --simp [Finset.nonempty_iff_ne_empty.symm] at knaveNotEmpty
  cases knaveNotEmpty
  expose_names
  --all_cases_satisfy_goal (all w)
  rcases all w with h'|h' 
  rw [h'] at h
  contradiction
  rw [h'] at h
  constructor ; assumption ; assumption

#check Finset.eq_univ_iff_forall
#check Finset.subset_insert_iff_of_notMem
#check Finset.subset_singleton_iff
#check Set.eq_empty_iff_forall_notMem
#checkFinset.eq_empty_of_forall_notMem

example
{stA : A ∈ Knight ↔ (A ∈ Knave ∨ B ∈ Knave)}
: A ∈ Knight ∧ B ∈ Knave := by 
--Let's start with proving that `A` is a knight. (use `have`)
  have AKnight : A ∈ Knight 
 -- Change the goal to `¬isKnave A` using the `knight_to_knave` tactic
  knave_interp
-- Assume `isKnave A`
  intro AKnave

-- Let's first prove `isKnave A ∨ isKnave B`. Type `∨` by \\or.
  have orexp:  A ∈ Knave or  B ∈ Knave
-- Choose which side to prove, `left` or `right`?
  left
  assumption
  -- `A`'s statement is true, so `A` is a knight.
  have AKnight := stA.mpr orexp
--But we already knew that `A` is a knave, `contradiction`.
  contradiction

-- `A` is a knight, so we can conclude `A`'s statement.

  have orexp :=  stA.mp AKnight
  /-
`{orexp}` can be simplified, using `simp` and the fact that `A` is a knight and that knights are not knaves.

  First, change `isKnave A` in `{orexp}` to `¬isKnight A` then use `simp` and the fact that `A` is a knight to simplify `{orexp}`
  -/
  knight_interp at orexp
  simp [AKnight] at orexp

-- Now close the goal
  knave_interp at orexp
  constructor
  assumption ; assumption
