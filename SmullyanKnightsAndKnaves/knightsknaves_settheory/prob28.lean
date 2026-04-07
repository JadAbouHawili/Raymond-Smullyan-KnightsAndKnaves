import SmullyanKnightsAndKnaves.knightsknaves

import Lean
-- prob28
-- included in game as dsl_iknaveorknave

--Raymond Smullyan, what is the name of this book, problem 28
set_option push_neg.use_distrib true

#check Finset.subset_of_eq
#check Finset.ssubset_iff_subset_ne
#check Finset.subset_iff

open Inhabitant

example
  (stA : A ∈ Knight ↔ (Knave:Finset Inhabitant).card ≥ 1)
  (stAn : A ∈ Knave ↔ (Knave : Finset Inhabitant).card < 1)
  : A ∈ Knight ∧ B ∈ Knave:= by
  rw [Nat.lt_one_iff] at stAn
  rw [Finset.card_eq_zero] at stAn

  have AKnight : A ∈ Knight :=by
    knave_interp
    intro AKnave
    have := stAn.mp AKnave
    rw [this] at AKnave
    contradiction
  have cardGEOne := stA.mp AKnight
  constructor
  assumption
  knight_interp
  intro BKnight

  #check Finset.eq_univ_iff_forall
  have subsetUniv: Knave ⊆ {A,B} := by
    by_universe
  knave_interp at BKnight
  knave_interp at AKnight
  -- make this into a custom tactic
  have : Knave ⊆ {B} := by
    exact (Finset.subset_insert_iff_of_notMem AKnight).mp subsetUniv
  have : (Knave :Finset Inhabitant) ⊆ ∅ := by 
   exact (Finset.subset_insert_iff_of_notMem BKnight).mp this
  simp at this
  rw [this] at cardGEOne
  contradiction

example
(all : ∀ (x : Inhabitant), x = A ∨ x = B)
  (stA : A ∈ Knight ↔ (@Knave Inhabitant).card ≥ 1)
  (stAn : A ∈ Knave ↔ (Knave : Finset Inhabitant).card < 1)
  : A ∈ Knight ∧ B ∈ Knave:= by
  rw [Nat.lt_one_iff] at stAn
  rw [Finset.card_eq_zero] at stAn

  have AKnight : A ∈ Knight :=by
    set_knight_to_knave
    intro AKnave
    have := stAn.mp AKnave
    rw [this] at AKnave
    contradiction

  have cardGEOne := stA.mp AKnight

  -- assuming B not knave gives contradiction
  #check Finset.subset_insert_iff_of_notMem
  #check Finset.subset_singleton_iff
  have ⟨w,winKnave⟩  :  ∃ w : Inhabitant, w ∈ Knave := by
    by_contra h'
    push_neg at h'
    #check Set.eq_empty_iff_forall_notMem
    have Knaveemp := Finset.eq_empty_of_forall_notMem h'
    rw [Knaveemp] at cardGEOne
    contradiction

  have BKnave : w=B := by
    rcases all w with h_1|h_2
    rw [h_1] at winKnave 
    contradiction
    assumption

  rw [BKnave] at winKnave
  constructor
  assumption
  assumption

example
{stA : A ∈ Knight ↔ (A ∈ Knave ∨ B ∈ Knave)}
: A ∈ Knight ∧ B ∈ Knave := by 
--Let's start with proving that `A` is a knight. (use `have`)
  have AKnight : A ∈ Knight 
 -- Change the goal to `¬isKnave A` using the `knight_to_knave` tactic
  set_knight_to_knave
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
