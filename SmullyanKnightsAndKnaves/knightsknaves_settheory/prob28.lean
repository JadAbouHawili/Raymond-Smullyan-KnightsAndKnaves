import SmullyanKnightsAndKnaves.knightsknaves

import Lean
-- prob28
-- included in game as dsl_iknaveorknave

set_option push_neg.use_distrib true

#check Finset.subset_of_eq
#check Finset.ssubset_iff_subset_ne
#check Finset.subset_iff

open Inhabitant


section
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
  have U : Finset.univ = ({A,B} : Finset Inhabitant):= by
    rfl 
  have subsetUniv: Knave ⊆ {A,B} := by 
    rw [←U]
    exact Finset.subset_univ Knave
  set_knight_to_knave at BKnight
  set_knight_to_knave at AKnight
  -- make this into a custom tactic
  have : Knave ⊆ {B} := by exact (Finset.subset_insert_iff_of_notMem AKnight).mp subsetUniv
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


open Lean Parser Elab Tactic
elab "show_goal" t:tactic : tactic => do
  logInfoAt t m!"⊢ {(← Elab.Tactic.getMainTarget)}"
  evalTactic t

def getTacs (t1 : Syntax) : Array Syntax :=
  match t1 with
    | .node _ ``tacticSeq #[.node _ ``tacticSeq1Indented #[.node _ `null args]] =>
      args.filter (! ·.isOfKind `null)
    | _ => #[t1]

elab "show_goals1 " tacs:tacticSeq : tactic => do
  let tacs := getTacs tacs
  for t in tacs do
    evalTactic (← `(tactic| show_goal $(⟨t⟩)))

elab "show_goals " tacs:tacticSeq : tactic => do
  let tacs := getTacs tacs
  let _ ← tacs.mapM fun t => do
    match t with
      | `(tactic| · $ts) => evalTactic (← `(tactic| · show_goals1 $(⟨ts.raw⟩)))
      | _ => evalTactic (← `(tactic| show_goals1 $(⟨t⟩)))


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

--Raymond Smullyan, what is the name of this book, problem 28
-- statement of `A` formalized with more complicated expression
example
  (stx : (A ∈ Knight) ↔ (A ∈ Knight ∧  B ∈ Knave)
                    ∨ (A ∈ Knave ∧ B ∈ Knight)
                    ∨ (A ∈ Knave ∧ B ∈ Knave)  )
  : (A ∈ Knight) and (B ∈ Knave):= by
  {
  set_knight_or_knave A with h_1 h_2
  · set_knight_or_knave B with h_3 h_4 
    · constructor
      assumption

      have stx2 := stx
      rw [not_iff_not.symm] at stx
      have conc := stx2.mp h_1
      -- notice that the negation of the right hand side of stx2 is true
      simp[h_1,h_3] at conc
      knave_interp at h_1
      simp [h_1] at conc
      assumption
    · constructor
      assumption ; assumption
  · set_knight_or_knave B with h_1 h_1
    · have := not_iff_not.mpr stx
      knight_interp at h_2
      have this2:= this.mp h_2
      contrapose this2
      --push_neg
      right
      left
      constructor
      knave_interp at h_2
      assumption;assumption
    · constructor
      · have := not_iff_not.mpr stx 
        rw [not_or] at this
        push_neg at this
        knight_interp at h_2
        have this2 := this.mp (h_2)
        contrapose this2
        push_neg
        right
        right
        knave_interp at this2
        constructor
        assumption ;assumption
      · assumption
}
#check not_iff_not

-- rewriting, making it neat
theorem organized 
  --sets
  { x y : Inhabitant}
  (h1 : Xor' (x ∈ Knight) (x ∈ Knave) ) 
  (h2: Xor' (y ∈ Knight)  (y ∈ Knave) )
  -- theres x and y, x says at least one of us is a knave
  --rules of the game, i.e knights tell the truth but knaves lie
  (stx : x ∈ Knight → (x ∈ Knight ∧  y ∈ Knave)
                    ∨ (x ∈ Knave ∧ y ∈ Knight)
                    ∨ (x ∈ Knave ∧ y ∈ Knave)  )
  (stnx : x ∈ Knave → ¬ ( (x ∈ Knight ∧  y ∈ Knave)
                    ∨ (x ∈ Knave ∧ y ∈ Knight)
                    ∨ (x ∈ Knave ∧ y ∈ Knave) ) )
  : x ∈ Knight ∧ y ∈ Knave:= by
{ 
--show_goals
cases h1 with
| inl h_1 =>
  obtain ⟨xKnight, xnKnave⟩ := h_1 
  have xTruth := stx xKnight
  cases xTruth with 
  | inl h_1 => exact h_1
  | inr h_1 => cases h_1 with 
               | inl h_1 =>
               obtain ⟨xKnave,yKnight⟩ := h_1
               contradiction

               | inr h_1 => 
               obtain ⟨xKnave,yKnave⟩ := h_1
               contradiction

| inr h_1 =>
  obtain ⟨xKnave, xnKnight⟩ := h_1  
  have xLie := stnx xKnave
  push_neg at xLie
  obtain ⟨notneeded,ynKnight,ynKnave⟩:= xLie 
  simp [xKnave] at ynKnight
  simp [xKnave] at ynKnave
  cases h2 with
    | inl h_1 =>
      obtain ⟨yKnight,_⟩:= h_1 
      contradiction
    | inr h_1 =>
      obtain ⟨yKnave,_⟩:= h_1 
      contradiction
}
end
