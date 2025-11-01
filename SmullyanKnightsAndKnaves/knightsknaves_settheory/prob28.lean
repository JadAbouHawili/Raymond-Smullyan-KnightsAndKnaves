import SmullyanKnightsAndKnaves.knightsknaves

import Lean
-- prob28
-- included in game as dsl_iknaveorknave

set_option push_neg.use_distrib true

   #check Finset.subset_of_eq
  #check Finset.ssubset_iff_subset_ne
  #check Finset.subset_iff

open settheory_approach



theorem univ_iff_all2
{K : Type}
{inst : Fintype K} {inst2 : DecidableEq K} {A B : K}   : Finset.univ = ({A,B} : Finset K) ↔  ∀ (x : K), x = A ∨ x = B := by
  constructor
  ·
    intro U
    intro x
    have xinU := Finset.mem_univ x
    rw [U] at xinU
    mem_finset at xinU
    assumption

  · intro all
    apply Finset.eq_of_subset_of_card_le
    intro x
    intro hx
    rcases all x with h|h
    · rw [h]
      is_mem
    · rw [h]
      is_mem
    apply Finset.card_le_card
    apply Finset.subset_univ


example
  {inst : DecidableEq Inhabitant}
  {inst2 : Fintype Inhabitant}
(all : ∀ (x : Inhabitant), x = A ∨ x = B)
  (stA : A ∈ Knight ↔ Knave.card ≥ 1)
  (stAn : A ∈ Knave ↔ Knave.card < 1)
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
  constructor
  assumption
  set_knave_to_knight
  intro BKnight


  have U : Finset.univ = ({A,B} : Finset Inhabitant):= univ_iff_all2.mpr all
  have subsetUniv: Knave ⊆ {A,B} := by 
    rw [←U]
    exact Finset.subset_univ Knave
  set_knight_to_knave at BKnight
  set_knight_to_knave at AKnight
  -- make this into a custom tactic
  have : Knave ⊆ {B} := by exact (Finset.subset_insert_iff_of_not_mem AKnight).mp subsetUniv
  have : Knave ⊆ ∅ := by exact (Finset.subset_insert_iff_of_not_mem BKnight).mp this
  simp at this
  rw [this] at cardGEOne
  contradiction

example
  {inst : DecidableEq Inhabitant}
  {inst2 : Fintype Inhabitant}
(all : ∀ (x : Inhabitant), x = A ∨ x = B)
  (stA : A ∈ Knight ↔ Knave.card ≥ 1)
  (stAn : A ∈ Knave ↔ Knave.card < 1)
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
  #check Finset.subset_insert_iff_of_not_mem
  #check Finset.subset_singleton_iff
  have ⟨w,winKnave⟩  :  ∃ w : Inhabitant, w ∈ Knave := by 
    by_contra h' 
    push_neg at h'
    #check Set.eq_empty_iff_forall_not_mem
    have Knaveemp := Finset.eq_empty_of_forall_not_mem h'
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
  {inst : DecidableEq Inhabitant}
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
  set_knave_to_knight at orexp
  simp [AKnight] at orexp

-- Now close the goal
  set_knight_to_knave at orexp
  constructor
  assumption ; assumption

--Raymond Smullyan, what is the name of this book, problem 28
-- statement of `A` formalized with more complicated expression
example
  {inst : DecidableEq Inhabitant}
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
      set_knight_to_knave at h_1
      simp [h_1] at conc
      assumption
    · constructor
      assumption ; assumption
  · set_knight_or_knave B with h_1 h_1
    · have := not_iff_not.mpr stx
      set_knave_to_knight at h_2
      have this2:= this.mp h_2
      contrapose this2
      push_neg
      right
      left
      constructor
      set_knight_to_knave at h_2
      assumption;assumption
    · constructor
      · have := not_iff_not.mpr stx 
        rw [not_or] at this
        push_neg at this
        set_knave_to_knight at h_2
        have this2 := this.mp (h_2)
        contrapose this2
        push_neg
        right
        right
        set_knight_to_knave at this2
        constructor
        assumption ;assumption
      · assumption
}
#check not_iff_not

-- rewriting, making it neat
theorem organized 
  --sets
  { x y : Inhabitant}
  {inst : DecidableEq Inhabitant}
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
