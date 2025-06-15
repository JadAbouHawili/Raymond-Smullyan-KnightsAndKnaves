import SmullyanKnightsAndKnaves.knightsknaves
--import SmullyanKnightsAndKnaves.dsl_knights_knaves
import Lean
-- prob28
-- included in game as dsl_iknaveorknave

set_option push_neg.use_distrib true

   #check Finset.subset_of_eq
  #check Finset.ssubset_iff_subset_ne
  #check Finset.subset_iff
theorem eq_of_or_not
{A B w : Type}
{p : Type → Prop}
(AorB : w = A ∨ w = B)
(npA : ¬(p A))
(pw : p w)

: w = B := by 
  rcases AorB with h|h
  rw [h] at pw
  contradiction

  assumption
example {P : Prop} (h : P) (h' : ¬P) : False := by 
  contradiction
example 
  {K : Type}
  {A B : K}
  {inst : DecidableEq K}
  {inst2 : Fintype K}
  (Knight : Finset K)
  (Knave : Finset K) 
  (h : Knight ∩ Knave = ∅ )
  (knavenonemp : Knave ≠ ∅)
(all : ∀ (x : K), x = A ∨ x = B)
  (h'' : ∀ (x: K), x ∈ Knight ∨ x ∈ Knave)
  (stA : A ∈ Knight ↔ Knave.card ≥ 1)
  (stAn : A ∈ Knave ↔ Knave.card < 1)
  : A ∈ Knight ∧ B ∈ Knave:= by
  #check Nat.lt_one_iff
  rw [Nat.lt_one_iff] at stAn
  rw [Finset.card_eq_zero] at stAn

-- can form the statement A ∈ Knave → Knave=∅ 
-- i.e A ∈ Knave → False
  have AnKnave : A ∈ Knave → False :=by
    intro AKnave
    have := stAn.mp AKnave
    rw [this] at AKnave
    contradiction
  simp  at AnKnave
  -- get Knave.card ≥ 1
  -- get Knave ⊆ {A,B} , Knave ⊆ {B}, Knave.card ≤ 1
  -- have not on both sides of stAn
  #check not_iff_not
  have notstAn:= not_iff_not.mpr stAn
  have atLeastKnave := notstAn.mp AnKnave
  simp at atLeastKnave

  -- assuming B not knave gives contradiction
  #check Finset.subset_insert_iff_of_not_mem
  #check Finset.subset_singleton_iff
  have U : Finset.univ = ({A,B} : Finset K):= univ_iff_all2.mpr all
  have ⟨w,winKnave⟩  :  ∃ w : K, w ∈ Knave := by 
    by_contra h' 
    push_neg at h'
    #check Set.eq_empty_iff_forall_not_mem
    have Knaveemp := Finset.eq_empty_of_forall_not_mem h'
    contradiction
  #check eq_of_or_not
  have AnKnave : ¬A ∈ Knave := by 
    exact AnKnave 


  have BKnave : w=B := by 
    rcases all w with h_1|h_2
    rw [h_1] at winKnave 
    contradiction

    assumption 
  rw [BKnave] at winKnave
  constructor
  rw [inleft_notinrightIff (h'' A) h]
  assumption ; assumption

#check all2_in_one_other_empty

example
  {K : Type}
  {A B : K}
  {Knight : Finset K}
  {Knave : Finset K}
  {inst : DecidableEq K}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{h2: B ∈ Knight ∨ B ∈ Knave }
{stA : A ∈ Knight  ↔ ((A ∈ Knave) ∨ (B ∈ Knave)) }
  : A ∈ Knight ∧ B ∈ Knave := by
  {
  -- book way, can't be further optimized
    have AnKnave: A ∉ Knave := by 
      intro AKnave
      have AOrB : A ∈ Knave ∨ B ∈ Knave := by left ; exact AKnave 
      have AKnight := stA.mpr AOrB
      exact disjoint h AKnight AKnave

    have AKnight := notinright_inleft h1 AnKnave 
    constructor
    · assumption
    · have AknOrB := stA.mp AKnight
      exact notleft_right AknOrB AnKnave 
  }


--open Lean Parser Elab Tactic
--elab "show_goal" t:tactic : tactic => do
--  logInfoAt t m!"⊢ {(← Elab.Tactic.getMainTarget)}"
--  evalTactic t
--
--def getTacs (t1 : Syntax) : Array Syntax :=
--  match t1 with
--    | .node _ ``tacticSeq #[.node _ ``tacticSeq1Indented #[.node _ `null args]] =>
--      args.filter (! ·.isOfKind `null)
--    | _ => #[t1]
--
--elab "show_goals1 " tacs:tacticSeq : tactic => do
--  let tacs := getTacs tacs
--  for t in tacs do
--    evalTactic (← `(tactic| show_goal $(⟨t⟩)))
--
--elab "show_goals " tacs:tacticSeq : tactic => do
--  let tacs := getTacs tacs
--  let _ ← tacs.mapM fun t => do
--    match t with
--      | `(tactic| · $ts) => evalTactic (← `(tactic| · show_goals1 $(⟨ts.raw⟩)))
--      | _ => evalTactic (← `(tactic| show_goals1 $(⟨t⟩)))

--Raymond Smullyan, what is the name of this book, problem 28
-- statement of `A` formalized with more complicated expression
example 
  { K : Type}
  {x y : K}
  {inst : DecidableEq K}
  (Knight : Finset K ) (Knave : Finset K) 
  (h : Knight ∩ Knave = ∅ )
  (h'' : ∀ (x: K), x ∈ Knight ∨ x ∈ Knave)
  (stx : (x ∈ Knight) ↔ (x ∈ Knight ∧  y ∈ Knave)
                    ∨ (x ∈ Knave ∧ y ∈ Knight)
                    ∨ (x ∈ Knave ∧ y ∈ Knave)  )
  : x ∈ Knight ∧ y ∈ Knave:= by
  {
  rcases ( h'' x) with h_1|h_2
  · rcases h'' y with h_3|h_4
    · constructor
      assumption

      have stx2 := stx
      rw [not_iff_not.symm] at stx
      have conc := stx2.mp h_1
      -- notice that the negation of the right hand side of stx2 is true
      have this := eq_true h_1
      have this2:= eq_true h_3

      simp[this,this2] at conc
      have this3:= inleft_notinright h h_1
      have this4:= eq_false this3
      simp[this4] at conc
      assumption

    · constructor
      assumption ; assumption
  · rcases h'' y with h_1|h_1
    · have := not_iff_not.mpr stx
      have this2:= this.mp (inright_notinleft h h_2)
      contrapose this2
      push_neg
      right
      left
      constructor
      assumption;assumption
    · constructor
      · have := not_iff_not.mpr stx 
        rw [not_or] at this
        push_neg at this
        have this2 := this.mp (inright_notinleft h h_2)
        contrapose this2
        push_neg
        right
        right
        constructor
        assumption ;assumption
      · assumption
}
#check not_iff_not

-- rewriting, making it neat
theorem organized 
  --sets
  {K : Type}
  { x y : K}
  (Knight : Set K ) (Knave : Set K)
  (h : Knight ∩ Knave = ∅ )
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
