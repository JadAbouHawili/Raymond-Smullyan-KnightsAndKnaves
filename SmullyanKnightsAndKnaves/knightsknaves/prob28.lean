import SmullyanKnightsAndKnaves.knightsknaves
import SmullyanKnightsAndKnaves.dsl_knights_knaves
import Lean
-- prob28

    #check Nat.lt_one_iff
    #check Finset.card_eq_zero
    #check Finset.subset_singleton_iff
   #check Finset.subset_of_eq
   #check Finset.empty_subset
  #check Finset.ssubset_iff_subset_ne
  #check Finset.subset_def
  #check Finset.subset_iff
theorem eq_of_or_not
{A B w : Type}
{p : Type → Prop}
(AorB : w = A or w = B)
(npA : ¬(p A))
(pw : p w)

: w = B := by 
  rcases AorB with h|h
  rw [h] at pw
  contradiction

  assumption

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
  -- can knave.card be replaced with A ∈ Knave ∨ B ∈ Knave? A ∈ Knave ∨ B ∈ Knave beaing true means that A ∈ Knave , or B ∈ knave or both. this can be shown on the truth table
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

--variable {K : Type}

--A: 'At least one of us is a knave.'
--What are A and B? "
def AtLeastOneIsKnave (A B : Islander) : Prop := (A.isKnave) ∨ (B.isKnave)
example 
{A B : Islander}
{stA : A said (A.isKnave or B.isKnave)}
: A.isKnight and B.isKnave := by 
   
  sorry

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
--
--(uni : Knight ∪ Knave) 
-- theres x and y, x says at least one of us is a knave
  -- diff formalization to stx
  --(stx : (A ∈ Knight) ↔ (A ∈ Knight ∧  B ∈ Knave)
   --                 ∨ (A ∈ Knave ∧ B ∈ Knight)
   --                 ∨ (A ∈ Knave ∧ B ∈ Knave)  )

--Raymond Smullyan, what is the name of this book, problem 28
example 
  { K : Type}
  {x y : K}
  {inst : DecidableEq K}
  (Knight : Finset K ) (Knave : Finset K) 
  --(uni : Knight ∪ Knave) 
  (h : Knight ∩ Knave = ∅ )
  -- theres x and y, x says at least one of us is a knave
  --rules of the game, i.e knights tell the truth but knaves lie

  (h'' : ∀ (x: K), x ∈ Knight ∨ x ∈ Knave)
  (stx : (x ∈ Knight) ↔ (x ∈ Knight ∧  y ∈ Knave)
                    ∨ (x ∈ Knave ∧ y ∈ Knight)
                    ∨ (x ∈ Knave ∧ y ∈ Knave)  )
--goal
  : x ∈ Knight ∧ y ∈ Knave:= by
  {
  --show_goals
  rcases ( h'' x) with h_1|h_2
  · rcases h'' y with h_3|h_4
    · constructor
      assumption
      -- since goal is impossible to directly prove, we neeed a proof by contradiction
      have stx2 := stx
      rw [not_iff_not.symm] at stx
      have conc := stx2.mp h_1
      -- notice that the negation of the right hand side of stx2 is true
      have this := eq_true h_1
      have this2:= eq_true h_3
      
      --have this3 := inleft_notinright h_1
      simp[this,this2] at conc
      have this3:= inleft_notinright h h_1
      have this4:= eq_false this3
      simp[this4] at conc
      assumption

    · constructor
      assumption ; assumption
  · cases h'' y
    · have := not_iff_not.mpr stx
      have this2:= this.mp (inright_notinleft h h_2)
      contrapose this2
      simp
      right
      left
      constructor
      assumption;assumption
    · constructor
      · have := not_iff_not.mpr stx 
        have this2 := this.mp (inright_notinleft h h_1)
        contrapose this2
        simp
        right
        right
        constructor
        assumption ;assumption
      · assumption

  }
#check not_iff_not

---- old formalization, not organized
--Statement 
--  --sets
--  (Knight : Set K ) (Knave : Set K) 
--  --(uni : Knight ∪ Knave) 
--  (h : Knight ∩ Knave = ∅ )
--  (h1 : Xor' (x ∈ Knight) (x ∈ Knave) ) 
--  (h2: Xor' (y ∈ Knight)  (y ∈ Knave) )
--  -- theres x and y, x says at least one of us is a knave
--  --rules of the game, i.e knights tell the truth but knaves lie
--  (stx : x ∈ Knight → (x ∈ Knight ∧  y ∈ Knave)
--                    ∨ (x ∈ Knave ∧ y ∈ Knight)
--                    ∨ (x ∈ Knave ∧ y ∈ Knave)  )
--  (stnx : x ∈ Knave → ¬ ( (x ∈ Knight ∧  y ∈ Knave)
--                    ∨ (x ∈ Knave ∧ y ∈ Knight)
--                    ∨ (x ∈ Knave ∧ y ∈ Knave) ) )
----goal
--  : x ∈ Knight ∧ y ∈ Knave:= by
--  {
--
--   --rw [Xor'] at h1
--   --rw [Xor'] at h2
--   --exact h1
--   --rw [Eq.rfl h1 ( (x ∈ Knight ∧ x ∉ Knave)  ∨ (x ∈ Knave ∧ x ∉ Knight ) )] at h1
--   --cases h1
--   --cases h2
--
--   -- no need to take two cases, explain to the user why!!!!
--   cases h1 
--   --cases h2
--   
--   have contr :=  stx h_1.left 
--   rcases contr
--
--   exact h_2
--
--   cases h_2 
--   have contr2 := mem_inter h_1.left h_3.left 
--   rw [h] at contr2
--   contradiction
--
--
--   have contr2 := mem_inter h_1.left h_3.left 
--   rw [h] at contr2
--   contradiction
--
--   have contr := stnx h_1.left
--   push_neg at contr
--   have yK := contr.right.left h_1.left 
--   have yk2 : y ∈ Knave := by {
--     rw [Xor'] at h2
--     cases h2 
--     have contr2:= h_2.left
--     contradiction
--
--     exact h_2.left
--   }
--  
--   have target := contr.right.right
--   have helpp := contrapositive target
--   push_neg at helpp
--   have done := helpp yk2
--   have := h_1.left
--   contradiction
--   --contrapose at target
--   --push_neg
--   --push_neg at target
--   --contrapose target
--   --push_neg at target
--  }
--
--
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
--goal
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
  have yNKnight := ynKnight xKnave
  have yNKnave := ynKnave xKnave
  cases h2 with 
    | inl h_1 => 
      obtain ⟨yKnight,_⟩:= h_1 
      contradiction
    | inr h_1 =>
      obtain ⟨yKnave,_⟩:= h_1 
      contradiction

}
-- no sorryAX
#print axioms organized



-- prob28
example 
  {K : Type}
  {A B : K}
  {inst : DecidableEq K}
  {inst2 : Fintype K}
  (Knight : Finset K)
  (Knave : Finset K) 
  (h : Knight ∩ Knave = ∅ )
(all : ∀ (x : K), x = A ∨ x = B)
  (h'' : ∀ (x: K), x ∈ Knight ∨ x ∈ Knave)
  -- can knave.card be replaced with A ∈ Knave ∨ B ∈ Knave? A ∈ Knave ∨ B ∈ Knave beaing true means that A ∈ Knave , or B ∈ knave or both. this can be shown on the truth table
  (stA : A ∈ Knight ↔ Knave.card ≥ 1)
  (stAn : A ∈ Knave ↔ Knave.card < 1)
  : A ∈ Knight ∧ B ∈ Knave:= by

  -- show that Knave.card<1 means Knave.card=0 which means Knave empty
  have : Knave.card<1 → Knave = ∅ := by {
    intro Klt1
    rw [Nat.lt_one_iff] at Klt1
    rw [Finset.card_eq_zero] at Klt1
    assumption
  }

-- can form the statement A ∈ Knave → Knave=∅ 
-- i.e A ∈ Knave → False
  have AnKnave := _root_.trans stAn.mp this 
  have AKnaveFalse : A ∈ Knave → False := by {
    intro AKnave 
    have Knaveemp:= AnKnave AKnave
    rw [Knaveemp] at AKnave
    contradiction
  }
  -- when doing rw, if its implies then if the conclusionpattern matching then the hypothesis are new goals added
  simp  at AKnaveFalse 
  -- get Knave.card ≥ 1
  -- get Knave ⊆ {A,B} , Knave ⊆ {B}, Knave.card ≤ 1
  #check Finset.subset_insert_iff_of_not_mem
  have U : Finset.univ = {A,B}:= univ_iff_all2.mpr all
   

  -- either do like after the separator or this
  have atleastoneKnave := stA.mp (by rw [inleft_notinrightIff (h'' A) h] ; assumption)
   
  ------------
  -- this can be made simpler by a proper introduction to the idea of universe.
  have : Knave ⊆ {A,B} := by 
    rw [←U]
    apply Finset.subset_univ

  rw [Finset.subset_insert_iff_of_not_mem AKnaveFalse] at this 

  have KleB:= Finset.card_le_card this
  have oneB : ({B} : Finset K).card =1 := by 
    rw [Finset.card_eq_one] 
    use B
  rw [oneB] at KleB 
  have Kge := stA.mp (notinright_inleft (h'' A) AKnaveFalse)
   
  have oneKnave := Nat.le_antisymm KleB Kge
  have knavenonemp : Knave ≠ ∅ := by 
    intro emp
    rw [emp] at oneKnave
    contradiction
   
  #check Finset.ssubset_iff_subset_ne
  #check Finset.subset_def
  #check Finset.subset_iff

  -- make it into its own theorem
  -- no need Finset.subset_singleton_iff is it

  /-
     for Knave ⊆ {A,B} ↔ Knave = ∅ ∨ Knave ={A,B}. this is not true
  -/
  have : Knave ⊆ {B} ↔ Knave =∅ ∨ Knave ={B} := by  
    constructor
    ·  
      intro sub 
      -- idk
      exact Finset.subset_singleton_iff.mp this
    · intro or
      cases or 
      · rw [h_1]
        apply Finset.empty_subset

      #check Finset.subset_of_eq
      exact Finset.subset_of_eq h_1

-------------
  have AnKnave : A ∉ Knave := by 
    intro AKnave
    have AKnave2 := AKnave
    rw [inright_notinleftIff (h'' A) h]  at AKnave
    have le1 := (Function.mt stA.mpr) AKnave
    push_neg at le1
    rw [Nat.lt_one_iff] at le1
    rw [Finset.card_eq_zero] at le1
    rw [le1] at AKnave2
    contradiction
  rw [notinright_inleftIff (h'' A) h] at AnKnave 
  
  have atleast := stA.mp AnKnave
  have BnKnight : B ∉ Knight := by
    intro BKnight
    have Knaveemp := all2_in_one_other_empty h all AnKnave BKnight
    rw [Knaveemp] at atleast
    contradiction
  
  rw [notinleft_inrightIff (h'' B) h] at BnKnight
  exact And.intro AnKnave BnKnight


-----------------
-- prob28
example 
  {K : Type}
  {A B : K}
  {inst : DecidableEq K}
  {inst2 : Fintype K}
  (Knight : Finset K)
  (Knave : Finset K) 
  (h : Knight ∩ Knave = ∅ )
(all : ∀ (x : K), x = A ∨ x = B)
  (h'' : ∀ (x: K), x ∈ Knight ∨ x ∈ Knave)
  -- can knave.card be replaced with A ∈ Knave ∨ B ∈ Knave? A ∈ Knave ∨ B ∈ Knave beaing true means that A ∈ Knave , or B ∈ knave or both. this can be shown on the truth table
  (stA : A ∈ Knight ↔ Knave.card ≥ 1)
  (stAn : A ∈ Knave ↔ Knave.card < 1)
  : A ∈ Knight ∧ B ∈ Knave:= by

  -- show that Knave.card<1 means Knave.card=0 which means Knave empty
  have : Knave.card<1 → Knave = ∅ := by {
    intro Klt1
    rw [Nat.lt_one_iff] at Klt1
    rw [Finset.card_eq_zero] at Klt1
    assumption
  }

-- can form the statement A ∈ Knave → Knave=∅ 
-- i.e A ∈ Knave → False
  have AnKnave := _root_.trans stAn.mp this 
  have AKnaveFalse : A ∈ Knave → False := by {
    intro AKnave 
    have Knaveemp:= AnKnave AKnave
    rw [Knaveemp] at AKnave
    contradiction
  }
  -- when doing rw, if its implies then if the conclusionpattern matching then the hypothesis are new goals added
  simp  at AKnaveFalse 
  -- get Knave.card ≥ 1
  -- get Knave ⊆ {A,B} , Knave ⊆ {B}, Knave.card ≤ 1
  #check Finset.subset_insert_iff_of_not_mem
  have U : Finset.univ = {A,B}:= univ_iff_all2.mpr all
   

  -- either do like after the separator or this
  have atleastoneKnave := stA.mp (by rw [inleft_notinrightIff (h'' A) h] ; assumption)
   
  ------------
  -- this can be made simpler by a proper introduction to the idea of universe.
  have : Knave ⊆ {A,B} := by 
    rw [←U]
    apply Finset.subset_univ

  rw [Finset.subset_insert_iff_of_not_mem AKnaveFalse] at this 

  have KleB:= Finset.card_le_card this
  have oneB : ({B} : Finset K).card =1 := by 
    rw [Finset.card_eq_one] 
    use B
  rw [oneB] at KleB 
  have Kge := stA.mp (notinright_inleft (h'' A) AKnaveFalse)
   
  have oneKnave := Nat.le_antisymm KleB Kge
  have knavenonemp : Knave ≠ ∅ := by 
    intro emp
    rw [emp] at oneKnave
    contradiction
   
  #check Finset.ssubset_iff_subset_ne
  #check Finset.subset_def
  #check Finset.subset_iff

  -- make it into its own theorem
  -- no need Finset.subset_singleton_iff is it

  /-
     for Knave ⊆ {A,B} ↔ Knave = ∅ ∨ Knave ={A,B}. this is not true
  -/
  have : Knave ⊆ {B} ↔ Knave =∅ ∨ Knave ={B} := by  
    constructor
    ·  
      intro sub 
      -- idk
      exact Finset.subset_singleton_iff.mp this
    · intro or
      cases or 
      · rw [h_1]
        apply Finset.empty_subset

      #check Finset.subset_of_eq
      exact Finset.subset_of_eq h_1

-------------
  have AnKnave : A ∉ Knave := by 
    intro AKnave
    have AKnave2 := AKnave
    rw [inright_notinleftIff (h'' A) h]  at AKnave
    have le1 := (Function.mt stA.mpr) AKnave
    push_neg at le1
    rw [Nat.lt_one_iff] at le1
    rw [Finset.card_eq_zero] at le1
    rw [le1] at AKnave2
    contradiction
  rw [notinright_inleftIff (h'' A) h] at AnKnave 
  
  have atleast := stA.mp AnKnave
  have BnKnight : B ∉ Knight := by
    intro BKnight
    have Knaveemp := all2_in_one_other_empty h all AnKnave BKnight
    rw [Knaveemp] at atleast
    contradiction
  
  rw [notinleft_inrightIff (h'' B) h] at BnKnight
  exact And.intro AnKnave BnKnight

