import SmullyanKnightsAndKnaves.knightsknaves

-- prob28
example 
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

