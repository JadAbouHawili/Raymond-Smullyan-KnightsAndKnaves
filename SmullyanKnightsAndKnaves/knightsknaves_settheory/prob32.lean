---- adapat to problems with only 2 inhabitants

--"
--Suppose instead, A and B say the following:
--A: All of us are knaves.
--B: Exactly one of us is a knave.
--Can it be determined what B is? Can it be determined what C is?
--"
import SmullyanKnightsAndKnaves.knightsknaves

-- exactly one of us is a knave
-- this can be represented as Knave = {A} ∨ Knave = {B} ∨ Knave = {C}
set_option push_neg.use_distrib true

#check Finset.mem_insert_coe
open settheory_approach

--A: All of us are knaves.
--B: Exactly one of us is a knave.
variable [DecidableEq Inhabitant]
example
{stA : A ∈ Knight ↔ (allKnave) }
{stAn : A ∈ Knave ↔ ¬ (allKnave) }
{stB: B ∈ Knight ↔ oneKnave }
{stBn: B ∈ Knave ↔ ¬ (oneKnave) }
  : A ∈ Knave ∧ C ∈ Knight := by

  {
--A: All of us are knaves.
--B: Exactly one of us is a knave.
  have AKnave : A ∈ Knave := by
    by_contra AKnight
    set_knave_to_knight at AKnight
    have knaves := stA.mp AKnight
    contradiction

  have notallknaves := stAn.mp AKnave
  constructor
  assumption
  set_knight_or_knave B with BKnight BKnave
  ·
    have oneKn := stB.mp BKnight 
    unfold oneKnave at oneKn
    simp [AKnave,BKnight,inleft_notinrightIff] at oneKn
    set_knight_to_knave 
    assumption

    /-
    unfold oneKnave at stBn
    rw [not_or] at stBn
    rw [not_or] at stBn
    by_contra CKnave 
    have first : ¬(A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knight) := by 
      intro ands
      exact CKnave ands.right.right
    have second : ¬(A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knight) := by 
      intro ands 
      exact CKnave ands.right.right
    have third : ¬( A ∈ Knight ∧ B ∈ Knight ∧ C ∈ Knave) := by 
      intro ands
      rw [inright_notinleftIff] at AKnave
      exact AKnave ands.left 
    have BKnave := stBn.mpr (And.intro first 
    (And.intro second third)) 
    contradiction
    -/
  ·
    unfold allKnave at notallknaves
    simp [AKnave,BKnave] at notallknaves
    set_knight_to_knave
    assumption
  }

#check not_eq_singleton_of_not_mem

theorem not_eq_singleton_already_full 
{K : Type}
{A B: K}
{Knave : Finset K}
(AneB : A ≠ B)
(AKnave : A ∈ Knave)

: Knave ≠ {B} := by
        intro knaveB 
        rw [knaveB] at AKnave
        #check Finset.mem_singleton
        rw [Finset.mem_singleton] at AKnave
        contradiction

#check card_eq_one_iff_singletons
#check card_eq
example
{h1 : A ∈ Knight ∨ A ∈ Knave }
{h2: B ∈ Knight ∨ B ∈ Knave }
{h3: C ∈ Knight ∨ C ∈ Knave }
{AneB : A≠ B}
{BneC : B≠ C}
{AneC : A≠ C}
-- Knave = {A,B,C} ???
-- similar to previous problem
{stA : A ∈ Knight  ↔ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave) }
{stB : B ∈ Knight ↔ Knave = {A} ∨ Knave = {B} ∨ Knave = {C}}
  : A ∈ Knave ∧ C ∈ Knight := by
    have h2' := h2
--  A: All of us are knaves.
--  B: Exactly one of us is a knave.
    have AKnave : A ∈ Knave := by
      by_contra AKnight
      have AKnight :=notright_left h1 AKnight
      have := stA.mp AKnight
      contradiction

    constructor
    assumption
    set_knight_or_knave B with BKnight BKnave
    · have knavesingle := stB.mp BKnight
      #check not_eq_singleton_of_not_mem
      have knaveneB : Knave ≠ {B} := not_eq_singleton_already_full AneB AKnave
      have knaveneC : Knave ≠ {C} := not_eq_singleton_already_full AneC AKnave
      simp [knaveneB, knaveneC] at knavesingle
      #check ne_of_mem_of_not_mem 
      #check full_singleton
      have := not_in_of_singleton knavesingle (by symm ; exact AneC)
      rw [inleft_notinrightIff] 
      assumption

    · by_contra CnKnight
      have CKnave := notleft_right h3 CnKnight
      have AKnight := stA.mpr (by constructor ; assumption ; constructor ; assumption ; assumption)
      contradiction

example {K : Type} {A B : Finset K} (h : A⊆B) : A.card ≤ B.card := by 
  exact Finset.card_le_card h

example
{K : Type}
{A B C : K}
{inst : DecidableEq K}
{S : Finset K}
{hS : S = {A,B,C}}
: A ∈ S
:= by
  rw [hS]
  apply Finset.mem_insert_self
example
{K : Type}
{A B C : K}
{inst : DecidableEq K}
{S : Finset K}
{hS : S = {A,B,C}}
: C ∈ S
:= by
  rw [hS]
  is_mem

-- working on this...
example
  {A B C : Inhabitant}
  {inst2 : Fintype Inhabitant}
  {inst : DecidableEq Inhabitant}
{AneB : A≠ B}
{BneC : B≠ C}
{AneC : A≠ C}
{all : ∀ (x : Inhabitant), x = A ∨ x = B ∨ x = C}
-- similar to previous problem
{stA : A ∈ Knight  ↔ (Knave= {A,B,C}) }
{stAn : A ∈ Knave ↔ ¬ (Knave = {A,B,C}) }
{stB : B ∈ Knight ↔ Knave = {A} ∨ Knave = {B} ∨ Knave = {C}}
  : A ∈ Knave ∧ C ∈ Knight := by

  -- same argument as prob 31
  -- try different approach, Knave={A,B,C} then A ∈ Knave . so we have the implication A ∈ Knight → A ∈ Knave
  have AKnave : A ∈ Knave := by
    by_contra AKnight
    rw [notinright_inleftIff] at AKnight
    have everyoneknave := stA.mp AKnight
    have AKnave: A ∈ Knave := by
     rw [everyoneknave]
     is_mem
    contradiction
--   Suppose instead, A and B say the following: 
--A: All of us are knaves. 
--B: Exactly one of us is a knave. 
-- saying there is one knight among us has the effect that everyone else is a knave, sounds like a nice level
--Can it be determined what B is? Can it be determined what 
--C is? 
  set_knight_or_knave B with h_3 h_4
  · have oneknave := stB.mp h_3 
    -- knave already full so from oneknave and AKnave we can conclude Knave = {A}

    -- think about cardinality
    #check eq_singleton_card_one
    #check Finset.card_eq_one

    -- now do cases all and show that Knave = {A}, so C must be a knight
    -- make this its own theorem
    have oneCard : Knave.card = 1 := by 
      #check card_eq_one_iff_singletons_univ
      #check card_eq_one_iff_singletons_univ
      #check singleton_iff_card_eq_one
      exact (card_eq_one_iff_singletons all).mpr oneknave
    rw [Finset.card_eq_one] at oneCard
    #check eq_singleton_card_one
    #check card_eq_one_iff_singletons

-------
-- the all specifies that any inhabitant is either A,B,C and no one else. This is setting the universe. Moreover, we state that they ar enot the same inhabitant. What we get from this is a series of theorems that intuitively hold true.
    -- card=1, already full?
    #check already_full

    have CKnight: C ∉ Knave := by 
      intro CKnave
      #check Finset.eq_singleton_iff_unique_mem
      have ⟨a,aKnave⟩:= oneCard 
      rw [Finset.eq_singleton_iff_unique_mem] at aKnave
      have Aa := aKnave.right A AKnave
      have Ca := aKnave.right C CKnave
      rw [←Ca] at Aa 
      contradiction
    #check eq_singleton_card_one
    set_knave_to_knight  at CKnight
    exact And.intro AKnave CKnight
      --rw [Finset.eq_singleton_iff_unique_mem] at this 
    --#check not_eq_singleton_of_not_mem
    ---- could also do not_eq_singleton_of_not_mem
    --have : Knave ≠ {B} := by 
    --  intro BKnave 
    --  rw [Finset.eq_singleton_iff_unique_mem] at BKnave
    --  exact disjoint h h_1 BKnave.left
    --simp [this] at oneknave
  · 
    -- need full2 where A ∈ S, B ∈ S, S.card=2 , A ≠ B , B ≠ C, C ≠ A then C ∉ S. can be used here because of ¬Knave={A,B,C}
    #check full2
    -- card equal two part, well knave ≠ {A} etc.. and we have all, so knave.card is not equal to one. its not equal to 3 either because ¬Knave={A,B,C}. its bounded above by 3, so the only options left are 2 or 0... this is tedious
    -- another way for card equal two part, Knave.card ≤ 3 , not equal three so ≤ 2. has two elements in it i.e ≥ 2 so its two.
    -- make a general theorem where
    #check Finset.ssubset_iff
    #check Finset.ssubset_iff_subset_ne
    #check Finset.card_lt_card
    #check univ_iff_all

    #check Finset.card_insert_le
    have U: Finset.univ = {A, B, C} := (univ_iff_all).mpr all 
    have knavesubU : Knave ⊆ {A,B,C} := by 
      apply set_subset_univ all
      assumption

    have knavenotall := stAn.mp AKnave
    have CKnight : C ∈ Knight := by 
      by_contra CKnave
      rw [notinleft_inrightIff] at CKnave  
      have : {A,B,C} ⊆ Knave := by
        intro x
        intro xIn
        rcases all x with h_2|h_2
        · rw [h_2]
          assumption
        · rcases h_2 with h_3|h_3
          · rw [h_3]
            assumption
          · rw [h_3]
            assumption
      #check Set.eq_of_subset_of_subset
      #check Finset.eq_of_subset_of_card_le
      #check Finset.eq_of_subset_of_card_le
      #check Finset.card_le_card
      have : Knave = {A,B,C}:= by 
        exact Eq.symm (Finset.Subset.antisymm this knavesubU)
      contradiction
    exact And.intro AKnave CKnight
/-
     more complicated solution
    have U: Finset.univ = {A, B, C} := (univ_iff_all inst2 inst).mpr all 
    have knavesubU : Knave ⊆ {A,B,C} := by 
      rw [←U]
      apply Finset.subset_univ
    have knavenotall := stAn.mp AKnave
    have knavessub := Finset.ssubset_iff_subset_ne.mpr ⟨knavesubU,knavenotall⟩ 
    have knavecardlt3 :=  Finset.card_lt_card knavessub
    #check Nat.le_of_lt_succ
    have : 1≤2 := by norm_num
    unfold Nat.le at this
    #check Nat.lt_iff_le_pred
    simp at knavecardlt3
    have : ({A,B,C}: Finset Inhabitant).card=3 := by{
      rw [Finset.card_eq_three]
      use A
      use B
      use C
    }
    rw [this] at knavecardlt3

    have knavele2: Knave.card ≤ 2 := by 
      #check Nat.lt_iff_le_pred
      exact (Nat.lt_iff_le_pred three_pos).mp knavecardlt3

    have card_ge_2 :Knave.card ≥ 2 := by

      have ABsub: {A,B} ⊆ Knave := by
        intro x
        intro xAB
        #check mem2_iff_or_finset
        rw [mem2_iff_or_finset] at xAB
        cases xAB
        rw [h_2]
        assumption
        rw [h_2]
        assumption
      #check Finset.card_le_of_subset
      have : ({A,B}: Finset Inhabitant).card =2 := by 
        rw [Finset.card_eq_two]
        use A
        use B
      have conc := Finset.card_le_of_subset ABsub
      rw [this] at conc
      assumption
    #check Nat.le_antisymm
    #check full
    have : C ∉ Knave := @full2 Inhabitant _ _ _ Knave inst inst2 AKnave h_1 (Nat.le_antisymm knavele2 card_ge_2) AneB BneC AneC all

    --have : C ∉ Knave := full2 Knave AKnave h_1 (Nat.le_antisymm knavele2 card_ge_2) AneB BneC AneC all

    -- and done............
    rw [notinright_inleftIff h3 h] at this
    exact And.intro AKnave this 
-/
