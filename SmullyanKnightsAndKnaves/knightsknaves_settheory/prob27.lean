import SmullyanKnightsAndKnaves.knightsknaves_3
-- problem 27

-- newformalization
open Inhabitant
/-
Suppose the stranger, instead of asking A what he is,
asked A, "How many knights are among you?" Again A
answers indistinctly. So the stranger asks B, "What did A
say?B replies, "A said that there is one knight among us."
Then C says, "Don't believe B; he is lying!"
Now what are B and C?
-/

example
(stB : (B ∈ Knight) ↔ (A ∈ Knight ↔ oneKnight))
(stC : ( C ∈ Knight ↔ B ∈ Knave) )
  : B ∈ Knave ∧ C ∈ Knight := by
  have : ¬B ∈ Knight
  intro BKnight
  knight_interp at stC
  have CKnave := stC.mpr BKnight

  have oneK := stB.mp BKnight
  knight_or_knave A with AKnight AKnave
  have oneK := oneK.mp AKnight
  unfold oneKnight at oneK
  simp [AKnight, CKnave, BKnight] at oneK
  knight_interp  at oneK 
  simp [ CKnave, BKnight] at oneK
  contradiction

  knight_interp at AKnave
  rw [not_iff_not.symm] at oneK
  have notone := oneK.mp AKnave 
  unfold oneKnight at notone
  simp [AKnave, CKnave, BKnight] at notone
  knight_interp  at notone
  simp [AKnave] at notone
  contradiction

  knave_interp  at this
  have CKnight :=  stC.mpr this
  constructor ; assumption ; assumption

/-
Suppose the stranger, instead of asking A what he is,
asked A, "How many knights are among you?" Again A
answers indistinctly. So the stranger asks B, "What did A
say?B replies, "A said that there is one knight among us."
Then C says, "Don't believe B; he is lying!"
Now what are B and C?
-/


example
(stB : (B ∈ Knight) ↔ (A ∈ Knight ↔(Knight : Finset Inhabitant).card = 1))
(stC : ( C ∈ Knight ↔ B ∈ Knave) )

  : B ∈ Knave ∧ C ∈ Knight := by 
  have BKnave : B ∈ Knave
  knight_interp
  intro BKnight
  knight_interp at stC
  have CKnave := stC.mpr BKnight
  have stA := stB.mp BKnight
  have AKnave : A ∈ Knave
  knight_interp
  intro AKnight
  have KnightCard := stA.mp AKnight
  rw [Finset.card_eq_one] at KnightCard
  have ⟨a,ha⟩ := KnightCard 
  rw [ha] at AKnight
  rw [ha] at BKnight
  simp at AKnight
  simp at BKnight
  rw [←AKnight] at BKnight
  contradiction
  knight_interp at AKnave
  simp [AKnave] at stA
  have : (Knight : Finset Inhabitant).card = 1
   
  rw [Finset.card_eq_one]
  use B
  rw [Finset.eq_singleton_iff_unique_mem]
  constructor
  assumption
  intro x h
  rcases all x with h'|h'|h'
  rw [h'] at h ; contradiction
  assumption
  rw [h'] at h ; contradiction

  contradiction
  have CKnight := stC.mpr BKnave
  exact And.intro BKnave CKnight

example
(stB : (B ∈ Knight) ↔ (A ∈ Knight ↔ Knight = {A} ∨ Knight = {B} ∨ Knight = {C}))
(stC : ( C ∈ Knight ↔ B ∈ Knave) )
(stCn : ( C ∈ Knave ↔ B ∈ Knight) )
  : B ∈ Knave ∧ C ∈ Knight := by 
  have BKnave : B ∈ Knave
  knight_interp
  intro BKnight
  have CKnave := stCn.mpr BKnight
  have stA := stB.mp BKnight
  knight_or_knave A with AKnight AKnave
  have oneKnight := stA.mp AKnight
  have : {A,B} ⊆ Knight := by
    intro x h 
    simp at h 
    all_cases_satisfy_goal h
  -- usage of grind and such to make reasoning easier for user , make all_cases_satisfy_goal even more powerful?
  rcases oneKnight with singleton|singleton|singleton
  · 
    rw [singleton] at BKnight
    simp at BKnight
  · rw [singleton] at AKnight
    simp at AKnight
  · rw [singleton] at AKnight
    simp at AKnight

  have : Knight = {B} := by
    apply Finset.Subset.antisymm
    · have : Knight ⊆ ({A,B,C} : Finset Inhabitant)
      by_universe
      knight_interp at CKnave
      knight_interp at AKnave
      remove_top at this
      rw [Finset.pair_comm] at this
      remove_top at this

    · intro a h
      simp at h ; rw [h] 
      assumption
  have AKnight : A ∈ Knight
  rw [stA]
  right ; left ; assumption
  contradiction

  have CKnight := stC.mpr BKnave
  constructor ; assumption ; assumption

#check Finset.card_insert_of_notMem
#check Finset.card_le_one_iff












-----------------------------------------------------------------------------------------------------------------------
-- the below are long winded compared to the above

/-
Suppose the stranger, instead of asking A what he is,
asked A, "How many knights are among you?" Again A
answers indistinctly. So the stranger asks B, "What did A
say?B replies, "A said that there is one knight among us."
Then C says, "Don't believe B; he is lying!"
Now what are B and C?
-/
-- knowing B would reveal C , so that shouldbe our focus , but to know B we need to deal with A
example
(stB : B ∈ Knight ↔ ( A ∈ Knight ↔ (Knight : Finset Inhabitant).card =1))
(stC : C ∈ Knight ↔ B ∈ Knave)
: B ∈ Knave ∧ C ∈ Knight := 
by 

  have BCdiff : B ∈ Knight ∧ C ∈ Knave ∨ B ∈ Knave ∧ C ∈ Knight := by 
    sorry
  -- we know that there is at least one knight, if A were a knight then they are two but this would contradict A's statement
  knight_or_knave A with AKnight AKnave
  · have : Knight.card ≠ 1 := by {
      rcases BCdiff with ⟨BKnight,CKnave⟩ |⟨BKnave, CKnight⟩ 
      ·
        intro OneKnight
        rw [Finset.card_eq_one] at OneKnight
        obtain ⟨x : Inhabitant ,xK⟩ := OneKnight 
        rw [xK] at AKnight
        simp at AKnight
        rw [xK] at BKnight
        simp at BKnight
        rw [←AKnight] at BKnight
        contradiction

      · intro OneKnight
        rw [Finset.card_eq_one] at OneKnight
        have ⟨x,xK⟩ := OneKnight 
        rw [xK] at AKnight
        simp at AKnight
        rw [xK] at CKnight
        simp at CKnight
        rw [←CKnight] at AKnight
        contradiction

    }
    simp [this] at stB
    knight_interp at stB
    have BKnave := stB.mpr AKnight
    knave_interp at BKnave
    have BKnight := stC.mpr BKnave
    constructor
    assumption
    assumption

  · knight_interp at AKnave
    #check Finset.eq_singleton_iff_unique_mem
    simp [AKnave] at stB
    have : (Knight : Finset Inhabitant).card = 1 := by
      rw [Finset.card_eq_one]  
      rcases BCdiff with h|h
      use B 
      apply Finset.Subset.antisymm
      knight_interp at h
      have : Knight ⊆ {A,B,C} := by
        by_universe
      grind
      grind

      use C
      apply Finset.Subset.antisymm
      knight_interp at h
      have : Knight ⊆ {A,B,C} := by
        by_universe
      grind
      grind

    knave_interp at stB
    have BKnave : B ∈ Knave := by exact stB.mpr this
    have CKnight : C ∈ Knight:= by exact stC.mpr BKnave
    constructor
    assumption
    assumption

example
(stB : B ∈ Knight ↔ ( A ∈ Knight ↔ (Knight : Finset Inhabitant).card =1))
(stC : C ∈ Knight ↔ B ∈ Knave)
: B ∈ Knave ∧ C ∈ Knight := 
by 
  have subsetKnight : {B} ⊆ Knight ∨ {C} ⊆ Knight 
  · knight_or_knave B with BKnight BKnave
    · left
      intro x h 
      simp at h ; rw[h] ; assumption
    · have CKnight := stC.mpr BKnave
      right
      intro x h
      simp at h ; rw[h] ; assumption
  
  knight_or_knave A with AKnight AKnave
  · simp [AKnight] at stB
    have twosetSubsetKnight : {A,B} ⊆ Knight ∨ {A,C} ⊆ Knight
    rcases subsetKnight with h|h
    · left
      intro x h'
      simp at h'
      have : B ∈ Knight := by exact Finset.singleton_subset_iff.mp h
      all_cases_satisfy_goal h'
    · right
      intro x h'
      simp at h'
      have : C ∈ Knight := by exact Finset.singleton_subset_iff.mp h
      all_cases_satisfy_goal h'
    have KnightCardGeTwo : (Knight : Finset Inhabitant).card ≥ 2
    rcases twosetSubsetKnight with h|h
    #check Finset.card_le_card
    · have := Finset.card_le_card h
      simp at this
      assumption

    #check Finset.card_le_card
    · have := Finset.card_le_card h
      simp at this
      assumption
    have : (Knight : Finset Inhabitant).card≠ 1
    exact Ne.symm (Nat.ne_of_lt KnightCardGeTwo)
    knave_interp at stB
    have BKnave := stB.mpr this
    have CKnight := stC.mpr BKnave
    constructor
    assumption ; assumption

  · knave_interp at stB 
    simp [AKnave] at stB
    rcases subsetKnight with h|h 
    · simp at h 
      knight_interp at stC
      simp [h] at stC
      knight_interp at stB 
      have notoneknight := stB.mp h
      have : (Knight : Finset Inhabitant).card =1
      rw [Finset.card_eq_one]
      use B

      rw [Finset.eq_singleton_iff_unique_mem]
      constructor
      assumption
      intro x h
      rcases all x with h'|h'|h'
      rw [h'] at h ; contradiction
      assumption
      rw [h'] at h ; contradiction

      contradiction

    · simp at h
      grind 
