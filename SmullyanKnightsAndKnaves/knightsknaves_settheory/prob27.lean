import SmullyanKnightsAndKnaves.knightsknaves
import SmullyanKnightsAndKnaves.knightsknaves_3
-- problem 27

-- newformalization
open settheory_approach
variable [DecidableEq Inhabitant]
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
  rw [not_iff_not.symm] at stC
  set_knave_to_knight at stC
  have CKnave := stC.mpr BKnight

  have oneK := stB.mp BKnight
  set_knight_or_knave A with AKnight AKnave
  have oneK := oneK.mp AKnight
  unfold oneKnight at oneK
  simp [AKnight, CKnave, BKnight] at oneK
  set_knave_to_knight  at oneK 
  simp [ CKnave, BKnight] at oneK
  contradiction

  set_knave_to_knight at AKnave
  rw [not_iff_not.symm] at oneK
  have notone := oneK.mp AKnave 
  unfold oneKnight at notone
  simp [AKnave, CKnave, BKnight] at notone
  set_knave_to_knight  at notone
  simp [AKnave] at notone
  contradiction

  set_knight_to_knave  at this
  have CKnight :=  stC.mpr this
  constructor ; assumption ; assumption

example
{inst2 : Fintype Inhabitant}
(stB : (B ∈ Knight) ↔ (A ∈ Knight ↔Knight.card = 1))
(stC : ( C ∈ Knight ↔ B ∈ Knave) )
(stCn : ( C ∈ Knave ↔ B ∈ Knight) )

  : B ∈ Knave ∧ C ∈ Knight := by 
  have BKnave : B ∈ Knave
  set_knave_to_knight
  intro BKnight
  have CKnave := stCn.mpr BKnight
  have stA := stB.mp BKnight
  have AKnave : A ∈ Knave
  set_knave_to_knight
  intro AKnight
  have KnightCard := stA.mp AKnight
  rw [Finset.card_eq_one] at KnightCard
  have ⟨a,ha⟩ := KnightCard 
  rw [ha] at AKnight
  rw [ha] at BKnight
  mem_finset at AKnight
  mem_finset at BKnight
  rw [←AKnight] at BKnight
  contradiction
  set_knave_to_knight at AKnave
  simp [AKnave] at stA
  apply stA
  rw [Finset.card_eq_one]
  use B
  -- back to the same point
  sorry
  sorry

example
{inst2 : Fintype Inhabitant}
(stB : (B ∈ Knight) ↔ (A ∈ Knight ↔ Knight = {A} ∨ Knight = {B} ∨ Knight = {C}))
(stC : ( C ∈ Knight ↔ B ∈ Knave) )
(stCn : ( C ∈ Knave ↔ B ∈ Knight) )

{all2 : ∀ (x : Inhabitant), x = A ∨ x = B ∨ x = C}

  : B ∈ Knave ∧ C ∈ Knight := by 
  have BKnave : B ∈ Knave
  set_knave_to_knight
  intro BKnight
  have CKnave := stCn.mpr BKnight
  have stA := stB.mp BKnight
  set_knight_or_knave A with AKnight AKnave
  have oneKnight := stA.mp AKnight
  rcases oneKnight with singleton|singleton|singleton
  · 
    rw [singleton] at BKnight
    mem_finset at BKnight
    contradiction
  
  · rw [singleton] at AKnight
    mem_finset at AKnight
    contradiction
  · rw [singleton] at AKnight
    mem_finset at AKnight
    contradiction

  have : Knight = {B} := by
    apply Finset.Subset.antisymm
    · have : Knight ⊆ ({A,B,C} : Finset Inhabitant)
      by_universe
      set_knave_to_knight at CKnave
      set_knave_to_knight at AKnave
      remove_top at this
      rw [Finset.pair_comm] at this
      remove_top at this

    · intro a h
      mem_finset at h ; rw [h] 
      assumption
  have AKnight : A ∈ Knight
  rw [stA]
  right ; left ; assumption
  contradiction

  have CKnight := stC.mpr BKnave
  constructor ; assumption ; assumption

#check Finset.card_insert_of_notMem
#check Finset.card_le_one_iff

/-
Suppose the stranger, instead of asking A what he is,
asked A, "How many knights are among you?" Again A
answers indistinctly. So the stranger asks B, "What did A
say?B replies, "A said that there is one knight among us."
Then C says, "Don't believe B; he is lying!"
Now what are B and C?
-/
example
(stB : B ∈ Knight ↔ ( A ∈ Knight ↔ Knight.card =1))
(stC : C ∈ Knight ↔ B ∈ Knave)
: B ∈ Knave ∧ C ∈ Knight := 
by 

  have BCdiff : B ∈ Knight ∧ C ∈ Knave ∨ B ∈ Knave ∧ C ∈ Knight := by 
    sorry
 /-
    rw [stC]
    rw [stCn]
    simp
    exact KorKn B
 -/

  -- we know that there is at least one knight, if A were a knight then they are two but this woudl contradict A's statement
  set_knight_or_knave A with AKnight AKnave
  · have : Knight.card ≠ 1 := by {
      rcases BCdiff with ⟨BKnight,CKnave⟩ |⟨BKnave, CKnight⟩ 
      ·
        intro OneKnight
        rw [Finset.card_eq_one] at OneKnight
        have ⟨x,xK⟩ := OneKnight 
        rw [xK] at AKnight
        mem_finset at AKnight
        rw [xK] at BKnight
        mem_finset at BKnight
        rw [←AKnight] at BKnight
        contradiction

      · intro OneKnight
        rw [Finset.card_eq_one] at OneKnight
        have ⟨x,xK⟩ := OneKnight 
        rw [xK] at AKnight
        mem_finset at AKnight
        rw [xK] at CKnight
        mem_finset at CKnight
        rw [←CKnight] at AKnight
        contradiction

    }
    simp [this] at stB
    rw [not_iff_not.symm] at stB
    simp at stB
    have BKnave := stB.mpr AKnight
    set_knight_to_knave at BKnave
    have BKnight := stC.mpr BKnave
    constructor
    assumption
    assumption

  · set_knave_to_knight at AKnave
    #check Finset.eq_singleton_iff_unique_mem
    simp [AKnave] at stB
    have : Knight.Nonempty := by {
      rcases BCdiff with h_1|h_1
      · have := h_1.left
        use B
      · use C
        exact h_1.right
      }
    have BorC: Knight = {B} ∨ Knight = {C} := by
      rcases BCdiff with h_1|h_1
      · left
        rw [Finset.eq_singleton_iff_nonempty_unique_mem]
        constructor
        assumption
        intro x
        intro xK
        rcases all x with h_2|h_2|h_2
        · rw [h_2] at xK
          contradiction
        · assumption
        · rw [h_2] at xK
          have := h_1.right
          contradiction

      · right
        rw [Finset.eq_singleton_iff_nonempty_unique_mem]
        constructor
        assumption
        intro x
        intro xK
        rcases all x with h_2|h_2|h_2
        · rw [h_2] at xK
          contradiction

        · rw [h_2] at xK
          have := h_1.left
          contradiction
        assumption
    have OneKnight : Knight.card =1 := by 
      rcases BorC with h_1|h_1
      · rw [h_1]
        rfl
      · rw [h_1]
        rfl

    knave_interp at stB
    simp [AKnave] at stB
    have BKnave : B ∈ Knave := by exact stBn.mpr OneKnight
    have CKnight : C ∈ Knight:= by exact stC.mpr BKnave 
    constructor
    assumption
    assumption

macro "all_cases_satisfy_goal3" t1:Lean.Parser.Tactic.elimTarget
: tactic =>
  do`(tactic|
  (rcases $t1 with h|h|h <;> (rw [h] ; assumption))
  )

macro "all_2_cases_satisfy_goal" t1:Lean.Parser.Tactic.elimTarget
: tactic =>
  do`(tactic|
  (rcases $t1 with h|h <;> (rw [h] ; assumption))
  )


syntax "all_cases_satisfy_goal_works" term : tactic
  macro_rules
    | `(tactic| all_cases_satisfy_goal_works $t1:term) =>
      `(tactic| first
        | (rw [($t1)]; assumption)  -- base case
        | (rcases ($t1) with h | h <;>
            first
            | (rw [h]; assumption)
            | all_cases_satisfy_goal_works h))


--syntax "all_cases_satisfy_goal_works" term : tactic
-- why does this not work, why do i have to do syntax ... then macro_rules , is a recursive macro not possible?
  macro "all_cases" t1:term : tactic
  =>    `(tactic| first
        | (rw [($t1)]; assumption)  -- base case
        | (rcases ($t1) with h | h <;>
            first
            | (rw [h]; assumption)
            | all_cases h))


  macro "all_cases_satisfy_goal" t1:Lean.Parser.Tactic.elimTarget : tactic =>
    `(tactic| cases $t1 <;> next h => rw [h]; assumption)


example
(stB : B ∈ Knight ↔ ( A ∈ Knight ↔ Knight.card =1))
(stC : C ∈ Knight ↔ B ∈ Knave)
: B ∈ Knave ∧ C ∈ Knight := 
by 
  have subsetKnight : {B} ⊆ Knight ∨ {C} ⊆ Knight 
  · set_knight_or_knave B with BKnight BKnave
    · left
      intro x h 
      mem_finset at h ; rw[h] ; assumption
    · have CKnight := stC.mpr BKnave
      right
      intro x h
      mem_finset at h ; rw[h] ; assumption
  
  set_knight_or_knave A with AKnight AKnave
  · simp [AKnight] at stB
    have twosetSubsetKnight : {A,B} ⊆ Knight ∨ {A,C} ⊆ Knight
    rcases subsetKnight with h|h
    · left
      intro x h'
      mem_finset at h'
      have : B ∈ Knight := by exact Finset.singleton_subset_iff.mp h
      all_cases_satisfy_goal h'
    · right
      intro x h'
      mem_finset at h'
      have : C ∈ Knight := by exact Finset.singleton_subset_iff.mp h
      cases h'
      all_cases_satisfy_goal h'
    have KnightCardGeTwo : Knight.card ≥ 2
    rcases twosetSubsetKnight with h|h
    #check Finset.card_le_card
    · have := Finset.card_le_card h
      simp at this
      assumption

    #check Finset.card_le_card
    · have := Finset.card_le_card h
      simp at this
      assumption
    have : Knight.card≠ 1
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
      set_knave_to_knight at stC
      simp [h] at stC
      knight_interp at stB 
      have notoneknight := stB.mp h
      have : Knight.card =1
      rw [Finset.card_eq_one]
      use B
    -- one of two options at this point
    -- either finset.eq_singleton_iff_unique_mem and use the all axiom
    -- or finset.subset.antisymm and prove knight subset of universe then remove top(can this option be made less tedious/repetitive?)
    /-
    apply Finset.Subset.antisymm
    · sorry
    · intro x h
      mem_finset at h
      rw [h] ; assumption
    -/
      rw [Finset.eq_singleton_iff_unique_mem]
      constructor
      assumption
      intro x h

      sorry
      sorry
    · sorry
