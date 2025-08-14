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
say? B replies, "A said that there is one knight among us."
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
(stB : (B ∈ Knight) ↔ (A ∈ Knight ↔ Knight = {A} ∨ Knight = {B} ∨ Knight = {C}))
(stC : ( C ∈ Knight ↔ B ∈ Knave) )
(stCn : ( C ∈ Knave ↔ B ∈ Knight) )

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
    mem_set at BKnight
    contradiction
  
  · rw [singleton] at AKnight
    mem_set at AKnight
    contradiction
  · rw [singleton] at AKnight
    mem_set at AKnight
    contradiction

  have : Knight = {B} := by
    apply Finset.Subset.antisymm
    · have : Knight ⊆ {A,B,C}
      by_universe
      set_knave_to_knight at CKnave
      set_knave_to_knight at AKnave
      remove_top at this
      rw [Finset.pair_comm] at this
      remove_top at this

    · intro a h 
      mem_set at h ; rw [h] 
      assumption
  have AKnight : A ∈ Knight
  rw [stA]
  right ; left ; assumption
  contradiction

  have CKnight := stC.mpr BKnave
  constructor ; assumption ; assumption

#check Finset.card_insert_of_not_mem
#check Finset.card_le_one_iff
example
(stB : B ∈ Knight ↔ ( A ∈ Knight ↔ Knight.card =1))
(stBn : B ∈ Knave ↔ ¬( A ∈ Knight ↔ Knight.card =1))
(stC : C ∈ Knight ↔ B ∈ Knave)
(stCn : C ∈ Knave ↔ B ∈ Knight)
: B ∈ Knave ∧ C ∈ Knight := 
by 

  have BCdiff : B ∈ Knight ∧ C ∈ Knave ∨ B ∈ Knave ∧ C ∈ Knight := by 
    rw [stC]
    rw [stCn]
    simp
    exact KorKn

  -- we know that there is at least one knight, if A were a knight then they are two but this woudl contradict A's statement
  set_knight_or_knave A with AKnight AKnave
  · have : Knight.card ≠ 1 := by {
      rcases BCdiff with ⟨BKnight,CKnave⟩ |⟨BKnave, CKnight⟩ 
      ·
        intro OneKnight
        rw [Finset.card_eq_one] at OneKnight
        have ⟨x,xK⟩ := OneKnight 
        rw [xK] at AKnight
        mem_set at AKnight
        rw [xK] at BKnight
        mem_set at BKnight
        rw [←AKnight] at BKnight
        contradiction

      · intro OneKnight
        rw [Finset.card_eq_one] at OneKnight
        have ⟨x,xK⟩ := OneKnight 
        rw [xK] at AKnight
        mem_set at AKnight
        rw [xK] at CKnight
        mem_set at CKnight
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

  · rw [inright_notinleftIff] at AKnave
    #check Finset.eq_singleton_iff_unique_mem
    simp [AKnave] at stBn
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
        rcases all x with h_2|h_2
        · rw [h_2] at xK
          contradiction
        · rcases h_2 with h_3|h_3
          · assumption
          · rw [h_3] at xK
            have := h_1.right
            contradiction

      · right
        rw [Finset.eq_singleton_iff_nonempty_unique_mem]
        constructor
        assumption
        intro x
        intro xK
        rcases all x with h_2|h_2
        · rw [h_2] at xK
          contradiction
        · rcases h_2 with h_3|h_3
          · rw [h_3] at xK
            have := h_1.left
            contradiction
          · assumption
    have OneKnight : Knight.card =1 := by 
      rcases BorC with h_1|h_1
      · rw [h_1]
        rfl
      · rw [h_1]
        rfl

    have BKnave : B ∈ Knave := by exact stBn.mpr OneKnight
    have CKnight : C ∈ Knight:= by exact stC.mpr BKnave 
    constructor
    assumption
    assumption
