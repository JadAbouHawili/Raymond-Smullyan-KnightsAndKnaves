import SmullyanKnightsAndKnaves.knightsknaves
-- problem 27

#check Finset.card_insert_of_not_mem
#check Finset.card_le_one_iff

        #check ne_eq
        #check ne_false_of_eq_true
        #check ne_true_of_eq_false

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
def oneKnight {A B C : Inhabitant} : Prop:=   (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight)

example
{A B C : Inhabitant}
--(h : Knight ∩ Knave = ∅ )
(stB : (B ∈ Knight) ↔ (A ∈ Knight ↔ @oneKnight A B C))
--(stBn : (B ∈ Knave) → (A ∈ Knight → ¬ (
--  (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight)) ) )
(stC : ( C ∈ Knight ↔ B ∈ Knave) )
--(stnC : ( C ∈ Knave → B ∈ Knight) )

  : B ∈ Knave ∧ C ∈ Knight := by 
  have : ¬B ∈ Knight 
  intro BKnight
  knave_to_knight B at stC
  knight_to_knave C at stC
  rw [not_iff_not] at stC  
  have CKnave := stC.mpr BKnight

  have oneK := stB.mp BKnight
  knight_or_knave A with AKnight AKnave
  have oneK := oneK.mp AKnight
  unfold oneKnight at oneK
  simp [AKnight, CKnave, BKnight] at oneK
  knave_to_knight A at oneK 
  knave_to_knight B at oneK 
  simp [ CKnave, BKnight] at oneK
  contradiction

  knave_to_knight A at AKnave
  rw [not_iff_not.symm] at oneK
  have notone := oneK.mp AKnave 
  unfold oneKnight at notone
  simp [AKnave, CKnave, BKnight] at notone
  knave_to_knight A at notone
  simp [AKnave] at notone

  knight_to_knave B at this
  simp [this,stC]

#check eq_or_lt_of_le
#check eq_iff_le_not_lt
#check Finset.card_le_one_iff

      #check Set.subset_insert_iff_of_not_mem 
      #check Set.subset_singleton_iff_eq
#check Nat.le_of_eq
#check ({1,2} : Multiset ℕ)

#check Set.insert
#check Set.eq_of_mem_singleton 
--
#check Multiset.mem_singleton
        #check Finset.eq_of_mem_singleton
#check Set.eq_of_mem_singleton 
#check Set.subset_insert_iff_of_not_mem 

#check Set.subset_insert_iff_of_not_mem
#check Set.subset_insert_iff_of_not_mem
#check Set.Subsingleton
#check Set.subsingleton_or_nontrivial 

    #check Finset.card_pos
    #check Finset.card_ne_zero_of_mem
  #check Classical.not_iff


#check Set.mem_setOf_eq 
#check Finset.mem_insert 
#check Finset.mem_singleton
#check       Finset.mem_insert
#check    Finset.card_eq_two
#check    Finset.card
#check Finset.card_le_card
#check Finset.mem_insert_self
    #check Finset.ssubset_iff_subset_ne

  #check Ne.symm
  #check Nat.ne_of_lt
  #check Finset.card_singleton

example  
{A B C : Inhabitant}
(h : Knight ∩ Knave = ∅ )
(Or : ∀(x : Inhabitant), x ∈ Knight ∨ x ∈ Knave)
(all : ∀(x :Inhabitant), x = A ∨ x = B ∨ x = C)
(stB : B ∈ Knight ↔ ( A ∈ Knight ↔ Knight.card =1))
(stBn : B ∈ Knave ↔ ¬( A ∈ Knight ↔ Knight.card =1))
(stC : C ∈ Knight ↔ B ∈ Knave)
(stCn : C ∈ Knave ↔ B ∈ Knight)
(AneB : A ≠ B)
(BneC : B ≠ C)
(AneC : A ≠ C)
: B ∈ Knave ∧ C ∈ Knight := 
by 

  have BCdiff : B ∈ Knight ∧ C ∈ Knave ∨ B ∈ Knave ∧ C ∈ Knight := by 
    rw [stC]
    rw [stCn]
    simp
    exact Or B

  -- we know that there is at least one knight, if A were a knight then they are two but this woudl contradict A's statement
  rcases (Or A) with AKnight|AKnave 
  · have : Knight.card ≠ 1 := by {
      rcases BCdiff with h_1|h_1
      · 
        by_contra OneKnight
        rw [Finset.card_eq_one] at OneKnight
        have ⟨x,xK⟩ := OneKnight 

        have BeqX : B=x := by 
          rw [xK] at h_1
          rw [Finset.mem_singleton] at h_1
          exact h_1.left

        rw [xK] at AKnight
        rw [Finset.mem_singleton] at AKnight
        rw [←BeqX] at AKnight
        exact AneB AKnight
      · intro OneKnight
        rw [Finset.card_eq_one] at OneKnight
        have ⟨x,xK⟩ := OneKnight 
        have CeqX : C=x := by 
          rw [xK] at h_1
          rw [Finset.mem_singleton] at h_1
          exact h_1.right
        rw [xK] at AKnight
        rw [Finset.mem_singleton] at AKnight
        rw [←CeqX] at AKnight
        exact AneC AKnight
    }
    simp [this] at stBn
    have BKnave := stBn.mpr AKnight
    have BKnight := stC.mpr BKnave
    constructor
    assumption
    assumption

  · rw [inright_notinleftIff (Or A) h] at AKnave
    #check Finset.card_eq_one
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
            exfalso
            exact disjoint h xK h_1.right
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
            exfalso
            exact disjoint h xK h_1.left
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

#check Set.mem_setOf_eq 
#check Finset.mem_insert

#check Finset.card_eq_one
#check Finset.eq_singleton_iff_unique_mem
#check Finset.ssubset_iff_subset_ne
#check Finset.subset_singleton_iff
#check Finset.card_pos
#check Finset.card_eq_one
#check Finset.card_eq_two
#check Finset.card_pos
#check Finset.Nonempty
#check eq_true
#check card_finset_fin_le
#check Finset.card_ne_zero_of_mem
#check Fin

#check Set.toFinset
#check and_iff_right_iff_imp
