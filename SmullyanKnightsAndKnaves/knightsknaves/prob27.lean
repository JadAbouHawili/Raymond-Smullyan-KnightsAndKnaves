import SmullyanKnightsAndKnaves.knightsknaves
-- problem 27

-- let's try cardinality formalization
#check Function.Bijective
#check Function.Bijective

-- use this instead of whatever was being used
--1. Finset.card_insert_of_not_mem.{u_1} {α : Type u_1} {s : Finset α} {a : α} [inst✝ : DecidableEq α] (h : a ∉ s) :
--     (insert a s).card = s.card + 1
#check Finset.card_insert_of_not_mem
#check Finset.card_le_one_iff

        #check ne_eq
        #check ne_false_of_eq_true
        #check ne_true_of_eq_false

-- newformalization
example
{K : Type}
{A B C : K}
  {inst : DecidableEq K}
  (Knight : Finset K ) (Knave : Finset K)
(h : Knight ∩ Knave = ∅ )
(h1 : A ∈ Knight ∨ A ∈ Knave ) 
(h2: B ∈ Knight ∨ (B ∈ Knave) )
(h3: C ∈ Knight ∨ C ∈ Knave )
(stB : (B ∈ Knight) ↔ (A ∈ Knight ↔
  (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight) ) )
--(stBn : (B ∈ Knave) → (A ∈ Knight → ¬ (
--  (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight)) ) )
(stC : ( C ∈ Knight ↔ B ∈ Knave) )
--(stnC : ( C ∈ Knave → B ∈ Knight) )

  : B ∈ Knave ∧ C ∈ Knight := by 
  -- formalizing solution from book
  -- statement of C implies that B and C are different type
  have : B ∈ Knight ∧ C ∈ Knave ∨ B ∈ Knave ∧ C ∈ Knight := 
    by
    have COr := h3
    rcases h3 with CKnight|CKnave
    -- C Knight
    · have := stC.mp CKnight
      right
      constructor
      assumption ; assumption
    -- C Knave
    · rw [not_iff_not.symm] at stC
      --rw [NotKnight_KnaveIff h COr] at stC
      #check notinleft_inrightIff COr h
      rw [notinleft_inrightIff COr h] at stC
      have := stC.mp CKnave
      rw [notinright_inleftIff h2 h] at this
      left
      constructor
      assumption; assumption

  cases h1
  · sorry
  · have distrib:= And.intro h_1 this
    #check and_or_left
    rw [and_or_left] at distrib  
    sorry





#check eq_or_lt_of_le
    #check eq_iff_le_not_lt
    #check Finset.card_le_one_iff
    #check Nat.le_of_eq
    #check Finset.card_le_one_iff

      #check Set.subset_singleton_iff_eq
      #check Set.subset_insert_iff_of_not_mem 
      #check Set.subset_singleton_iff_eq
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

-- proper formalization using cardinality lemmas
--inductive Inhabitant | A : Inhabitant | B : Inhabitant | C : Inhabitant --| dontknow : Person 
--inductive Inhabitant 
--|A :Inhabitant
--|B :Inhabitant
--|C :Inhabitant

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

/-


    -- prove instead ssubset
    #check Finset.ssubset_iff_subset_ne
-/
  #check Ne.symm
  #check Nat.ne_of_lt
  #check Finset.card_singleton

example  
{Inhabitant : Type}
{A B C : Inhabitant}
[inst : DecidableEq Inhabitant]
(Knight : Finset Inhabitant ) 
(Knave : Finset Inhabitant)
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
      cases BCdiff
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
        contradiction
      · by_contra OneKnight
        rw [Finset.card_eq_one] at OneKnight
        have ⟨x,xK⟩ := OneKnight 
        have CeqX : C=x := by 
          rw [xK] at h_1
          rw [Finset.mem_singleton] at h_1
          exact h_1.right
        rw [xK] at AKnight
        rw [Finset.mem_singleton] at AKnight
        rw [←CeqX] at AKnight
        contradiction
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
      cases BCdiff
      · have := h_1.left 
        use B 
      · use C
        exact h_1.right
      }
    have BorC: Knight = {B} ∨ Knight = {C} := by 
      cases BCdiff
      · left
        rw [Finset.eq_singleton_iff_nonempty_unique_mem] 
        constructor
        assumption 
        intro x
        intro xK
        cases all x
        · rw [h_2] at xK
          contradiction
        · cases h_2
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
        cases all x
        · rw [h_2] at xK
          contradiction
        · cases h_2
          · rw [h_3] at xK
            exfalso
            exact disjoint h xK h_1.left
          · assumption
    have OneKnight : Knight.card =1 := by 
      cases BorC
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
--#check Finset.card_le_of_subset
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

--def A : Person := Person.Knight ∨ Person.Knave
--def B : Person := Person.Knight ∨ Person.Knave
--def C : Person := Person.Knight ∨ Person.Knave

#check Set.toFinset
#check and_iff_right_iff_imp
