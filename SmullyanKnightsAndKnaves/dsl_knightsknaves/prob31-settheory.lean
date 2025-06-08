import SmullyanKnightsAndKnaves.knightsknaves
import SmullyanKnightsAndKnaves.dsl_knights_knaves

open settheory_approach
#check Knight
example

  {inst3 : DecidableEq Type}
  {A B C : Inhabitant}
  {inst : DecidableEq Inhabitant}
  {inst2 : Fintype Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
  {all : Finset.univ = {A,B,C}}
  --{all : ∀(x : Inhabitant), x = A ∨ x = B ∨ x = C}

{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{h2: B ∈ Knight ∨ B ∈ Knave }
{h3: C ∈ Knight ∨ C ∈ Knave }
{stA : A ∈ Knight  ↔ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave) }
{stB: B ∈ Knight ↔ (Knight = {A} ∨ Knight = {B} ∨ Knight = {C}) }
{stBn: B ∈ Knave ↔ ¬ (Knight = {A} ∨ Knight = {B} ∨ Knight = {C}) }
  : Solution A B C Knight Knave:= by

  have AKnave : A ∈ Knave := by {
      #check iff_iff_implies_and_implies
      have := (iff_iff_implies_and_implies).mp stA
      by_contra AKnight
      rw [notinright_inleftIff h1 h] at AKnight
      have AKnave := stA.mp AKnight
      have := AKnave.left
      contradiction
      --exact IamKnave h h1 (by simp[AKnight,AKnave.left] )
      --exact disjoint h AKnight AKnave.left 
    }
  have BKnight : B ∈ Knight := by 
    by_contra BKnave
    have notallKnaves := stAn.mp AKnave
   -- rw [notinleft_inrightIff] at BKnave <;> try assumption
    #check inleft_notinrightIff
    have : ¬(B ∈ Knight) := by assumption
    --rw [inleft_notinrightIff (either B )] at this
    set_knight_to_knave B at this
    --simp at BKnave
    --set_knight_to_knave at BKnave
    --rw [notinleft_inrightIff h2 h] at BKnave
    simp [AKnave,BKnave] at notallKnaves
    -- stB is equivalent to Knight.card = 1
    -- have a theorem which says given the universe, Knight.card = 1, and the first element in not in knight and the second as well then the third has to be. this idea of a universe need to be explicitly explained.
    have : Knight ⊆ Finset.univ := by exact Finset.subset_univ Knight
    rw [all] at this 
    rw [inright_notinleftIff h1 h] at AKnave
    rw [inright_notinleftIff h2 h] at BKnave

  -- Set.subset_insert_iff_of_not_mem.{u} {α : Type u} {a : α} {s t : Set α} (ha : a ∉ s) : s ⊆ insert a t ↔ s ⊆ t

    #check Finset.subset_insert_iff_of_not_mem
    #check Finset.subset_insert_iff_of_not_mem AKnave
--    simp [AKnave,BKnave] at this
    #check (Finset.subset_insert_iff_of_not_mem AKnave).mp this
--    have smaller :=      (Finset.subset_insert_iff_of_not_mem AKnave).mp this

    have helper: {A,B,C} = insert A ({B,C} : Finset Inhabitant) := by rfl
    rw [helper] at this
    -- name is too long? or make the user understand the naming convention
    rw [(Finset.subset_insert_iff_of_not_mem AKnave)] at this
    rw [(Finset.subset_insert_iff_of_not_mem BKnave)] at this
    have Csubset : {C} ⊆ Knight := by
    -- make this into a theorem, C ∈ Knight so the singleton subset of knight. mem_singleton_subset
      intro x
      intro xC
      rw[Finset.mem_singleton] at xC
      rw [xC]
      exact (notright_left h3 notallKnaves )
      
    have : Knight = {C} := by exact Finset.Subset.antisymm this Csubset

    have BKnight := stB.mpr (by right ; right ; assumption)
    contradiction

  sorry
example 
{K : Type} {S : Set K}
{A : K}
{S' : Set K}
  (h : S ⊆ ({A}: Set K) ∪ S') (h' : A ∉ S) : S ⊆ S' := by exact (Set.subset_insert_iff_of_not_mem h').mp h

example 

{K : Type} {S : Set K}
{A : K}
{AinS : A ∈ S} : {A} ⊆ S := by exact Set.singleton_subset_iff.mpr AinS


example
  {A B C : Inhabitant}
  {inst : DecidableEq Inhabitant}
  {inst2 : Fintype Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
  {all : ∀(x : Inhabitant), x = A ∨ x = B ∨ x = C}
  { AneB : A ≠ B}
  { BneC : B ≠ C}
  { AneC : A ≠ C}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{h2: B ∈ Knight ∨ B ∈ Knave }
{h3: C ∈ Knight ∨ C ∈ Knave }
{stA : A ∈ Knight  ↔ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave) }
{stB: B ∈ Knight ↔ (Knight = {A} ∨ Knight = {B} ∨ Knight = {C}) }
{stBn: B ∈ Knave ↔ ¬ (Knight = {A} ∨ Knight = {B} ∨ Knight = {C}) }
  : Solution A B C Knight Knave:= by
--  A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave
  {
    
    -- this is similar to i am a knave
    have AKnave : A ∈ Knave := by {
      --#check iff_iff_implies_and_implies
      have := (iff_iff_implies_and_implies).mp stA
      by_contra AKnight
      rw [notinright_inleftIff h1 h] at AKnight
      have AKnave := stA.mp AKnight
      exact IamKnave h h1 (by simp[AKnight,AKnave.left] )
      --exact disjoint h AKnight AKnave.left 
    }

    have BKnight : ¬B ∈ Knave := by 
      intro BKnave
      have notallknave := stAn.mp AKnave
      simp [BKnave,AKnave] at notallknave
      #check set_subset_univ
      have : Knight ⊆ {A,B,C} := by 
        apply set_subset_univ
        repeat assumption
      #check Finset.subset_insert_iff_of_not_mem notallknave
      rw [inright_notinleftIff h1 h] at AKnave
      rw [inright_notinleftIff h2 h] at BKnave
      rw [Finset.subset_insert_iff_of_not_mem AKnave] at this
      rw [Finset.subset_insert_iff_of_not_mem BKnave] at this
      rw [notinright_inleftIff h3 h] at notallknave
      have sub : {C} ⊆ Knight := by 
        intro x
        intro hC 
        rw [Finset.mem_singleton] at hC
        rw [hC]
        assumption
      have knightC := Finset.Subset.antisymm this sub 
      rw [notinleft_inrightIff h2 h] at BKnave  
      have cont := stBn.mp BKnave 
      push_neg at cont
      exact cont.right.right knightC
     
    have BKnight : B ∈ Knight := by {
      by_contra BKnave
      rw [notinleft_inrightIff h2 h] at BKnave

      --push_neg at stBn 
      --rw [not_and_or] at stAn
      --rw [not_and_or] at stAn
      -- 
      --simp[AKnave] at stAn 
      --simp[BKnave] at stAn 
       
      --have := stBn.mp BKnave
      -- last one left theorem, its own level?
      have CKnight : C ∈ Knight := by 
        have Knaves := stAn.mp AKnave
        repeat rw [not_and_or] at Knaves
        --push_neg at Knaves
        simp [AKnave,BKnave] at Knaves
        exact notright_left h3 Knaves 

       
      have KnighteqC : Knight = {C} := by
        --#check Set.eq_of_subset_of_subset   
        rw [Finset.eq_singleton_iff_unique_mem] 
        constructor
        · assumption
        -- make a theorem of this and for all the cases
        · intro x
          intro xK
          rcases all x with h_1|h_2
          · rw [h_1] at xK
            exfalso 
            exact disjoint h xK AKnave
          · rcases h_2 with h_11|h_22
            · rw [h_11] at xK
              exfalso
              exact disjoint h xK BKnave
            · assumption
      have BKnight:= stB.mpr (by right; right; assumption)
      exact disjoint h BKnight BKnave  
    }

    have CKnave : C ∈ Knave := by {
      have OneKnight := stB.mp BKnight
      by_contra CKnight 
      have CKnight := notright_left h3 CKnight
      -- now theorem
      rcases OneKnight with h_1|h_2
      · 
        --#check Finset.singleton_subset_iff
        --#check Finset.mem_singleton
        exact full_singleton h_1 BKnight AneB.symm 
        
      · rcases h_2 with h_11|h_22
        · 
          exact full_singleton h_11 CKnight BneC.symm
        · exact full_singleton h_22 BKnight BneC

      --    -- make a full version but for this, i can turn Knight={C} into card one and use full
    }
    -- now submit
    sorry

  }
