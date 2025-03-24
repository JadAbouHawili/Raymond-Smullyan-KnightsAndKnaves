import SmullyanKnightsAndKnaves.knightsknaves
import SmullyanKnightsAndKnaves.dsl_knights_knaves
---- adapt to problems with only 2
--Introduction 
--"
--Again we have three people, A, B, C, each of whom is either 
--a knight or a knave. A and B make the following statements: 
--A: All of us are knaves. 
--B: Exactly one of us is a knight. 
--What are A, B, C?
--"
-- setup to import into every file, instead of having to do , example {..} {..} {..} ...
open Inhabitant
example {Inhabitant : Type} {A : Inhabitant} {hA : A ∈ Knight2}: 2=2 := by
  rfl

variable {A B C : Islander}
def allKnaves := A.isKnave ∧ B.isKnave ∧ C.isKnave
def oneisknight := (A.isKnight ∧ B.isKnave ∧ C.isKnave)  ∨(A.isKnave ∧  B.isKnight ∧ C.isKnave) ∨ (A.isKnave ∧ B.isKnave ∧  C.isKnight)
open Islander
example 
{stA : A said @allKnaves A B C}
{stB : B said @oneisknight A B C}
: A.isKnave ∧ B.isKnight ∧ C.isKnave := by 
  have AKnave : ¬A.isKnight  
  intro AKnight
  have allknave := knight_said stA AKnight
  unfold allKnaves at allknave
  have AKnave := allknave.left 
  contradiction

  have notallknave := notknight_said stA AKnave 
  sorry

variable {Inhabitant : Type}
variable {A B C : Inhabitant}
inductive Solution (A B C : Inhabitant) (Knight : Finset Inhabitant) (Knave : Finset Inhabitant)
| submit (h : A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) : Solution A B C (Knight) (Knave)
-- i could obfuscate this by making a type that when given the correct argument solves the exercise.
-- all : ∀ (x : Inhabitant), x = A ∨ x = B ∨ x = C
-- {stA : A ∈ Knight  ↔ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave) }

#check Set.mem_setOf
example{K : Type} (S : Set K) : S = {x | x ∈ S} := by exact rfl
  
  ----
  --exact (Set.eq_univ_of_univ_subset fun ⦃a⦄ a_1 => all a).symm

-- using Finset.univ instead of all
-- another formalization using cardinalities instead of A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave
#check Knight2
#check inst22
example

  {A1 : Type}
  {inst3 : DecidableEq Type}
  {Inhabitant : Type}
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
  have : A1 ∈ Knight2 := sorry
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
    set_knight_to_knave2 at this
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

theorem all_in_one
  {inst : DecidableEq Inhabitant}
  {A B C : Inhabitant}
  {S : Finset Inhabitant} 
  {all : ∀(x : Inhabitant), x = A ∨ x = B ∨ x = C}
  (hA : A ∈ S)
  (hB : B ∈ S)
  (hC : C ∈ S)
  : S = {A,B,C}
  := by 
    #check Finset.eq_of_subset_of_card_le 
    #check everyone_in_set_eq
    apply?
    exact?
    sorry
  
example
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
  {all : ∀(x : Inhabitant), x = A ∨ x = B ∨ x = C}
  { AneB : A ≠ B}
  { BneC : B ≠ C}
  { AneC : A ≠ C}
{h : Knight ∩ Knave = ∅ }
  {Or : ∀(x:Inhabitant), x ∈ Knave ∨ x ∈ Knight}
{h1 : A ∈ Knight ∨ A ∈ Knave }
{h2: B ∈ Knight ∨ B ∈ Knave }
{h3: C ∈ Knight ∨ C ∈ Knave }
{stA : A ∈ Knight  ↔ (Knave={A,B,C}) }
{stAn : A ∈ Knave ↔ ¬ (Knave={A,B,C}) }
{stB: B ∈ Knight ↔ (Knight = {A} ∨ Knight = {B} ∨ Knight = {C}) }
{stBn: B ∈ Knave ↔ ¬ (Knight = {A} ∨ Knight = {B} ∨ Knight = {C}) }
  : Solution A B C Knight Knave:= by
    -- A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave
--  rw [everyone_knave_set_eq all] at stA
  --rw [everyone_knave_set_eq all] at stAn
  -- also similar to I am a Knave
  have AKnave : A ∈ Knave := by
    by_contra AKnight
    rw [notinright_inleftIff h1 h] at AKnight
    have everyoneknave := stA.mp AKnight  
    have AKnave: A ∈ Knave := by rw [everyoneknave] ; apply Finset.mem_insert_self
    contradiction
  have notallknave := stAn.mp AKnave
  have AnKnight: Knight ≠ {A} := by 
    intro KnighteqA 
    have := mem_of_eq_singleton KnighteqA 
    contradiction
  simp [AnKnight] at stB
  have BKnight2 : B ∈ Knight := by 
    by_contra BKnave 
    rw [notinleft_inrightIff h2 h] at BKnave 
    have CnKnave : C ∉ Knave := by 
      intro CKnave 
      have : Knave = {A,B,C} := by 
        #check everyone_in_set_eq
        exact (everyone_in_set_eq all).mp ⟨AKnave,BKnave ,CKnave⟩
      contradiction 
    -- so Knight = {C} so B knight, contradiction 
    sorry
  have BKnight : B ∈ Knight := by 
    by_contra BKnave
    rw [notinleft_inrightIff h2 h] at BKnave
    have notoneknight := stBn.mp BKnave
    push_neg at notoneknight
    -- by stAn, C is a knight because otherwise Knave={A,B,C}. then knight={C} contradiction
    -- since ¬Knave={A,B,C} then Knight is not empty. If C knave, then knight empty or then Knave={A,B,C} contradition. So C not knave, i.e C Knight but if C Knight then Knight ={C} contradiction
    #check Finset.univ
    #check all2_in_one_other_empty
    #check all3_in_one_other_empty
    #check all3_in_one_other_eq_all
    #check two_in_one_other_nonemp 
    --rw [or_comm] at Or
    have S'nonemp := two_in_one_other_nonemp all Or AKnave BKnave notallknave
    #check set_subset_univ
    have : Knight ={C} := by 
      rw [Finset.eq_singleton_iff_nonempty_unique_mem] 
      constructor
      · exact Finset.nonempty_iff_ne_empty.mpr S'nonemp
      · intro x
        intro xKnight
        have xs := all x
        -- repeated pattern of reasoning
        rcases xs with h_1|h_2
        · rw [h_1] at xKnight
          exfalso
          exact disjoint h xKnight AKnave
        · rcases h_2 with h_3|h_4
          · rw [h_3] at xKnight
            exfalso
            exact disjoint h xKnight BKnave
          · assumption
    have := notoneknight.right.right 
    contradiction
    --exact notoneknight.right.right this
  -- solution is A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave
  have Knightsingle := stB.mp BKnight
  #check mem_of_eq_singleton
  -- repeated pattern of reasoning
  -- A ∉ Knight so Knight ≠ {A}
  #check not_eq_singleton_of_not_mem
  rw [inright_notinleftIff (h1) h] at AKnave
  have KneA := not_eq_singleton_of_not_mem AKnave 
  simp [KneA] at Knightsingle
   
  #check already_full
  have := already_full BKnight Knightsingle BneC
  have : C ∉ Knight := by 
    intro CKnight 
    rw [this] at CKnight 
    rw [Finset.mem_singleton] at CKnight
    exact BneC CKnight.symm

  -- now submit
  sorry


example 
{K : Type}
{A B C : K} { inst2 : Fintype K} {inst : DecidableEq K} 
{S S' : Finset K} 
(all : ∀(x:K),x=A ∨ x=B ∨ x=C)
(Or : ∀(x:K), x ∈ S ∨ x ∈ S')
(SneAll : S ≠ {A,B,C}) : S' ≠ ∅ := by 
  intro S'emp 
  #check Finset.empty
  #check Finset.eq_empty_iff_forall_not_mem
  rw [Finset.eq_empty_iff_forall_not_mem] at S'emp
  have AinS:= notright_left (Or A) (S'emp A)   
  have BinS:= notright_left (Or B) (S'emp B)   
  have CinS:= notright_left (Or C) (S'emp C)   

  have : ∀(x:K), x ∈ S := by 
    intro x
    have nS' := S'emp x 
    exact  notright_left (Or x) nS'
  have SeqAll : S = {A,B,C} := by 
    apply Finset.ext
    intro a
    constructor
    · intro ainS
      #check {A,B,C}
      --#check Finset.instSingletonFinset
      #check (mem_iff_or_finset).mpr
       
     -- exact (mem_iff_or A B C a).mpr (all a)
      apply (mem_iff_or_finset).mpr
      exact all a

      --cases all a
      ---- make thm first_mem, second_mem third_mem, this is a repeated pattern of reasoning
      --· rw [h]
      --  apply Finset.mem_insert_self
      --· sorry
    · exact fun _ => this a
  contradiction
