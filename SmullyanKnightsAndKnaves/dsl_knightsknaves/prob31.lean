import SmullyanKnightsAndKnaves.knightsknaves
import SmullyanKnightsAndKnaves.dsl_knights_knaves
---- adapt to problems with only 2
--"
--Again we have three people, A, B, C, each of whom is either 
--a knight or a knave. A and B make the following statements: 
--A: All of us are knaves. 
--B: Exactly one of us is a knight. 
--What are A, B, C?
--"
open settheory_approach
set_option diagnostics true
#check Inter

set_option push_neg.use_distrib true
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
  have BKnight : ¬B.isKnave
  intro BKnave
  have notoneknight := knave_said stB BKnave
  unfold oneisknight at notoneknight
  knight_to_knave at AKnave
  #check isKnight_notisKnaveIff
  simp [AKnave, BKnave , isKnave_notisKnightIff.mp BKnave, isKnave_notisKnightIff.mp AKnave] at notoneknight
  knight_to_knave at notoneknight
  unfold allKnaves at notallknave
  simp [AKnave, BKnave, notoneknight] at notallknave

  knave_to_knight at BKnight 
  have one := knight_said stB BKnight
  unfold oneisknight at one
  simp [AKnave,BKnight] at one
  knave_to_knight at one
  simp [AKnave,BKnight] at one
  knight_to_knave at one 
  knight_to_knave at AKnave
  simp [AKnave,BKnight,one]

variable {Inhabitant : Type}
variable {A B C : Inhabitant}
inductive Solution (A B C : Inhabitant) (Knight : Finset Inhabitant) (Knave : Finset Inhabitant)
| submit (h : A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) : Solution A B C (Knight) (Knave)
-- all : ∀ (x : Inhabitant), x = A ∨ x = B ∨ x = C

#check Set.mem_setOf
example{K : Type} (S : Set K) : S = {x | x ∈ S} := by exact rfl
  
  --exact (Set.eq_univ_of_univ_subset fun ⦃a⦄ a_1 => all a).symm

-- using Finset.univ instead of all
-- another formalization using cardinalities instead of A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave

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
    exact (everyone_in_set_eq all).mp ⟨hA,hB,hC⟩ 

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
