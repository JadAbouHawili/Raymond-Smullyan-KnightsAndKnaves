import SmullyanKnightsAndKnaves.dsl_knights_knaves
---- adapt to problems with only 2
--"
--Again we have three people, A, B, C, each of whom is either 
--a knight or a knave. A and B make the following statements: 
--A: All of us are knaves. 
--B: Exactly one of us is a knight. 
--What are A, B, C?
--"
set_option diagnostics true
#check Inter

set_option push_neg.use_distrib true
variable {A B C : Islander}

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


#check Set.mem_setOf
example{K : Type} (S : Set K) : S = {x | x ∈ S} := by exact rfl
  
  --exact (Set.eq_univ_of_univ_subset fun ⦃a⦄ a_1 => all a).symm

-- using Finset.univ instead of all
-- another formalization using cardinalities instead of A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave

