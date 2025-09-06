
import SmullyanKnightsAndKnaves.knightsknaves
import SmullyanKnightsAndKnaves.knightsknaves_3

/-
This can be done in other provers more 'naturally'
https://www.youtube.com/watch?v=oEAa2pQKqQU
https://summerofgodel.blogspot.com/2019/04/table-of-contents-for-series-of-posts.html?

-/
open settheory_approach
example
  {inst : DecidableEq Inhabitant}
(h1 : A ∈ Knight ∨ A ∈ Knave ) 
(h2: B ∈ Knight ∨ B ∈ Knave )
(h3: C ∈ Knight ∨ C ∈ Knave )
(stB : B ∈ Knight ↔ ( A ∈ Knight ↔ A ∈ Knave  ) )
(stC : C ∈ Knight ↔ B ∈ Knave)
 : B ∈ Knave ∧ C ∈ Knight := by{
-- solving it the prolog way
  have AOr := h1
  rcases h1 with h_1|h_2
  · cases h2
    · cases h3
      simp [*] at *
      · tauto
      · set_knight_to_knave at h_1
        tauto
    · cases h3
      · tauto
      · tauto

  · rcases h2 with h_11|h_22
    · rcases h3 with h_2|h_1
      · tauto
      · tauto

    · cases h3 
      · tauto
      · tauto
}

example 
  {x y : Inhabitant}
  (h1 : Xor' (x ∈ Knight) (x ∈ Knave) ) 
  (h2: Xor' (y ∈ Knight)  (y ∈ Knave) )
  -- theres x and y, x says at least one of us is a knave
  --rules of the game, i.e knights tell the truth but knaves lie
  (stx : x ∈ Knight → (x ∈ Knight ∧  y ∈ Knave)
                    ∨ (x ∈ Knave ∧ y ∈ Knight)
                    ∨ (x ∈ Knave ∧ y ∈ Knave)  )
  (stnx : x ∈ Knave → ¬ ( (x ∈ Knight ∧  y ∈ Knave)
                    ∨ (x ∈ Knave ∧ y ∈ Knight)
                    ∨ (x ∈ Knave ∧ y ∈ Knave) ) )
  : x ∈ Knight ∧ y ∈ Knave:= by
  {
 --  show_goals
   rcases h1 with h_1|h_1 

   · rcases h2 with h_2|h_2

     · have statement:= stx h_1.left 
       tauto
     · tauto

   · cases h2 
     · have statement := stnx h_1.left 
       tauto

     · 
       have statement := stnx h_1.left 
       tauto
  }

