
import SmullyanKnightsAndKnaves.knightsknaves

/-
This can be done in other provers more 'naturally'
https://www.youtube.com/watch?v=oEAa2pQKqQU
https://summerofgodel.blogspot.com/2019/04/table-of-contents-for-series-of-posts.html?

-/
example
  {Inhabitant : Type}
  {A B C : Inhabitant}
  {inst : DecidableEq Inhabitant}
  (Knight : Finset Inhabitant ) (Knave : Finset Inhabitant)
(h : Knight ∩ Knave = ∅ )
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
      · have := inleft_notinright h h_1 
        tauto
    · cases h3 
      · tauto
      · tauto

  · rcases h2 with h_11|h_22
    · rcases h3 with h_2|h_1
      · tauto
      · have := inright_notinleft h h_1 
        have := stB.mp h_11
        exfalso
        exact IamKnave h AOr this
        --tauto

    · cases h3 
      · tauto
      · tauto
}

example 
  {Inhabitant : Type}
  {x y : Inhabitant}
  (Knight : Set Inhabitant ) (Knave : Set Inhabitant) 
  --(uni : Knight ∪ Knave) 
  (h : Knight ∩ Knave = ∅ )
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

