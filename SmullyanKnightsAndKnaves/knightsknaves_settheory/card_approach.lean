import SmullyanKnightsAndKnaves.knightsknaves
import SmullyanKnightsAndKnaves.knightsknaves_3

/-
cardinality approach:(does not work...)
(would tell the user to use a theorem that would rewrite Knave.card=3 to Knave = {A,B,C} which reduces to that style of representing the problem)
- When proving that A is a kanve:
  - Assume A is a knight
  - Conclude A's statement that knave.card=3
  - now we want to prove that A is a knave
    (but how?, would need to go through 3*3*3 = 27 cases)
-/
variable [Fintype Inhabitant]
example
{inst3 : Fintype Inhabitant}
{stA : A ∈ Knight  ↔ (Knave= {A,B,C}) }
{stAn : A ∈ Knave ↔ ¬ (Knave = {A,B,C}) }
{three : A ∈ Knight ↔ Knave.card=3 }
{stB : B ∈ Knight ↔ Knave.card=1 }
{stBn : B ∈ Knave ↔ Knave.card ≠ 1}
{AneC : A ≠ C}
(all : ∀ (x : Inhabitant), x = A ∨ x = B ∨ x = C)
  : A ∈ Knave ∧ C ∈ Knight := by

  have : (Knave.card = 3) ↔ (Knave = ({A,B,C} : Finset Inhabitant) ) := by
    constructor
    intro card3
    rw [Finset.card_eq_three] at card3
    by_contra neq
    have ⟨x,y,z,xney,xnez,ynez,eq⟩ := card3 
    rw [eq] at neq
    
    sorry
    intro eq 
    rw [Finset.card_eq_three]
    use A ; use B ; use C
    exact ⟨AneB , AneC , BneC , eq⟩ 
  have AKnave : A ∈ Knave
  set_knave_to_knight
  intro AKnight
  have c := three.mp AKnight
  rw [Finset.card_eq_three] at c
  have ⟨x,y,z,xney,xnez,ynez,knaveEq⟩ := c 
  have : A ∈ Knave
  rw [knaveEq]
  repeat rw [Finset.mem_insert]
  rw [Finset.mem_singleton]
  sorry
  have : Knave ={A,B,C}
 -- have : Knave ⊆ ({A,B,C} : Finset Inhabitant) := by
 --     exact set_subset_univ all
  have : Knave ⊆ (Finset.univ) := by
      exact Finset.subset_univ Knave

  -- do case for every x,y,z. every combination which is 27 to get this..
  rcases all x with xA|xB|xC
  ·
    rcases all y with yA|yB|yC
    · rcases all z with zA|zB|zC
      · rw [xA] at xney
        rw [yA] at xney 
        contradiction
      · rw [xA] at xney
        rw [yA] at xney 
        contradiction
      · rw [xA] at xney
        rw [yA] at xney 
        contradiction
    · rcases all z with zA|zB|zC
      · rw [xA] at xnez
        rw [zA] at xnez 
        contradiction
      · rw [yB] at ynez
        rw [zB] at ynez 
        contradiction
      · rw [xA] at knaveEq
        rw [yB] at knaveEq
        rw [zC] at knaveEq
        assumption
    · rcases all z with zA|zB|zC
      · rw [xA] at xnez
        rw [zA] at xnez 
        contradiction
      · rw [xA] at knaveEq
        rw [yC] at knaveEq
        rw [zB] at knaveEq
        rw [knaveEq]
        sorry
      · rw [zC] at ynez
        rw [yC] at ynez
        contradiction

  ·
    rcases all y with yA|yB|yC
    · rcases all z with zA|zB|zC
      · sorry
      · sorry
      · sorry
    · rcases all z with zA|zB|zC
      · sorry
      · sorry
      · sorry
    · rcases all z with zA|zB|zC
      · sorry
      · sorry
      · sorry
  ·
    rcases all y with yA|yB|yC
    · rcases all z with zA|zB|zC
      · sorry
      · sorry
      · sorry
    · rcases all z with zA|zB|zC
      · sorry
      · sorry
      · sorry
    · rcases all z with zA|zB|zC
      · sorry
      · sorry
      · sorry

  sorry

  have notallKnave := stAn.mp AKnave

  constructor
  assumption
  set_knight_to_knave
  intro CKnave
  set_knight_or_knave B with BKnight BKnave
  · have one := stB.mp BKnight
    rw [Finset.card_eq_one] at one
    have ⟨a,singleton⟩ := one 
    rw [singleton] at AKnave 
    rw [singleton] at CKnave 
    rw [Finset.mem_singleton] at CKnave
    rw [Finset.mem_singleton] at AKnave
    rw [←CKnave] at AKnave
    contradiction
  · 
    have : Knave = {A,B,C}
    apply set_full3 
    repeat assumption
    contradiction


#check Finset.ssubset_iff_subset_ne.mpr

#check full2
#check Finset.card_eq_two
