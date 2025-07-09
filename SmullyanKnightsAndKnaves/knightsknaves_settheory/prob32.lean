import SmullyanKnightsAndKnaves.knightsknaves

set_option push_neg.use_distrib true
set_option trace.Meta.Tactic.simp true
set_option trace.Meta.Tactic.contradiction true
--set_option trace.Meta.synthInstance true

open settheory_approach
#help option
--A:All of us are knaves.
--B: Exactly one of us is a knave.
variable [DecidableEq Inhabitant]
example
{stA : A ∈ Knight ↔ (allKnave) }
{stAn : A ∈ Knave ↔ ¬ (allKnave) }
{stB: B ∈ Knight ↔ oneKnave }
{stBn: B ∈ Knave ↔ ¬ (oneKnave) }
  : A ∈ Knave ∧ C ∈ Knight := by
  {
--A: All of us are knaves.
--B: Exactly one of us is a knave.
  have AKnave : A ∈ Knave := by
    by_contra AKnight
    set_knave_to_knight at AKnight
    have knaves := stA.mp AKnight
    have AKnave := knaves.left
    contradiction

  have notallknaves := stAn.mp AKnave
  constructor
  assumption
  set_knight_or_knave B with BKnight BKnave
  ·
    have oneKn := stB.mp BKnight 
    unfold oneKnave at oneKn
    simp [AKnave,BKnight,inleft_notinrightIff] at oneKn
    set_knight_to_knave 
    assumption
  ·
    unfold allKnave at notallknaves
    simp [AKnave,BKnave] at notallknaves
    set_knight_to_knave
    assumption
  }

#check not_eq_singleton_of_not_mem

theorem not_eq_singleton_already_full 
{K : Type}
{A B: K}
{Knave : Finset K}
(AneB : A ≠ B)
(AKnave : A ∈ Knave)

: Knave ≠ {B} := by
        intro knaveB 
        rw [knaveB] at AKnave
        #check Finset.mem_singleton
        rw [Finset.mem_singleton] at AKnave
        contradiction

#check card_eq_one_iff_singletons
#check card_eq

example
{stA : A ∈ Knight  ↔ (Knave= {A,B,C}) }
{stAn : A ∈ Knave ↔ ¬ (Knave = {A,B,C}) }
{stB : B ∈ Knight ↔ Knave = {A} ∨ Knave = {B} ∨ Knave = {C}}
{stBn : B ∈ Knave ↔ ¬ (Knave = {A} ∨ Knave = {B} ∨ Knave = {C})}
(all : ∀ (x : Inhabitant), x = A ∨ x = B ∨ x = C)
  : A ∈ Knave ∧ C ∈ Knight := by
  have AKnave : A ∈ Knave
  set_knave_to_knight
  intro AKnight
  have allKnave := stA.mp AKnight
  have AKnave : A ∈ Knave 
  rw [allKnave]
  is_mem
  contradiction

  have notallKnave := stAn.mp AKnave

  constructor
  assumption
  set_knight_or_knave B with BKnight BKnave
  · have oneKnave := stB.mp BKnight
    set_knight_to_knave
    intro CKnave
    rcases oneKnave with single|single|single
    · 
      rw [single] at CKnave
      rw [Finset.mem_singleton] at CKnave
      symm at CKnave
      sorry
    · sorry
    · sorry


  · have notsingleknave := stBn.mp BKnave
    simp at notsingleknave 
    set_knight_to_knave
    intro CKnave
    #check Finset.Subset.antisymm
    --show_term contradiction
    #check full2
    have : Knave = {A,B,C} := by
      apply knave_full3
      repeat assumption
    contradiction

variable [Fintype Inhabitant]
example
{stA : A ∈ Knight  ↔ (Knave= {A,B,C}) }
{stAn : A ∈ Knave ↔ ¬ (Knave = {A,B,C}) }
{three : A ∈ Knight ↔ Knave.card=3}
{stB : B ∈ Knight ↔ Knave.card=1}
{stBn : B ∈ Knave ↔ Knave.card ≠ 1}
{AneC : A ≠ C}
(all : ∀ (x : Inhabitant), x = A ∨ x = B ∨ x = C)
  : A ∈ Knave ∧ C ∈ Knight := by

  have AKnave : A ∈ Knave
  set_knave_to_knight
  intro AKnight
  have c := three.mp AKnight
  rw [Finset.card_eq_three] at c
  have ⟨x,y,z,xney,xnez,ynez,knaveEq⟩ := c 
  have : Knave ={A,B,C}
  have : Knave ⊆ {A,B,C} := by
      exact set_subset_univ all
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
    apply knave_full3 
    repeat assumption
    contradiction


#check Finset.ssubset_iff_subset_ne.mpr

#check full2
#check Finset.card_eq_two
