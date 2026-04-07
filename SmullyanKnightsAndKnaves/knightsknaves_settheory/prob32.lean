import SmullyanKnightsAndKnaves.knightsknaves_3

set_option push_neg.use_distrib true

open Inhabitant

--A:All of us are knaves.
--B: Exactly one of us is a knave.
example
{stA : A ∈ Knight ↔ (allKnave) }
{stAn : A ∈ Knave ↔ ¬ (allKnave) }
{stB: B ∈ Knight ↔ oneKnave }
{stBn: B ∈ Knave ↔ ¬ (oneKnave) }
  : A ∈ Knave ∧ C ∈ Knight := by
  {
  have AKnave : A ∈ Knave := by
    by_contra AKnight
    knight_interp at AKnight
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
    simp [AKnave,BKnight,knight_notknaveIff] at oneKn
    set_knight_to_knave
    assumption
  ·
    unfold allKnave at notallknaves
    simp [AKnave,BKnave] at notallknaves
    set_knight_to_knave
    assumption
  }

-- if A subset B then card A <= card B
example (A B : Finset Inhabitant) (h : A ⊆ B) : A.card ≤ B.card := by
  exact Finset.card_le_card h


--A:All of us are knaves.
--B: Exactly one of us is a knave.


open Lean Elab Tactic
example {α : Type} {x a b c : α} {p : α → Prop}
(ha : p a) (hb : p b) (hc : p c)
(h : x = a ∨ x = b ∨ x = c) : p x := by 
  all_cases_satisfy_goal3 h

example
{stA : A ∈ Knight ↔ (Knave : Finset Inhabitant).card =3}
{stAn : A ∈ Knave ↔ (Knave : Finset Inhabitant).card ≠ 3}
{stB : B ∈ Knight ↔ (Knave : Finset Inhabitant).card = 1}
{stBn : B ∈ Knave ↔ (Knave : Finset Inhabitant).card ≠ 1}
: A ∈ Knave ∧ C ∈ Knight := by
  -- create a custom tactic that would transform stA into stAn and vice versa
  have AKnave : A ∈ Knave
  knight_interp
  intro AKnight
  have allKnave := stA.mp AKnight
  have Knavesubset: Knave ⊆ {A,B,C}
  intro x h ; simp ; exact all x
  --by_universe
  have KnaveAll: Knave = {A,B,C}
  apply eq_of_subset_card_eq Knavesubset
  -- doing simp would just work
  simp only [allKnave]
  symm
  rw [Finset.card_eq_three]
  use A
  use B
  use C
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, and_self]

  have AKnave : A ∈ Knave
  rw [KnaveAll] ; simp
  contradiction

  constructor
  assumption

  set_knight_to_knave
  intro CKnave
  set_knight_or_knave B with BKnight BKnave
  have oneKnave := stB.mp BKnight
  rw [Finset.card_eq_one] at oneKnave
  have ⟨a,ha⟩ := oneKnave
  rw [ha] at AKnave
  rw [ha] at CKnave
  simp at AKnave
  simp at CKnave
  rw [←CKnave] at AKnave
  contradiction
  /-
  have knaveSub : {A,C} ⊆ Knave
  intro x h
  simp at h
  rcases h with h|h
  rw [h] ; assumption
  rw [h] ; assumption

  have : 2 ≤ Knave.card
  #check Finset.card_le_card
  have := Finset.card_le_card knaveSub
  have : ({A,C} : Finset Inhabitant).card = 2
  rw [Finset.card_eq_two]
  use A
  use C
  constructor
  exact AneC
  trivial
  rw [←this] ; assumption

  rw[oneKnave] at this ; contradiction
  -/

  have : (Knave : Finset Inhabitant).card=3
  rw [Finset.card_eq_three]
  use A,B,C
  simp
  #check eq_of_subset_card_eq
  apply Finset.Subset.antisymm
  by_universe
  intro x h
  simp at h
  all_cases_satisfy_goal3 h

  have := stAn.mp AKnave
  contradiction

#check Finset.mem_insert
  #check Finset.mem_singleton
  #check Finset.mem_univ
example
{stA : A ∈ Knight  ↔ (Knave= ({A,B,C} : Finset Inhabitant)) }
{stAn : A ∈ Knave ↔ ¬ (Knave = {A,B,C}) }
{stB : B ∈ Knight ↔ Knave = {A} ∨ Knave = {B} ∨ Knave = {C}}
{stBn : B ∈ Knave ↔ ¬ (Knave = {A} ∨ Knave = {B} ∨ Knave = {C})}
  : A ∈ Knave ∧ C ∈ Knight := by
  have AKnave : A ∈ Knave
  knight_interp
  intro AKnight
  have allKnave := stA.mp AKnight
  have AKnave : A ∈ Knave
  rw [allKnave]
  simp
  contradiction

  have notallKnave := stAn.mp AKnave

  constructor
  assumption

  set_knight_or_knave B with BKnight BKnave
  · have oneKnave := stB.mp BKnight
    set_knight_to_knave
    intro CKnave
    #check Finset.eq_iff_card_ge_of_superset
    #check Finset.eq_of_subset_of_card_le
    rcases oneKnave with s|s|s
    rw [s] at CKnave
    simp at CKnave
    contradiction

    rw [s] at CKnave
    simp at CKnave
    contradiction

    rw [s] at AKnave
    simp at AKnave
    contradiction

  ·
    set_knight_to_knave
    intro CKnave
    apply notallKnave
    apply Finset.Subset.antisymm
    · by_universe

    ·
      intro a
      intro h
      simp at h
      -- take cases and done
      rcases h with h|h|h <;> (rw [h] ; assumption) --simp only [h, AKnave, BKnave, CKnave]
