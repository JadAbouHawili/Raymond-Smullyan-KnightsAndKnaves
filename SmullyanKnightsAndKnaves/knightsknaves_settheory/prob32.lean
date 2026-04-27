import SmullyanKnightsAndKnaves.knightsknaves_3

set_option push_neg.use_distrib true

open Inhabitant

/-

-/
--A:All of us are knaves.
--B: Exactly one of us is a knave.
example
{stA : A ∈ Knight ↔ (allKnave) }
{stAn : A ∈ Knave ↔ ¬ (allKnave) }
{stB: B ∈ Knight ↔ oneKnave }
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
  knight_or_knave B with BKnight BKnave
  ·
    have oneKn := stB.mp BKnight
    unfold oneKnave at oneKn
    simp [AKnave,BKnight,knight_notknaveIff] at oneKn
    knave_interp
    assumption
  ·
    unfold allKnave at notallknaves
    simp [AKnave,BKnave] at notallknaves
    knave_interp
    assumption
  }


  #check Finset.card_eq_iff_eq_univ
  #check Finset.eq_of_subset_of_card_le 
  #check Finset.eq_univ_of_card 
  #check Finset.card_eq_iff_eq_univ
example
{stA : A ∈ Knight  ↔ (Knave= {A,B,C}) }
{stAn : A ∈ Knave ↔ ¬ (Knave = {A,B,C}) }
{three : A ∈ Knight ↔ (Knave : Finset Inhabitant).card=3 }
{stB : B ∈ Knight ↔ (Knave : Finset Inhabitant).card=1 }
  : A ∈ Knave ∧ C ∈ Knight := by
  have AKnave: A ∈ Knave
  sorry
  constructor
  assumption
  knave_interp
  intro CKnave
  knight_or_knave B with BKnight BKnave
  · have one := stB.mp BKnight
    rw [Finset.card_eq_one] at one
    have ⟨a,singleton⟩ := one 
    rw [singleton] at AKnave 
    rw [singleton] at CKnave 
    simp at CKnave
    simp at AKnave
    rw [←CKnave] at AKnave
    contradiction
  ·
    have : Knave = {A,B,C}
    apply Finset.Subset.antisymm
    by_universe
    intro x h
    simp at h
    all_cases_satisfy_goal h

    have := stA.mpr this
    contradiction










--A:All of us are knaves.
--B: Exactly one of us is a knave.
open Lean Elab Tactic
example {α : Type} {x a b c : α} {p : α → Prop}
(ha : p a) (hb : p b) (hc : p c)
(h : x = a ∨ x = b ∨ x = c) : p x := by 
  all_cases_satisfy_goal h

#check Finset.card_eq_iff_eq_univ 
#check Finset.card_univ
#check Finset.univ_subset_iff

example
{stA : A ∈ Knight ↔ (Knave : Finset Inhabitant) = {A,B,C}}
{stB : B ∈ Knight ↔ (Knave : Finset Inhabitant).card = 1}
: A ∈ Knave ∧ C ∈ Knight := by
  have AKnave: A ∈ Knave 
  knight_interp 
  intro AKnight
  have allKnave := stA.mp AKnight
  have : A ∈ Knave
  rw [allKnave]
  simp ; contradiction

  knave_interp at stA
  have notallKnave := stA.mp AKnave
  knight_or_knave B with BKnight BKnave
  have oneKnave := stB.mp BKnight
  rw [Finset.card_eq_one] at oneKnave
  obtain ⟨a,ha⟩ :=oneKnave 
  have CKnight : C ∈ Knight
  knave_interp
  intro CKnave

  grind
  grind
  sorry


example
{stA : A ∈ Knight ↔ (Knave : Finset Inhabitant).card =3}
{stAn : A ∈ Knave ↔ (Knave : Finset Inhabitant).card ≠ 3}
{stB : B ∈ Knight ↔ (Knave : Finset Inhabitant).card = 1}
: A ∈ Knave ∧ C ∈ Knight := by
  have AKnave : A ∈ Knave
  knight_interp
  intro AKnight
  have allKnave := stA.mp AKnight
  --grind -- have a super powerful grind that can do this...  think about making tactics more powerful in lean 4 games
  -- abstracted into a theorem...
  have : 3 = (Finset.univ : Finset Inhabitant).card := by exact Nat.eq_of_beq_eq_true rfl
  rw [this] at allKnave
  have : Knave = (Finset.univ: Finset Inhabitant) := by 
    exact (Finset.card_eq_iff_eq_univ Knave).mp allKnave
  -- consequence of the inductive type
  #check exists₅_congr
  have this2 : Finset.univ = {A,B,C} := by exact Finset.val_inj.mp rfl 
  rw [this2] at this


  have Knavesubset: Knave ⊆ {A,B,C}
  by_universe
  have KnaveAll: Knave = {A,B,C}
  apply Finset.eq_of_subset_of_card_le Knavesubset
  exact Nat.le_of_eq ((Eq.symm allKnave))


  have AKnave : A ∈ Knave
  rw [KnaveAll] ; simp
  contradiction

  constructor
  assumption

  knave_interp
  intro CKnave
  knight_or_knave B with BKnight BKnave
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
  apply Finset.Subset.antisymm
  by_universe
  intro x h
  simp at h
  all_cases_satisfy_goal h

  have := stAn.mp AKnave
  contradiction

#check Finset.mem_insert
  #check Finset.mem_singleton
  #check Finset.mem_univ
example
{stA : A ∈ Knight  ↔ (Knave= ({A,B,C} : Finset Inhabitant)) }
{stAn : A ∈ Knave ↔ ¬ (Knave = {A,B,C}) }
{stB : B ∈ Knight ↔ Knave = {A} ∨ Knave = {B} ∨ Knave = {C}}
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

  knight_or_knave B with BKnight BKnave
  · have oneKnave := stB.mp BKnight
    knave_interp
    intro CKnave
    #check Finset.eq_iff_card_ge_of_superset
    #check Finset.eq_of_subset_of_card_le
    rcases oneKnave with s|s|s
    rw [s] at CKnave
    simp at CKnave

    rw [s] at CKnave
    simp at CKnave

    rw [s] at AKnave
    simp at AKnave

  ·
    knave_interp
    intro CKnave
    apply notallKnave
    apply Finset.Subset.antisymm
    · by_universe

    ·
      intro a h
      simp at h
      all_cases_satisfy_goal h
