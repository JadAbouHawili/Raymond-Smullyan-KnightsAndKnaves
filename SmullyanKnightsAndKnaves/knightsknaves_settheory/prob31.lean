import SmullyanKnightsAndKnaves.knightsknaves_3
#check Finset.card_bij
#check Equiv.setCongr

  #check congrFun
  #check iff_of_eq
#check Finset.ext_iff
#check Set.ext_iff
#check Finset.subtype_eq_univ
  #check Finset.subtype

set_option push_neg.use_distrib true
-- theorem using full3 is ideal
open Inhabitant
-- A : all of us are knaves
-- B : exactly one of us is a knight
example
{stA : A ∈ Knight ↔ allKnave}
{stAn : A ∈ Knave ↔ ¬allKnave}
{stB : B ∈ Knight ↔ oneKnight}
{stBn : B ∈ Knave ↔ ¬oneKnight}
: A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave := by
  have AKnave : A ∈ Knave
  knight_interp
  intro AKnight
  have allKnaves := stA.mp AKnight
  unfold allKnave at allKnaves
  have AKnave := allKnaves.left
  contradiction
  constructor
  assumption

  have notallknave := stAn.mp AKnave
  have BKnight : B ∈ Knight
  knave_interp
  intro BKnave
  have notoneKnight := stBn.mp BKnave
  unfold allKnave at notallknave
  simp [AKnave,BKnave] at notallknave
  knight_interp at notallknave
  have OneKnight : oneKnight
  unfold oneKnight
  simp [AKnave,BKnave,notallknave]
  contradiction

  constructor
  assumption
  have OneKnight := stB.mp BKnight
  unfold oneKnight at OneKnight
  simp [AKnave,BKnight] at OneKnight
  knight_interp at AKnave
  knave_interp at BKnight
  simp [AKnave,BKnight] at OneKnight
  assumption


-- turn a statement of S = {A,B,C} into A ∈ S ∧ ...

#check Finset.eq_univ_iff_forall



theorem simp_eq {S : Finset Inhabitant} : S = ({A,B,C} : Finset Inhabitant) ↔ A ∈ S ∧ B ∈ S ∧ C ∈ S := by
  constructor
  · intro h ; rw [h] ;simp
  · intro h
    apply Finset.Subset.antisymm
    · by_universe
    · intro x h'
      simp at h'
      have ⟨h1,h2,h3⟩ := h
      all_cases_satisfy_goal h'

#check Finset.nonempty_iff_eq_singleton_default
  #check Finset.ne_empty_of_mem
  #check Finset.nonempty_iff_ne_empty
  #check Finset.nonempty_iff_eq_singleton_default

example
{stA : A ∈ Knight ↔ Knave = {A,B,C}}
{stB : B ∈ Knight ↔ Knight = {A} ∨ Knight = {B} ∨ Knight = {C} }
{all2:  Knight ∪ Knave = {A,B,C}}
: A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave := by
  have AKnave : A ∈ Knave
  knight_interp
  intro AKnight
  have allKnave := stA.mp AKnight
  simp at allKnave
  sorry

  knave_interp at stA
  have notallKnave := stA.mp AKnave
  have KnightNonempty: (Knight : Finset Inhabitant).Nonempty := by
    by_contra h
    simp at h
    rw [h] at all2
    simp at all2
    contradiction
  have : ∃a, a ∈ (Knight : Finset Inhabitant) := by exact Finset.nonempty_def.mp KnightNonempty
  have ⟨a,ha⟩ := this
  clear this
  have BKnight : B ∈ Knight
  knave_interp
  intro BKnave
  knave_interp at stB
  have knight_not_eq_singleton := stB.mp BKnave
  have : C ∈ Knight := by
    rcases all a with h|h|h
    · rw [h] at ha
      contradiction
    · rw [h] at ha ; contradiction 
    · rw [h] at ha ; assumption

  -- the following or remove_top
  have KnighteqC : Knight = {C}
  rw [Finset.eq_singleton_iff_unique_mem]
  constructor
  assumption
  intro x h'

  rcases all x with h|h|h
  rw [h] at h' ; contradiction
  rw [h] at h' ; contradiction
  assumption

  simp [KnighteqC] at knight_not_eq_singleton

  have oneKnight := stB.mp BKnight
  rcases oneKnight with h|h|h
  grind
  have : C ∈ Knave
  knight_interp
  intro h'
  rw [h] at h'
  contradiction
  grind 
  rw [h] at BKnight
  contradiction

#check Finset.univ_subset_iff.mp

theorem full3 {S : Finset Inhabitant} (hA : A ∈ S) (hB : B ∈ S) (hC : C ∈ S) : S = {A,B,C} := by
    #check Finset.eq_univ_iff_forall
    #check Finset.univ_subset_iff
    have : Finset.univ = {A,B,C} := rfl
    rw [←this]
    rw [Finset.eq_univ_iff_forall]
    intro x
    all_cases_satisfy_goal all x

/-

ideal

-/
example
{stA : A ∈ Knight ↔ Knave = {A,B,C}}
{stB : B ∈ Knight ↔ (Knight : Finset Inhabitant).card = 1  }
: A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave := by
   
  have AKnave : A ∈ Knave -- proof for this like a primitive (repeated pattern)
  knight_interp
  intro AKnight
  have allknave := stA.mp AKnight
  have AKnave : A ∈ Knave
  rw [allknave]
  simp
  contradiction

  knave_interp at stA
  have := stA.mp AKnave
  have BKnight : B ∈ Knight
  knave_interp
  intro BKnave
  have oneKnight : (Knight: Finset Inhabitant).card = 1
  --knave_interp at stB
  --have notoneKnight := stB.mp BKnave
  --apply notoneKnight
  rw [Finset.card_eq_one]
  use C
  rw [Finset.eq_singleton_iff_unique_mem]
  have CKnight : C ∈ Knight
  knave_interp
  intro CKnave
  have : Knave = {A,B,C} 
  exact full3 AKnave BKnave CKnave
  contradiction
  constructor
  assumption
  intro x h 
  rcases all x with h'|h'|h' 
  rw [h'] at h ; contradiction 
  rw [h'] at h ; contradiction 
  assumption
  have BKnight := stB.mpr oneKnight
  contradiction
  have oneKnight := stB.mp BKnight
  rw [Finset.card_eq_one] at oneKnight
  obtain ⟨a,ha⟩ := oneKnight 
  have CKnave: C ∈ Knave
  knight_interp
  intro knight
  rw [ha] at knight
  simp at knight
  rw [ha] at BKnight
  simp at BKnight
  rw [←knight] at BKnight
  contradiction
  grind

/- proving two sets equal
  -- best way for singletons
  --rw [Finset.eq_singleton_iff_unique_mem]

  
  --rw [Finset.ext_iff]
  apply Finset.Subset.antisymm


#check Set.Subset.antisymm
#check Set.ext_iff.mpr
-/


/-
not ideal 
-/
example
{stA : A ∈ Knight ↔ Knave = {A,B,C}}
{stB : B ∈ Knight ↔ Knight = {A} ∨ Knight = {B} ∨ Knight = {C} }
--}
: A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave := by
  have AKnave : A ∈ Knave -- proof for this like a primitive (repeated pattern)
  knight_interp
  intro AKnight
  have allknave := stA.mp AKnight
  have AKnave : A ∈ Knave
  rw [allknave]
  -- primitive of proving A ∈ {A,B,C}... , introduce Finset.mem_insert
  simp
  contradiction

  knave_interp at stA
  have notallknave := stA.mp AKnave
  have BKnight : B ∈ Knight
  knave_interp
  intro BKnave

  -- can also use this
  -- primitive , proving two sets are equal and there are two ways , either subset.antisymm or unique_mem(all is needed so that would be introduced as a primitive as well)
  have KnighteqC : Knight = {C}
  --rw [Finset.eq_singleton_iff_unique_mem]

  
  --rw [Finset.ext_iff]
  apply Finset.Subset.antisymm
  have : Knight ⊆ {A,B,C} := by 
    by_universe

  knight_interp at AKnave
  -- primitive
  remove_top at this
  knight_interp at BKnave
  remove_top at this
  intro a h
  simp at h
  rw [h]
  knave_interp
  intro CKnave
  have allknave : Knave = {A,B,C}
  rw[Finset.ext_iff]
  simp
  intro x
  constructor
  · intro hh
    exact all x
  sorry

/-
  apply Finset.Subset.antisymm
  by_universe
  intro a' h'
  simp at h'
  all_cases_satisfy_goal h'
  contradiction
  -/

  have BKnight : B ∈ Knight
  rw [stB]
  right ; right ; sorry
  contradiction
  sorry

  have oneKnight := stB.mp BKnight
  rcases oneKnight with singleton|singleton|singleton
  -- use theorem here
  ·
    have AKnight : A ∈ Knight
    rw [singleton] ; simp
    contradiction

  ·
    have CKnave : C ∈ Knave
    knight_interp
    intro CKnight
    rw [singleton] at CKnight
    simp at CKnight
    constructor ; assumption
    constructor ; assumption ; assumption

  ·
    rw [singleton] at BKnight
    simp at BKnight


/-
not ideal
-/
example
{stA : A ∈ Knight ↔ (Knave : Finset Inhabitant).card = 3}
{stB : B ∈ Knight ↔ (Knight : Finset Inhabitant).card = 1}
: A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave := by
  have AKnave : A ∈ Knave
  knight_interp
  intro AKnight
  have allKnave := stA.mp AKnight
  have Knavesubset: Knave ⊆ {A,B,C}
  by_universe
  -- just have this instead of Knave.card=3...
  have KnaveAll: Knave = {A,B,C}
  apply Finset.eq_of_subset_of_card_le Knavesubset
  simp
  rw[ allKnave]

  have AKnave : A ∈ Knave
  rw [KnaveAll] ; simp
  contradiction

  have BKnight : B ∈ Knight
  knave_interp
  intro BKnave
  knave_interp at stB
  have notoneKnave := stB.mp BKnave
  knight_or_knave C with CKnight CKnave
  apply notoneKnave
  rw [Finset.card_eq_one]
  use C

  rw [Finset.eq_singleton_iff_unique_mem]
  constructor ; assumption
  intro x h

  sorry
  sorry
  sorry

#check Finset.eq_singleton_iff_unique_mem


#check subsingleton_iff_forall_eq
#check Set.Subsingleton.eq_empty_or_singleton
#check Set.subsingleton_of_subset_singleton

#check Set.eq_singleton_or_nontrivial


#check Set.mem_powerset_iff


#check Finset.eq_univ_iff_forall

#check Finset.eq_singleton_or_nontrivial
#check Set.eq_singleton_or_nontrivial

#check Finset.eq_singleton_iff_nonempty_unique_mem
#check Finset.eq_singleton_iff_unique_mem


#check Ne.symm
#check ne_of_mem_of_not_mem'

#check Finset.eq_empty_iff_forall_notMem
