import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Basic

import SmullyanKnightsAndKnaves.logic

variable {K : Type}
variable {A B : K}

theorem disjoint_general
{K : Type}
{inst : DecidableEq K}  {left : Finset K} {right : Finset K}
{A : K}
(h : left ∩ right = ∅ )
(hk : A ∈ left)
(hkn : A ∈ right)  : False := by 
  --have := Finset.mem_inter.mpr (And.intro hk hkn )
  have := Finset.mem_inter_of_mem hk hkn 
  rw [h] at this
  contradiction

theorem card_eq {Normal : (Finset K)} (h : Normal.card =1) (ANormal : A ∈ Normal) ( BNormal : B ∈ Normal) : A=B := by 
  have := Nat.le_of_eq h
  rw [Finset.card_le_one_iff] at this
  exact this ANormal BNormal

theorem full
{S : Finset K} 
{B : K}
(AinS: A ∈ S)
(One : S.card =1)
(AneB : A ≠ B)
: B ∉ S := by {
  by_contra BinS
  exact AneB (card_eq One AinS BinS)
}

theorem is_singleton {A : K} {S : Finset K}
(AinS : A ∈ S) (OneS : S.card = 1 )
: S={A} := by 
  have OneS2 := Finset.card_eq_one.mp OneS
  #check Finset.nontrivial_iff_ne_singleton
  #check Finset.Nontrivial
  by_contra ne_singleton
  push_neg at ne_singleton
  have := (Finset.nontrivial_iff_ne_singleton AinS).mpr ne_singleton
  unfold Finset.Nontrivial at this
  unfold Set.Nontrivial at this
  have ⟨x,hx,y,hy,xney⟩ := this 
  #check full
  #check card_eq
  #check Finset.nontrivial_iff_ne_singleton 
  exact xney (card_eq OneS hx hy )



#check is_singleton
-- is single_iff_exists and singleton_iff_card_eq_one pointless?? i probably only would need the forward direction in a problem , also the assumption ruins the original point of the lemma which was built on an error in my reasoning.
theorem singleton_iff_exists {S : Finset K}
{B : K} (BinS : B ∈ S): S={B} ↔ ∃x, S={x} := by 
  constructor
  · intro singleton
    use B 
  · intro exist
    have ⟨x,hx⟩ := exist  
    rw [hx] at BinS  
    have Beqx := Finset.mem_singleton.mp BinS
    rw [Beqx]
    assumption


theorem full_singleton  
{S : Finset K} 
{B : K}
(singleton : S={B})
(AinS: A ∈ S)
(AneB : A ≠ B)
: False := by {
   rw [singleton] at AinS 
   have AeqB := Finset.mem_singleton.mp AinS
   contradiction
   
   --exact AneB (by )
---
  --#check Finset.eq_singleton_iff_unique_mem
  --have exist: ∃x, S={x} := by use B
  --rw [Finset.card_eq_one.symm] at exist 
  --#check card_eq
  --exact AneB (card_eq exist AinS

  --exact AneB (card_eq (by rw [Finset.card_eq_one] ; use B) AinS (by rw [singleton] ; exact Finset.mem_singleton.mpr rfl))

  --by_contra BinS
  --exact AneB (card_eq One AinS BinS)
}


#check Finset.eq_singleton_iff_unique_mem
#check Finset.mem_singleton
theorem mem_of_eq_singleton 

{K : Type}
{S : Finset K} {A : K} (h : S={A}) : A ∈ S := by 
  exact (Finset.eq_singleton_iff_unique_mem.mp h).left

  /-
  symm at h
  have := Finset.subset_of_eq h
  exact Finset.singleton_subset_iff.mp this
  -/

theorem singleton_iff_card_eq_one 
{K : Type}
{S : Finset K}
{B : K}
{all : ∀(x:K), x=B}
: S={B} ↔ S.card=1 := by 
  constructor
  · intro singleton
    rw [Finset.card_eq_one]
    #check Classical.not_forall_not
    use B
  · intro One
    rw [Finset.card_eq_one] at One
    have ⟨x,hx⟩ := One
    have := all x
    rw [this] at hx
    rw [Finset.eq_singleton_iff_unique_mem] 
    constructor
    #check mem_of_eq_singleton  
    exact mem_of_eq_singleton hx
    intro y
    intro yinS
    have := all y
    assumption

theorem not_in_of_singleton  
{S : Finset K} 
{B : K}
(singleton : S={B})
(AneB : A ≠ B)
: A ∉ S := by {
  by_contra AinS
  exact full_singleton singleton AinS AneB
  --exact AneB (card_eq (by rw [Finset.card_eq_one] ; use B) AinS (by rw [singleton] ; exact Finset.mem_singleton.mpr rfl))

  --by_contra BinS
  --exact AneB (card_eq One AinS BinS)
}

  #check Finset.subset_of_eq
  #check Finset.card_eq_of_equiv
  #check Finset.card_le_card
  --have := Finset.card_eq_of_equiv (by exact Equiv.setCongr singleton )
  #check Finset.nontrivial_iff_ne_singleton
-- A ∈ S and S.card=1 , so S={A}
theorem eq_singleton_card_one {A : K} {S : Finset K } 
(singleton : S={A}) : S.card=1 := by 
  rw [Finset.card_eq_one]
  use A
  --#check congrArg
  --have : S.card=({A} : Finset K).card  := by
  --  exact congrArg Finset.card singleton
  --rw [this]
  --exact rfl

/-
  #check Finset.subset_of_eq
--  #check Finset.card_le_of_subset
  #check Finset.card_eq_of_equiv
  --have := Finset.card_eq_of_equiv (by exact Equiv.setCongr singleton )
  have Sin := Finset.subset_of_eq singleton
  have Sless := (Finset.eq_iff_card_le_of_subset Sin).mp
 -- have Sless := Finset.card_le_of_subset Sin
  have Aless:  (({A}:Finset K).card) ≤ S.card  := by 
     exact (Finset.eq_iff_card_ge_of_superset Sin).mpr (id (Eq.symm singleton))
  #check Finset.eq_iff_card_le_of_subset
  #check Finset.card_le_one_iff_subset_singleton
--  have Aless := (Finset.eq_iff_card_le_of_subset Ain).mp

  exact (Nat.le_antisymm Aless Sless).symm


  --rw [(Finset.nontrivial_iff_ne_singleton).symm] at ne_singleton
-/

#check Insert
theorem forward {A B C : K} (all : ∀ (x : K), x = A ∨ x = B ∨ x = C) : (Set.univ)  = ({A,B,C} : Set K) := by 
  #check Set.univ_subset_iff
  #check Set.eq_univ_of_univ_subset
  apply Set.eq_of_subset_of_subset
  · intro x
    intro xU
    exact all x

  -----
   --- exact fun ⦃a⦄ a_1 => all a

  ·
    #check Set.mem_univ
    intro x
    rw [eq_true (Set.mem_univ x)]
    rw [implies_true]
    trivial

    --exact fun _ => trivial
    ---
    --intro x
    --intro xABC
    --exact trivial

  -------
    --- exact fun ⦃a⦄ a => trivial

theorem backward  {A B C : K} (h : (Set.univ)  = ({A,B,C} : Set K) ):  ∀ (x : K), x = A ∨ x = B ∨ x = C:= by 
  intro x
  have : x ∈ Set.univ := by exact trivial
  rw [h] at this
  exact this

theorem univ_or  {A B C : K} :  (Set.univ)  = ({A,B,C} : Set K)  ↔  ∀ (x : K), x = A ∨ x = B ∨ x = C:= by 
  constructor
  exact fun a x => backward a x
  #check forward
  exact forward

theorem card_eq_one_iff_singletons 
{A B C : K} {S : Finset K}
(all : ∀(x : K), x = A ∨ x = B ∨ x = C)
: S.card =1 ↔  S = {A} ∨ S = {B} ∨ S = {C}
  := by 
  constructor
  · intro OneS
    rw [Finset.card_eq_one] at OneS
    have ⟨x,hx⟩ := OneS
    have Ors := all x
    rcases Ors with h_1|h_2
    · rw [h_1] at hx
      -- A ∈ S and S.card=1 , so S={A}
      #check full_singleton
      left
      assumption
    · rcases h_2 with h_11|h_22
      -- identical reasoning
      · right
        left
        rw [h_11] at hx
        assumption

      · right
        right
        rw [h_22] at hx
        assumption

  · intro singletons
    rcases singletons with h_1|h_2
    ·
      exact eq_singleton_card_one h_1
    · rcases h_2 with h_11|h_22
      · exact eq_singleton_card_one h_11
      · exact eq_singleton_card_one h_22

theorem card_eq_one_iff_singletons_univ (A B C : K) {S : Finset K} 
(U : (Set.univ)  = ({A,B,C} : Set K))
--(all : ∀(x : K), x = A ∨ x = B ∨ x = C)
: S.card = 1 ↔ S = {A} ∨ S = {B} ∨ S = {C} := by  
  have all := univ_or.mp U
  exact card_eq_one_iff_singletons all 

-- can use to intuitively explain other things like x ∈ {A} means x=A etc.. start from it and then say more generally ...
-- mem1_iff_or for x ∈ {A}
-- mem2_iff_or for x ∈ {A,B} , can use repeat rw way
theorem mem_iff_or 
(A B C: K) (x : K) : x ∈ ({A,B,C} : Set K) ↔  x = A ∨ x =B ∨ x = C := by
  constructor
  · intro xIn
    exact xIn 
  · intro Ors
    exact Ors
 -- exact IfToIff (fun a ↦ a) fun a ↦ a

theorem mem2_iff_or_finset {inst : DecidableEq K} 
{A B : K} {x : K} : x ∈ ({A,B} : Finset K) ↔  x = A ∨ x =B := by
  constructor
  · intro xIn
    rw [Finset.mem_insert] at xIn 
    rw [Finset.mem_singleton] at xIn
    assumption
  · intro xIn
    rw [Finset.mem_insert]  
    rw [Finset.mem_singleton] 
    assumption

theorem mem_iff_or_finset {inst : DecidableEq K} 
{A B C: K} {x : K} : x ∈ ({A,B,C} : Finset K) ↔  x = A ∨ x =B ∨ x = C := by
  constructor
  · intro xIn

    rw [Finset.mem_insert] at xIn
    rw [Finset.mem_insert] at xIn
    rw [Finset.mem_singleton] at xIn
    assumption
  · intro Ors
    rw [Finset.mem_insert]
    rw [Finset.mem_insert]
    rw [Finset.mem_singleton] 
    assumption

#check Finset.mem_insert_self
#check Finset.mem_insert_of_mem
#check mem_of_eq_singleton

theorem one_in_of_card_eq_one {A B C : K} {S : Finset K}  (U : Set.univ = ({A,B,C} : Set K)) (h : S.card = 1) 
(AneB : A ≠ B)
(BneC : B ≠ C)
(AneC : A ≠ C)
: A ∈ S ∧ B ∉ S ∧ C ∉ S ∨ A ∉ S ∧ B ∈ S ∧ C ∉ S ∨ A ∉ S ∧ B ∉ S ∧ C ∈ S := by 

  rw [card_eq_one_iff_singletons_univ A B C U ] at h  
  rcases h with h_1|h_1
  · left
    constructor
    · exact mem_of_eq_singleton h_1

    · constructor
      ·         exact not_in_of_singleton h_1 (AneB.symm) 
      · exact not_in_of_singleton h_1 (AneC.symm)

  -- similarly
  · rcases h_1 with h|h
    · right
      left 
      constructor
      · exact not_in_of_singleton h AneB 
      · constructor
        · exact mem_of_eq_singleton h
        · exact not_in_of_singleton h BneC.symm

    · right
      right
      constructor
      · exact not_in_of_singleton h AneC
      · constructor
        · exact not_in_of_singleton h BneC
        · exact mem_of_eq_singleton h

example {K : Type} (A B C: K) ( all : ∀(x : K), x = A ∨ x = B ∨ x = C) : @Set.univ K = {A,B,C} := by
  exact (Set.eq_univ_of_univ_subset fun ⦃a⦄ a_1 => all a).symm

theorem univ_iff_all {K : Type} {inst : Fintype K} {inst2 : DecidableEq K} {A B C : K}   : Finset.univ = ({A,B,C} : Finset K) ↔  ∀ (x : K), x = A ∨ x = B ∨ x = C:= by 
--  #check Finset.toSet Finset.univ
--  #check Finset.coe_inj
--  rw [Finset.coe_inj.symm]
--  #check Finset.coe_inj
--  #check Finset.toSet
--  have : Finset.univ = {A,B,C} ↔ Set.univ = {A,B,C} := by 
--    constructor
--    · intro Fu
--      rw [Fu]
--    · sorry

  constructor
  · intro U
    intro x
    #check Finset.mem_univ
    have : x ∈ Finset.univ := Finset.mem_univ x 
    rw [U] at this
    #check instDecidableEqBool
    #check Finset.mem_insert_of_mem
    #check Finset.mem_insert
    rw [Finset.mem_insert] at this
    rw [Finset.mem_insert] at this
    rw [Finset.mem_singleton] at this
    assumption
  · intro U
    apply Finset.ext
    intro a
    constructor
    · intro aU
      rcases U a with h|h
      · rw [h]
        exact Finset.mem_insert_self A {B, C}
      · rcases h with h_1|h_1
        · rw [h_1]  
          #check Finset.mem_insert_of_mem
          apply Finset.mem_insert_of_mem
          exact Finset.mem_insert_self B {C}
        · rw [h_1]
          apply Finset.mem_insert_of_mem
          apply Finset.mem_insert_of_mem
          exact Finset.mem_singleton.mpr rfl

    · exact fun a_1 => Finset.mem_univ a

theorem univ_iff_all2 {inst : Fintype K} {inst2 : DecidableEq K} {A B : K}   : Finset.univ = ({A,B} : Finset K) ↔  ∀ (x : K), x = A ∨ x = B := by 
  constructor
  · 
    intro U 
    intro x
    #check Finset.mem_univ
    have xinU := Finset.mem_univ x
    rw [U] at xinU
    rw [Finset.mem_insert] at xinU
    rw [Finset.mem_singleton] at xinU
    assumption

  · intro all 
    apply Finset.eq_of_subset_of_card_le 

    intro x
    intro hx
    rcases all x with h|h
    · rw [h]
      apply Finset.mem_insert_self
    · rw [h]
      apply Finset.mem_insert_of_mem 
      rw [Finset.mem_singleton]

    apply Finset.card_le_card
    apply Finset.subset_univ



#check Set.mem_compl
  #check Set.mem_compl_iff
  #check Set.inter_eq_compl_compl_union_compl

#check Finset.Nonempty
#check Finset.empty
#check not_iff_not.mpr Finset.not_nonempty_iff_eq_empty
#check Finset.not_nonempty_iff_eq_empty.mpr

#check Finset.Nonempty
#check Finset.empty
#check not_iff_not.mpr Finset.not_nonempty_iff_eq_empty
#check Finset.not_nonempty_iff_eq_empty.mpr
#check Finset.univ_inter
example {K : Type} {inst3 : Unique K} {inst : Fintype K} {inst2 : DecidableEq K} {S : Finset K}: Finset.univ ∩ S = ∅ → S = ∅ := by 
  intro h
  rw [Finset.univ_inter] at h
  assumption

theorem all2_in_one_other_empty 
{K : Type}
{A B : K}
{inst : Fintype K}
{inst2 : DecidableEq K} {S S' : Finset K} (h : S ∩ S' = ∅)(all : ∀(x:K), x = A ∨ x = B) (hA : A ∈ S) (hB : B ∈ S) : S' = ∅ := by 
  have : S = (Finset.univ) := by 
    have := (@univ_iff_all2 K inst inst2  ).mpr all
    rw [this]
    apply Finset.ext
    intro a
    constructor
    · intro aSprime
      exact mem2_iff_or_finset.mpr (all a)
    · intro h 
      #check mem2_iff_or_finset
      rw [mem2_iff_or_finset] at h
      rcases h with h|h
      rw [h]
      assumption
      rw [h]
      assumption

  rw [this] at h
  rw [Finset.inter_comm] at h
  rw [Finset.inter_univ] at h
  assumption

  --by_contra nonemp 
----  have := (not_iff_not.mpr Finset.not_nonempty_iff_eq_empty).mpr nonemp
  --rw [(not_iff_not.mpr Finset.not_nonempty_iff_eq_empty).symm] at nonemp

  --push_neg at nonemp
  ---- now use helper theorem
  --unfold Finset.Nonempty at nonemp 
  --have ⟨x,hx⟩ := nonemp 
  --rcases all x with h_1|h_2
  --· rw [h_1] at hx
  --  exact disjoint h hA hx 
  --· rw [h_2] at hx
  --  exact disjoint h hB hx

theorem all3_in_one_other_empty 
{K : Type}
{inst : DecidableEq K} {A B C : K} {S S' : Finset K}
{all : ∀(x:K), x=A ∨ x=B ∨ x=C}
(hA : A ∈ S)
(hB : B ∈ S)
(hC : C ∈ S)
(h : S ∩ S'= ∅ )
: S'=∅ := by 
  rw [Finset.eq_empty_iff_forall_not_mem] 
  intro x
  intro xInS'
  rcases all x with h_1|h_2
  · rw [h_1] at xInS'
    exact disjoint_general h hA xInS'
  · rcases h_2 with h_3|h_4
    · rw [h_3] at xInS'
      exact disjoint_general h hB xInS' 
    · rw [h_4] at xInS'
      exact disjoint_general h hC xInS' 


-- if one is empty then the other eq_all
theorem S_union_S'_eq_univ
{inst : DecidableEq K} {inst2 : Fintype K} {A B C : K} {S S' : Finset K}
(all : ∀(x:K), x=A ∨ x=B ∨ x=C)
(Or : ∀(x:K), x ∈ S ∨ x ∈ S')
: S ∪ S' = Finset.univ := by  
  #check Set.eq_of_subset_of_subset
  #check Finset.eq_of_subset_of_card_le
  #check Finset.card_le_univ
  #check Finset.subset_univ
  --apply Finset.eq_of_subset_of_card_le
  --· apply Finset.subset_univ
  --· sorry

  apply Finset.ext
  intro a
  constructor
  · #check Finset.mem_univ
    intro 
    apply Finset.mem_univ
  · have : S ∪ S' = {A,B,C} := by 
      apply Finset.ext 
      intro b
      constructor
      · intro t
        #check mem_iff_or_finset
        rw [mem_iff_or_finset]
        exact all b
      · intro t
        #check Finset.mem_union 
        rw [Finset.mem_union]
        exact Or b

    intro inU
    rw [this]
    #check univ_iff_all
    have Ueq : Finset.univ ={A,B,C}:= (univ_iff_all).mpr all
    rw [←Ueq]
    trivial

theorem empty_eq_all {inst : DecidableEq K} {A B C : K} {S S' : Finset K}
{inst2 : Fintype K}
{all : ∀(x:K), x=A ∨ x=B ∨ x=C}
{Or : ∀(x:K), x ∈ S ∨ x ∈ S'}
(Semp : S= ∅ ) : S' ={A,B,C} := by 
  #check S_union_S'_eq_univ
  have : S ∪ S' = Finset.univ := S_union_S'_eq_univ all Or
  #check univ_iff_all
  have U: Finset.univ = {A,B,C} := (univ_iff_all).mpr all
  rw [U] at this
  rw [Semp] at this
  simp at this
  #check Finset.empty_union
  assumption

theorem all3_in_one_other_eq_all {inst : DecidableEq K} {A B C : K} {S S' : Finset K}
{all : ∀(x:K), x=A ∨ x=B ∨ x=C}
(hA : A ∈ S)
(hB : B ∈ S)
(hC : C ∈ S)
(h : S ∩ S'= ∅ ) : S={A,B,C} := by 
  apply Finset.ext
  intro a
  constructor
  · intro aInS
    -- S is the whole universe, so S' empty
    -- S = Finset.univ , Finset.univ ∩ S' = ∅ #check Finset.inter
    sorry
  · sorry 

theorem everyone_in_set_eq {inst : DecidableEq K} {S : Finset K} {A B C : K} (all : ∀ (x : K), x = A ∨ x = B ∨ x = C) : (A ∈ S ∧ B ∈ S ∧ C ∈ S) ↔ (S = ({A,B,C} : Finset K) ) := by 
  constructor
  · intro allknaves
    #check Finset.ext_iff
    apply Finset.ext
    intro a
    constructor
    · intro aKn
      rcases all a with h|h
      · rw [h]
        exact Finset.mem_insert_self A {B, C}
      · rcases h with h_1|h_1
        · rw [h_1]
          #check Finset.mem_insert_of_mem
          apply Finset.mem_insert_of_mem
          exact Finset.mem_insert_self B {C}
        · rw [h_1]  
          apply Finset.mem_insert_of_mem
          apply Finset.mem_insert_of_mem
          exact Finset.mem_singleton.mpr rfl

    · intro aIn
      rcases all a with h|h
      · rw [h]  
        exact allknaves.left
      · rcases h with h_1|h_1
        · rw [h_1]
          exact allknaves.right.left
        · rw [h_1]
          exact allknaves.right.right

  · intro KnaveEveryone
    rw [KnaveEveryone]

    constructor
    · exact Finset.mem_insert_self A {B, C}
    · constructor

      · apply Finset.mem_insert_of_mem
        exact Finset.mem_insert_self B {C}

      · apply Finset.mem_insert_of_mem
        apply Finset.mem_insert_of_mem
        exact Finset.mem_singleton.mpr rfl

theorem two_in_one_other_nonemp {inst : DecidableEq K} {A B C : K} {S S' : Finset K}
(all : ∀ (x : K), x = A ∨ x = B ∨ x = C)
--{h : S ∩ S' = ∅}
(Or : ∀(x:K), x ∈ S ∨ x ∈ S')
(hA : A ∈ S)
(hB : B ∈ S)
(notall : S ≠ ({A,B,C} : Finset K) ) : S' ≠ ∅ := by 
  intro S'emp
  --rw [Finset.eq_empty_iff_forall_not_mem] at S'emp
  have hnC : C ∉ S := by 
    intro hC 
    #check all3_in_one_other_empty 
    #check everyone_in_set_eq
    exact notall ((everyone_in_set_eq all).mp ⟨hA,⟨hB,hC⟩ ⟩  )
    --exact all3_in_one_other_empty hA hB hC h
  have := Or C
  simp [hnC] at this
  rw [S'emp] at this
  contradiction


#check univ_iff_all
theorem univ_set_iff_or 
{K : Type}
{x : K}
{inst : DecidableEq K} {A B C : K} 
{inst3 : DecidableEq Bool}
{inst2 : Fintype K}
: (x = A ∨ x = B ∨ x = C) ↔ x ∈ ({A,B,C} : Finset K) := by 
  #check univ_iff_all
  --rw [univ_iff_all inst2 inst] 
  constructor 
  · 
    #check mem_iff_or
    intro ors
    have := (@mem_iff_or_finset _ inst _ _ _ x).mpr ors
    assumption
    --exact fun a ↦ (fun {K} {inst} {A B C x} ↦ mem_iff_or_finset.mpr) a

    --intro all
    --have U : Finset.univ = {A, B, C} := (univ_iff_all inst2 inst).mpr (all)
    --rw [←U]
    --exact Finset.mem_univ x
  · intro mem
    exact mem_iff_or_finset.mp mem


#check Finset.univ_subset_iff
#check Finset.subset_univ
theorem set_subset_univ {inst : DecidableEq K} 
{inst2 : Fintype K}
{A B C : K} {S : Finset K}
(all : ∀ (x : K), x = A ∨ x = B ∨ x = C)
: S ⊆ {A,B,C} := by 
  rw [(univ_iff_all).symm] at all
  rw [←all]
  exact Finset.subset_univ S

theorem every_elt_in_univ {inst : DecidableEq K} {A B C : K} 
{inst2 : Fintype K}
{all : ∀ (x : K), x = A ∨ x = B ∨ x = C}
: ∀(x:K), x ∈ ({A,B,C} : Finset K) := by 
  --have : Finset.univ = {A,B,C} := univ_iff_all.mpr all
  rw [(univ_iff_all).symm] at all
  rw [←all]
  intro x
  exact Finset.mem_univ x

theorem not_eq_singleton_of_not_mem {A : K} {S : Finset K} (h : A ∉ S) : S ≠ {A} := by 
  intro eq
  have := mem_of_eq_singleton eq
  contradiction

theorem already_full 
{A B : K}
{S : Finset K}
(hA : A ∈ S)
(either_single : S={A} ∨ S={B})
(AneB : A ≠ B)
: S={A} := by
  rcases either_single with h|h
  assumption
  
  rw [h] at hA 
  rw [Finset.mem_singleton] at hA
  exfalso 
  contradiction

theorem full2 
{A B C : K}
(S : Finset K) 
{inst : DecidableEq K}
{inst2 : Fintype K}
(AinS: A ∈ S)
(BinS: B ∈ S)
(Two : S.card =2)
(AneB : A ≠ B)
(BneC : B ≠ C)
(AneC : A ≠ C)
(all : ∀(x:K),x=A ∨ x=B ∨ x=C)
: C ∉ S := by {
  #check Finset.card_le_two
  intro CinS
  #check Finset.card_eq_two 
  have two := Two
  rw [Finset.card_eq_two] at Two

  --have ⟨x,y,xney,Seqxy⟩ := Two  
  --rw [Seqxy] at AinS  
  --rw [Seqxy] at BinS  
  --rw [Seqxy] at CinS  

  have : S.card=3 := by 
    rw [Finset.card_eq_three]
    use A
    use B
    use C
    constructor
    assumption
    constructor
    assumption
    constructor 
    assumption 
    #check univ_iff_all 
    rw [(univ_iff_all).symm] at all
    have : {A,B,C} ⊆ S := by
      intro x
      intro hx
      #check mem_iff_or_finset
      rw [mem_iff_or_finset] at hx
      rcases hx  with h|h
      rw [←h] at AinS
      assumption
      rcases h with h_1|h_1
      rw[h_1] 
      assumption
      rw[h_1] 
      assumption

    #check Finset.eq_of_subset_of_card_le
    --#check Finset.card_le_of_subset
    apply Finset.eq_of_subset_of_card_le
    rw [←all]
    apply Finset.subset_univ S
    --#check Finset.card_le_of_subset
    -- make my own theorem which would avoid using Finset.card_le_of_subset
    apply Finset.card_le_card
    assumption
    --sorry
  rw [two] at this
  contradiction

}

-- transition from finset to set stuff and vice versa
-- this2: B ∈ Set.toFinset (Knight) := by
-- {hK : Finset Knight}
-- this was being considered when Set was still used, but now everything if Finset
theorem memToFinset (Knight : Set K ) {finKnight : Fintype Knight}  (AKnight : A ∈ Knight) : A ∈ (Set.toFinset Knight) := by  
  have FinKnight:= Set.toFinset Knight
  exact Set.mem_toFinset.mpr AKnight

axiom not_both
  {Inhabitant : Type}
  {A : Inhabitant}
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
  (AKnight : A ∈ Knight) (AKnave : A ∈ Knave)  : False
