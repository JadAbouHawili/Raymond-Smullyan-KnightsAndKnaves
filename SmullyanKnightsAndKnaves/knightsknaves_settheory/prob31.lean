import SmullyanKnightsAndKnaves.knightsknaves_3
#check Finset.card_bij
#check Equiv.setCongr
example {K : Type} [Fintype K] [DecidableEq K] {s t : Set K} (h: s = t) : ∀(x:K) , x ∈ s ↔ x ∈ t := by
  #check congrFun
  exact?

example {K : Type} [Fintype K] [DecidableEq K] {s t : Finset K} : (s = t) ↔  (∀(x:K) , x ∈ s ↔ x ∈ t) := by

  #check Finset.subtype_eq_univ
  #check Finset.subtype
  constructor
  · sorry
  · intro h
    ext a
    sorry
  --exact Finset.ext_iff
example {K : Type} [Fintype K] [DecidableEq K] {s t : Finset K} (h: s = t) : ∀(x:K) , x ∈ s ↔ x ∈ t := by
  exact fun x ↦ Eq.to_iff (congrFun (congrArg Membership.mem h) x)
example {K : Type} [Fintype K] [DecidableEq K] {s t : Finset K} (h: s = t) : s ≃ t := by
  have : (s : Set K) ≃ (t : Set K) := by rw [h]
  exact this
--  exact Equiv.subtypeEquivProp (by rw [h])

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
  set_knight_to_knave
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


theorem simp_eq222 {K : Type} [DecidableEq K] [Fintype K] {S : Finset K} : S = (Finset.univ : Finset K) ↔ ∀(x:K), x ∈ S := by
  exact Finset.eq_univ_iff_forall

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

example
{stA : A ∈ Knight ↔ Knave = {A,B,C}}
{stB : B ∈ Knight ↔ (Knight : Finset Inhabitant).card =1  }
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
  knave_interp at stB 
  have notoneKnight := stB.mp BKnave
  apply notoneKnight  
  rw [Finset.card_eq_one]
  use C
  have CKnight : C ∈ Knight
  knave_interp
  intro CKnave
  have : Knave = {A,B,C} 
  exact full3 AKnave BKnave CKnave
  contradiction
  rw [Finset.eq_singleton_iff_unique_mem]
  constructor
  assumption
  intro x h 
  rcases all x with h'|h'|h' 
  rw [h'] at h ; contradiction 
  rw [h'] at h ; contradiction 
  assumption
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

-- A : all of us are knaves
-- B : exactly one of us is a knight
example
{stA : A ∈ Knight ↔ Knave = {A,B,C}}
{stB : B ∈ Knight ↔ Knight = {A} ∨ Knight = {B} ∨ Knight = {C} }
--}
: A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave := by
  #check knave_notknightIff
  --knave_interp at stA
  have AKnave : A ∈ Knave -- proof for this like a primitive (repeated pattern)
  set_knave_to_knight
  intro AKnight
  have allknave := stA.mp AKnight
  have AKnave : A ∈ Knave
  rw [allknave]
  -- primitive of proving A ∈ {A,B,C}... , introduce Finset.mem_insert
  simp
  contradiction

  -- replace all2 with knight ∪ knave = {A,B,C}
  #check all
  -- semantics is change interpretation to knaves

  knave_interp at stA
  /-

stA : A ∈ Knave ↔ ¬Knave = {A, B, C}

  knave_interp at *
  -/
  --
  -- set_knight_to_knave 
  -- rw [not_iff_not.symm] at stA 
  -- simp only[knight_notknaveIff,not_not] at stA
  have notallknave := stA.mp AKnave
  have BKnight : B ∈ Knight
  set_knight_to_knave
  intro BKnave

  -- can also use this
  -- primitive , proving two sets are equal and there are two ways , either subset.antisymm or unique_mem(all is needed so that would be introduced as a primitive as well)
  have KnighteqC : Knight = {C}
  --rw [Finset.eq_singleton_iff_unique_mem]

  
  --rw [Finset.ext_iff]
  apply Finset.Subset.antisymm
  --intro x hx
  --rcases all x with h|h|h
  --rw [h] at hx ; contradiction
  --rw [h] at hx ; contradiction
  --rw [h] ; simp
  have : Knight ⊆ {A,B,C} := by 
    by_universe

  set_knave_to_knight at AKnave
  -- primitive
  have : Knight ⊆ {B,C} := by
    exact (Finset.subset_insert_iff_of_notMem AKnave).mp this
  remove_top at this
  set_knave_to_knight at BKnave
  remove_top at this
  intro a h
  simp at h
  rw [h]
  set_knight_to_knave
  intro CKnave
  have allknave : Knave = {A,B,C}
  rw[Finset.ext_iff]
  simp
  intro x
  simp [all2]
  sorry

/-
  apply Finset.Subset.antisymm
  by_universe
  intro a' h'
  simp at h'
  rcases h' with h|h|h
  rw [h] ; assumption
  rw [h] ; assumption
  rw [h] ; assumption
  contradiction
  -/

  have BKnight : B ∈ Knight
  rw [stB]
  right ; right ; assumption
  contradiction

  have oneKnight := stB.mp BKnight
  rcases oneKnight with singleton|singleton|singleton
  -- use theorem here
  · 
    have AKnight : A ∈ Knight
    rw [singleton] ; simp
    contradiction

  · 
    have CKnave : C ∈ Knave
    set_knave_to_knight
    intro CKnight
    rw [singleton] at CKnight
    simp at CKnight
    contradiction
    constructor ; assumption
    constructor ; assumption ; assumption

  · 
    rw [singleton] at BKnight
    simp at BKnight ; contradiction

#check Finset.singleton_subset_iff
#check Finset.singleton_subset_singleton
#check Finset.singleton_subset_set_iff



example
{stA : A ∈ Knight ↔ Knave.card = 3}
{stB : B ∈ Knight ↔ Knight.card = 1}
: A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave := by
  have AKnave : A ∈ Knave
  set_knave_to_knight
  intro AKnight
  have allKnave := stA.mp AKnight
  have Knavesubset: Knave ⊆ {A,B,C}
  by_universe
  have KnaveAll: Knave = {A,B,C}
  apply eq_of_subset_card_eq Knavesubset
  simp
  assumption

  have AKnave : A ∈ Knave
  rw [KnaveAll] ; simp
  contradiction

  have BKnight : B ∈ Knight
  set_knight_to_knave
  intro BKnave
  knave_interp at stB
  have notoneKnave := stB.mp BKnave
  knight_or_knave C with CKnight CKnave
  have : Knight.card=1
  rw [Finset.card_eq_one]
  use C

  rw [Finset.eq_singleton_iff_unique_mem]
  constructor ; assumption
  intro x h
  
  


  sorry

#check Finset.eq_singleton_iff_unique_mem

variable {α : Type*} {β : Type*}
/-
theorem Subsingleton.eq_singleton_of_mem (hs : s.Subsingleton) {x : α} (hx : x ∈ s) : s = {x} :=
  ext fun _ => ⟨fun hy => hs hx hy ▸ mem_singleton _, fun hy => (eq_of_mem_singleton hy).symm ▸ hx⟩


theorem eq_of_mem_singleton {x y : α} (h : x ∈ ({y} : Set α)) : x = y :=
  h

-/
#check Set.eq_singleton_or_nontrivial
#check Finset.mem_singleton
example {K : Type} {A : K} : A ∈ ({A}:Finset K) := by
  exact?

theorem mem_of_eq_singleton2 {s : Finset α} {a : α} : s = {a} → a ∈ s  := by
  grind

theorem subset_of_mem_powerset22 {x s : Set α} (h : x ∈ 𝒫 s) : x ⊆ s := h
  theorem powerset {s t: Set α} : s ⊆ t → ∃ p ∈ 𝒫 t , s = p  := by
    #check Set.mem_powerset_iff
    grind?
    (expose_names; exact fun a ↦ (fun {a'} ↦ exists_eq_right'.mpr) a)


theorem mem_of_eq_singleton
{K : Type}
{S : Finset K} {A : K} (h : S={A}) : A ∈ S := by
  grind

#check Finset.eq_singleton_or_nontrivial
example
{K : Type}
{A : K} {S : Set K} (h : A ∉ S) : S ≠ {A} := by 
  exact Ne.symm (ne_of_mem_of_not_mem' rfl h)

theorem not_eq_singleton_of_not_mem
{K : Type}
{A : K} {S : Set K} (h : A ∉ S) : S ≠ {A} := by 
  exact Ne.symm (ne_of_mem_of_not_mem' rfl h)

theorem mem_of_eq_singleton222 {s : Set α} {a : α} : s = {a} → a ∈ s  := by
  grind


example 
{K : Type}
{inst : DecidableEq K} [Fintype K] {S : Finset K} (all3 : ∀ (x : K), x ∈ S) : S = Finset.univ := by 
  exact simp_eq222.mpr all3

/-
uniqueness of univ...
uniqueness of a set , i.e there exists only one set that satisfies a certain property/proposition
theorem everyone_in_set_eq 
{K : Type}
{inst : DecidableEq K} {S : Finset K} {A B C : K} (all3 : ∀ (x : K), x = A ∨ x = B ∨ x = C) : (A ∈ S ∧ B ∈ S ∧ C ∈ S) ↔ (S = ({A,B,C} : Finset K) ) := by 
  constructor
  · intro allS
    ext a
    constructor
    · intro aKn
      rcases all3 a with h|h|h
<;> rw [h] ; simp

    · intro aIn
      rcases all3 a with h|h|h
<;> rw [h]
      · exact allS.left
      · exact allS.right.left
      · exact allS.right.right

  · intro SEveryone
    rw [SEveryone]
    constructor <;> try constructor
    simp

#check Finset.eq_empty_iff_forall_not_mem
theorem two_in_one_other_nonemp 
{K : Type}
{inst : DecidableEq K} {A B C : K} {S S' : Finset K}
(all : ∀ (x : K), x = A ∨ x = B ∨ x = C)
(hA : A ∈ S)
(hB : B ∈ S)
(Or : ∀(x:K), x ∈ S ∨ x ∈ S')
(notall : S ≠ ({A,B,C} : Finset K) ) : S' ≠ ∅ := by 
  -- union axiom is interesting here where S ∪ S' = {A,B,C}
  intro S'emp
  have hnC : C ∉ S := by 
    intro hC
    exact notall ((everyone_in_set_eq all).mp ⟨hA,⟨hB,hC⟩ ⟩  )
  have : C ∈ S' := by exact notinleft_inright (Or C) hnC
  rw [S'emp] at this
  contradiction


theorem already_full 
{K : Type}
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

example
  {inst : DecidableEq Inhabitant}
  {inst2 : Fintype Inhabitant}
  {all : ∀(x : Inhabitant), x = A ∨ x = B ∨ x = C}
{stA : A ∈ Knight  ↔ (Knave={A,B,C}) }
{stAn : A ∈ Knave ↔ ¬ (Knave={A,B,C}) }
{stB: B ∈ Knight ↔ (Knight = {A} ∨ Knight = {B} ∨ Knight = {C}) }
{stBn: B ∈ Knave ↔ ¬ (Knight = {A} ∨ Knight = {B} ∨ Knight = {C}) }
  :

  A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave
  := by
  -- also similar to I am a Knave
  have AKnave : A ∈ Knave := by
    set_knave_to_knight
    intro AKnight
    have everyoneknave := stA.mp AKnight  
    have AKnave: A ∈ Knave := by rw [everyoneknave] ; simp
    contradiction
  have notallknave := stAn.mp AKnave
  have AnKnight: Knight ≠ {A} := by 
    intro KnighteqA 
    have := mem_of_eq_singleton KnighteqA 
    contradiction
  simp [AnKnight] at stB
  have BKnight2 : B ∈ Knight := by 
    set_knight_to_knave
    intro BKnave
    have CnKnave : C ∉ Knave := by 
      intro CKnave
      have : Knave = {A,B,C} := by 
        #check everyone_in_set_eq
        exact (everyone_in_set_eq all).mp ⟨AKnave,BKnave ,CKnave⟩
      contradiction 
    -- so Knight = {C} so B knight, contradiction 
    have : Knight = {C} := by
      apply Finset.Subset.antisymm
      · have : Finset.univ = {A,B,C} := by exact univ_iff_all.mpr all
        have : Knight ⊆ {A,B,C} := by  
          by_universe
          exact inst2
        set_knave_to_knight at AKnave
        set_knave_to_knight at BKnave
        remove_top at this
        remove_top at this
      · intro a h
        simp at h
        rw [h]
        set_knight_to_knave
        assumption
    simp [this] at stB
    contradiction
  have BKnight : B ∈ Knight := by 
    set_knight_to_knave
    intro BKnave
    have notoneknight := stBn.mp BKnave
    push_neg at notoneknight
    -- by stAn, C is a knight because otherwise Knave={A,B,C}. then knight={C} contradiction
    -- since ¬Knave={A,B,C} then Knight is not empty. If C knave, then knight empty or then Knave={A,B,C} contradition. So C not knave, i.e C Knight but if C Knight then Knight ={C} contradiction
    --#check all3_in_one_other_empty
    --#check all3_in_one_other_eq_all
    --#check two_in_one_other_nonemp 
    have Or := KorKn
    simp [or_comm] at Or
    -- instead of other nonemp , instead have other is singleton
    have S'nonemp := two_in_one_other_nonemp all  AKnave BKnave (Or) notallknave
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
          contradiction
        · rcases h_2 with h_3|h_4
          · rw [h_3] at xKnight
            contradiction
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
  set_knave_to_knight at AKnave
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
{A B C : K}
{inst : DecidableEq K}
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
    ext a
    constructor
    · intro ainS
      simp
      exact all a
    · exact fun _ => this a
  contradiction

#check Set.Subset.antisymm
#check Set.ext_iff.mpr
  -/
example {A:Type} [DecidableEq Type]
: {A,A} = ({A} : Finset Type) := by
  {
  exact Finset.pair_eq_singleton A
  exact Set.pair_eq_singleton A
  ext x
  simp?
}
#check Finset.insert_eq_of_mem
