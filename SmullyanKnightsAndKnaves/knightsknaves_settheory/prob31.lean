import SmullyanKnightsAndKnaves.knightsknaves
import SmullyanKnightsAndKnaves.knightsknaves_3

open settheory_approach
set_option push_neg.use_distrib true

variable [DecidableEq Inhabitant]
variable [Fintype Inhabitant]

-- A : all of us are knaves
-- B : exactly one of us is a knight
example
{stA : A ∈ Knight ↔ allKnave}
{stAn : A ∈ Knave ↔ ¬allKnave}
{stB : B ∈ Knight ↔ oneKnight}
{stBn : B ∈ Knave ↔ ¬oneKnight}
: A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave := by
  have AKnave : A ∈ Knave
  set_knave_to_knight
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
  set_knave_to_knight at notallknave
  have OneKnight : oneKnight
  unfold oneKnight
  simp [AKnave,BKnave,notallknave]
  contradiction

  constructor
  assumption
  have OneKnight := stB.mp BKnight
  unfold oneKnight at OneKnight
  simp [AKnave,BKnight] at OneKnight
  set_knave_to_knight at AKnave
  set_knight_to_knave at BKnight
  simp [AKnave,BKnight] at OneKnight
  assumption


example
{stA : A ∈ Knight ↔ Knave = {A,B,C}}
{stAn : A ∈ Knave ↔ Knave ≠ {A,B,C}}
{stB : B ∈ Knight ↔ Knight = {A} ∨ Knight = {B} ∨ Knight = {C} }
{stBn : B ∈ Knave ↔ ¬(Knight = {A} ∨ Knight = {B} ∨ Knight = {C}) }
{all2:  Knight ∪ Knave = {A,B,C}}
: A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave := by
  have AKnave : A ∈ Knave
  set_knave_to_knight
  intro AKnight
  have notallKnave := stA.mp AKnight
  have : A ∈ Knave 
  rw [notallKnave] ; mem_finset
  contradiction

  have notallKnave := stAn.mp AKnave
  have : Knight ≠ ∅ := by
    rw [←all2] at notallKnave
    intro h
    rw [h] at notallKnave
    simp at notallKnave
  #check Finset.nonempty_iff_eq_singleton_default 
  #check Finset.ne_empty_of_mem
  #check Finset.nonempty_iff_ne_empty
  rw [Finset.nonempty_iff_ne_empty.symm] at this
  have : ∃a, a ∈ Knight := by exact this
  #check Finset.nonempty_iff_eq_singleton_default
  have BKnight : B ∈ Knight
  set_knight_to_knave
  intro BKnave
  have knight_not_eq_singleton := stBn.mp BKnave
  have : C ∈ Knight := by
    have ⟨a,ha⟩ := this

    have all2:= all a
    rcases all a with h|h|h
    simp_all [h,ha]
    simp_all [h,ha]
    simp_all [h,ha]
    --rw [h] at ha; assumption
    --rw [h] at ha; contradiction

  -- can also use this
  -- primitive , proving two sets are equal and there are two ways , either subset.antisymm or unique_mem(all is needed so that would be introduced as a primitive as well)
  have KnighteqC : Knight = {C}
  rw [Finset.eq_singleton_iff_unique_mem]
  constructor
  assumption
  intro x h
  -- similar reasoning
  rcases all x with h|h|h
  simp_all [h]
  simp_all [h]
  simp_all [h]
  simp_all

/-
  have knight_singleton := stB.mp BKnight
  rw [Finset.eq_singleton_iff_unique_mem] at knight_singleton
  simp [AKnave,knight_notknaveIff] at knight_singleton
  -/
  have knight_not_A: Knight ≠ {A}
  intro h
  rw [h] at BKnight
  mem_finset at BKnight
  contradiction

  have knight_not_C: Knight ≠ {C}
  intro h
  rw [h] at BKnight
  mem_finset at BKnight
  contradiction

  have : Knight = {B}
  simp [knight_not_A,knight_not_C,BKnight] at stB
  assumption

  conv at stA => simp
  --simp_rw [] at stA
  -- after simp , hypothesis goes to bottom

/-


example
{stA : A ∈ Knight ↔ Knave = {A,B,C}}
{stAn : A ∈ Knave ↔ Knave ≠ {A,B,C}}
{stB : B ∈ Knight ↔ Knight = {A} ∨ Knight = {B} ∨ Knight = {C} }
{stBn : B ∈ Knave ↔ ¬(Knight = {A} ∨ Knight = {B} ∨ Knight = {C}) }
{all2:  ∀ (x : Inhabitant), x = A or x = B or x = C
}
: A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave := by
  have AKnave : A ∈ Knave
  set_knave_to_knight
  intro AKnight
  have allknave := stA.mp AKnight
  have AKnave : A ∈ Knave
  rw [allknave]
  -- primitive of proving A ∈ {A,B,C}... , introduce Finset.mem_insert
  mem_finset
  contradiction

  -- replcae all2 with knight ∪ knave = {A,B,C}
  have notallknave := stAn.mp AKnave
  have BKnight : B ∈ Knight
  set_knight_to_knave
  intro BKnave

  -- can also use this
  -- primitive , proving two sets are equal and there are two ways , either subset.antisymm or unique_mem(all is needed so that would be introduced as a primitive as well)
  have KnighteqC : Knight = {C}
  --rw [Finset.eq_singleton_iff_unique_mem]

  rw [Finset.ext_iff]
  apply Finset.Subset.antisymm
  have : Knight ⊆ {A,B,C} := by 
    by_universe

  set_knave_to_knight at AKnave
  #check Finset.subset_insert_iff_of_not_mem
  remove_top at this
  set_knave_to_knight at BKnave
  remove_top at this

  intro a h
  mem_finset at h
  rw [h]
  set_knight_to_knave
  intro CKnave
  have allknave : Knave = {A,B,C}
  rw[Finset.ext_iff]
  mem_finset
  intro x
  simp [all2]
  sorry

/-
  apply Finset.Subset.antisymm
  by_universe
  intro a' h'
  mem_finset at h'
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
    rw [singleton] ; mem_finset
    contradiction

  · 
    have CKnave : C ∈ Knave
    set_knave_to_knight
    intro CKnight
    rw [singleton] at CKnight
    mem_finset at CKnight
    contradiction
    constructor ; assumption
    constructor ; assumption ; assumption

  · 
    rw [singleton] at BKnight
    mem_finset at BKnight ; contradiction

#check Finset.singleton_subset_iff
#check Finset.singleton_subset_singleton
#check Finset.singleton_subset_set_iff


theorem mem_of_eq_singleton 
{K : Type}
{S : Finset K} {A : K} (h : S={A}) : A ∈ S := by
  rw [h]
  mem_finset


theorem everyone_in_set_eq 
{K : Type}
{inst : DecidableEq K} {S : Finset K} {A B C : K} (all3 : ∀ (x : K), x = A ∨ x = B ∨ x = C) : (A ∈ S ∧ B ∈ S ∧ C ∈ S) ↔ (S = ({A,B,C} : Finset K) ) := by 
  constructor
  · intro allS
    ext a
    constructor
    · intro aKn
      rcases all3 a with h|h|h
<;> rw [h] ; mem_finset

    · intro aIn
      rcases all3 a with h|h|h
<;> rw [h]
      · exact allS.left
      · exact allS.right.left
      · exact allS.right.right

  · intro SEveryone
    rw [SEveryone]
    constructor <;> try constructor
    mem_finset


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

theorem not_eq_singleton_of_not_mem
{K : Type}
{A : K} {S : Finset K} (h : A ∉ S) : S ≠ {A} := by 
  intro eq
  have := mem_of_eq_singleton eq
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
    have AKnave: A ∈ Knave := by rw [everyoneknave] ; mem_finset
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
        mem_finset at h
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
      mem_finset
      exact all a
    · exact fun _ => this a
  contradiction

#check Set.Subset.antisymm
#check Set.ext_iff.mpr
example {A:Type}
: {A,A} = ({A} : Set Type) := by
  {
  ext x
  mem_set
  simp
  }
  -/
