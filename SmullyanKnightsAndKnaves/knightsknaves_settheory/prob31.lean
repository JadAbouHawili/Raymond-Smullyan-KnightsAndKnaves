import SmullyanKnightsAndKnaves.knightsknaves
import SmullyanKnightsAndKnaves.knightsknaves_3

open settheory_approach
set_option push_neg.use_distrib true

variable [DecidableEq Inhabitant]

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
{inst2 : Fintype Inhabitant}
{stA : A ∈ Knight ↔ Knave = {A,B,C}}
{stAn : A ∈ Knave ↔ Knave ≠ {A,B,C}}
{stB : B ∈ Knight ↔ Knight = {A} ∨ Knight = {B} ∨ Knight = {C} }
{stBn : B ∈ Knave ↔ ¬(Knight = {A} ∨ Knight = {B} ∨ Knight = {C}) }
: A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave := by
  have AKnave : A ∈ Knave
  set_knave_to_knight
  intro AKnight
  have allknave := stA.mp AKnight
  have AKnave : A ∈ Knave
  rw [allknave]
  is_mem
  contradiction

  have notallknave := stAn.mp AKnave
  have BKnight : B ∈ Knight
  set_knight_to_knave
  intro BKnave

  -- can also use this
  --rw [Finset.eq_singleton_iff_unique_mem] 
  have KnighteqC : Knight = {C}
  apply Finset.Subset.antisymm
  have : Knight ⊆ {A,B,C} := by by_universe
  set_knave_to_knight at AKnave
  remove_top at this
  set_knave_to_knight at BKnave
  remove_top at this

  intro a h
  mem_set at h
  rw [h]
  set_knight_to_knave
  intro CKnave
  have allknave : Knave = {A,B,C}
  apply Finset.Subset.antisymm
  by_universe
  intro a h
  mem_set at h
  rcases h with h|h|h
  rw [h] ; assumption
  rw [h] ; assumption
  rw [h] ; assumption
  contradiction

  have BKnight : B ∈ Knight
  rw [stB]
  right ; right ; assumption
  contradiction

  have oneKnight := stB.mp BKnight
  rcases oneKnight with singleton|singleton|singleton
  have AKnight : A ∈ Knight
  rw [singleton] ; is_mem
  contradiction

  have CKnave : C ∈ Knave
  set_knave_to_knight
  intro CKnight
  rw [singleton] at CKnight
  mem_set at CKnight
  symm at CKnight ; contradiction
  constructor ; assumption
  constructor ; assumption ; assumption

  rw [singleton] at BKnight
  mem_set at BKnight ; contradiction

#check Finset.singleton_subset_iff
#check Finset.singleton_subset_singleton
#check Finset.singleton_subset_set_iff

example
  {inst : DecidableEq Inhabitant}
  {all : ∀(x : Inhabitant), x = A ∨ x = B ∨ x = C}
{h : Knight ∩ Knave = ∅ }
  {Or : ∀(x:Inhabitant), x ∈ Knave ∨ x ∈ Knight}
{h1 : A ∈ Knight ∨ A ∈ Knave }
{h2: B ∈ Knight ∨ B ∈ Knave }
{h3: C ∈ Knight ∨ C ∈ Knave }
{stA : A ∈ Knight  ↔ (Knave={A,B,C}) }
{stAn : A ∈ Knave ↔ ¬ (Knave={A,B,C}) }
{stB: B ∈ Knight ↔ (Knight = {A} ∨ Knight = {B} ∨ Knight = {C}) }
{stBn: B ∈ Knave ↔ ¬ (Knight = {A} ∨ Knight = {B} ∨ Knight = {C}) }
  :

  A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave
  := by
  -- also similar to I am a Knave
  have AKnave : A ∈ Knave := by
    by_contra AKnight
    rw [notinright_inleftIff] at AKnight
    have everyoneknave := stA.mp AKnight  
    have AKnave: A ∈ Knave := by rw [everyoneknave] ; apply Finset.mem_insert_self
    contradiction
  have notallknave := stAn.mp AKnave
  have AnKnight: Knight ≠ {A} := by 
    intro KnighteqA 
    have := mem_of_eq_singleton KnighteqA 
    contradiction
  simp [AnKnight] at stB
  have BKnight2 : B ∈ Knight := by 
    by_contra BKnave 
    rw [notinleft_inrightIff] at BKnave 
    have CnKnave : C ∉ Knave := by 
      intro CKnave 
      have : Knave = {A,B,C} := by 
        #check everyone_in_set_eq
        exact (everyone_in_set_eq all).mp ⟨AKnave,BKnave ,CKnave⟩
      contradiction 
    -- so Knight = {C} so B knight, contradiction 
    sorry
  have BKnight : B ∈ Knight := by 
    by_contra BKnave
    rw [notinleft_inrightIff] at BKnave
    have notoneknight := stBn.mp BKnave
    push_neg at notoneknight
    -- by stAn, C is a knight because otherwise Knave={A,B,C}. then knight={C} contradiction
    -- since ¬Knave={A,B,C} then Knight is not empty. If C knave, then knight empty or then Knave={A,B,C} contradition. So C not knave, i.e C Knight but if C Knight then Knight ={C} contradiction
    #check Finset.univ
    #check all2_in_one_other_empty
    #check all3_in_one_other_empty
    #check all3_in_one_other_eq_all
    #check two_in_one_other_nonemp 
    --rw [or_comm] at Or
    have S'nonemp := two_in_one_other_nonemp all Or AKnave BKnave notallknave
    #check set_subset_univ
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
          show_term contradiction
          exact disjoint xKnight AKnave
        · rcases h_2 with h_3|h_4
          · rw [h_3] at xKnight
            exfalso
            exact disjoint xKnight BKnave
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
  rw [inright_notinleftIff] at AKnave
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
    apply Finset.ext
    intro a
    constructor
    · intro ainS
      apply (mem_iff_or_finset).mpr
      exact all a

      --cases all a
      ---- make thm first_mem, second_mem third_mem, this is a repeated pattern of reasoning
      --· rw [h]
      --  apply Finset.mem_insert_self
      --· sorry
    · exact fun _ => this a
  contradiction
