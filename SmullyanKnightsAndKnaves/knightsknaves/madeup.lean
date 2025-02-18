-- file which contains knights and knaves problems we made up.

import SmullyanKnightsAndKnaves.knightsknaves
/-
"
A : All of us are knights
B: Exactly one of us is a knave
"
-/
variable {Inhabitant : Type}
variable { A B : Inhabitant}

example
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{all2 : ∀ (x : Inhabitant), x = A ∨ x = B}
{Or : ∀(x :Inhabitant), x ∈ Knight ∨ x ∈ Knave}
{stA : A ∈ Knight ↔ (Knight={A,B}) }
{stAn : A ∈ Knave ↔ ¬ (Knight={A,B}) }
{stB: B ∈ Knight ↔  (Knave={A} ∨ Knave={B}) }
{stBn: B ∈ Knave ↔  ¬ (Knave={A} ∨ Knave={B}) }
  : A∈ Knave := by

  {
    rcases Or B with BKnight|BKnave
    · have oneknave := stB.mp BKnight 
      rcases oneknave with KA|KB
      · exact mem_of_eq_singleton KA
      · #check mem_of_eq_singleton  
        have BKnave := mem_of_eq_singleton KB
        exfalso
        exact disjoint h BKnight BKnave
    · by_contra AKnight 
      rw [notinright_inleftIff (Or A) h] at AKnight
      have KAB := stA.mp AKnight 
--      #check Finset.eq_of_not_mem_of_mem_insert
      #check Finset.erase_eq_iff_eq_insert
      #check Finset.insert_eq 
      -- Knight = {A,B} ∧ all ↔ A ∈ Knight ∧ B ∈ Knight 
      -- Knight = {A,B} → A ∈ Knight ∧ B ∈ Knight

      have : Knight={A,B} → B ∈ Knight := by 
        intro h'
        rw [h']
        exact mem2_iff_or_finset.mpr (all2 B)

      #check Finset.insert_eq_of_mem 
      have BKnight := this KAB
      exact disjoint h BKnight BKnave
  }

-- given a proof of p, goal is changed to ¬p
--absurd

-- instead of having h1 : A ∈ Knight ∨ A ∈ Knave clogging the assumption, just have a tactic person_cases A that does it(uses obtain)

-- A says I am a knave or B is a knave
example {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
--{all2 : ∀ (x : Inhabitant), x = A ∨ x = B}
--{Or : ∀(x :Inhabitant), x ∈ Knight ∨ x ∈ Knave}
{stA : A ∈ Knight ↔ (A ∈ Knave ∨ B ∈ Knave) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∨ B ∈ Knave) }
 : 2=2 := by sorry



/-
formalization
{stA : A ∈ Knight ↔ (B ∈ Knight) }
{stAn : A ∈ Knave ↔ ¬ (B ∈ Knight) }

here, stAn is redundant. theres a theorem that would you this by doing not both sides of iff of stA.

put here so user doesn't have to do that
-/
/-
A says B is a knight
B says all of us are knights
C says A  is a kngiht or B is a knight
-/
example 
{C :Inhabitant}
{inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{Or : ∀(x :Inhabitant), x ∈ Knight ∨ x ∈ Knave}
{stA : A ∈ Knight ↔ (B ∈ Knight) }
{stAn : A ∈ Knave ↔ ¬ (B ∈ Knight) }
{stB : B ∈ Knight ↔ A ∈ Knight ∧ B ∈ Knight ∧ C ∈ Knight}
{stBn : B ∈ Knave ↔ ¬ (A ∈ Knight ∧ B ∈ Knight ∧ C ∈ Knight)}
{stC : C ∈ Knight ↔ A ∈ Knight ∨ B ∈ Knight}
{stCn : C ∈ Knave ↔ ¬ (A ∈ Knight ∨ B ∈ Knight)}
: A ∈ Knight ∧ B ∈ Knight ∧ C ∈ Knight ∨ A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave:= by 
  have stB2 := stB
  nth_rw 1 [stA.symm] at stB2 

  rcases Or A with h_1|h_2
  · left 
    exact stB2.mp h_1
  · have BnKnight := stAn.mp h_2
    simp [BnKnight] at stCn
    have AKnave := h_2
    rw [inright_notinleftIff (Or A) h] at h_2
    have CKnave := stCn.mpr h_2
    right
    rw [notinleft_inrightIff (Or B) h] at BnKnight
    exact And.intro AKnave (And.intro BnKnight CKnave)

