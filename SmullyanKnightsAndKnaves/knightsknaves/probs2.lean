import SmullyanKnightsAndKnaves.knightsknaves

/-
wolfram generated
A ⇔ (¬C ∧ B)
B ⇔ (C ⇔ A)
A: C is a knave and B is a knight.
B: C is a knight, if and only if A is a knight.
-/
import Mathlib.Tactic.Have
import SmullyanKnightsAndKnaves.settheory
example {P Q : Prop} (h : ¬(P ∧ Q)) : ¬P ∨ ¬Q := by 
  exact?


  #check Classical.not_and_iff_or_not_not
  #check not_and
  #check or_iff_right_of_imp
  #check not_and_of_not_or_not
  #check not_or
example {A B C : Prop}
{stA : A ↔ (¬C ∧ B)}
{stAn : ¬A ↔ ¬(¬C ∧ B)}
{stB : B ↔ (C ↔ A)}
{stBn : ¬B ↔ ¬(C ↔ A)}
: ¬A ∧ ¬B ∧ C := by 
  have nA : ¬A := by 
    intro hA 
    have ⟨nC,hB⟩ := stA.mp hA  
    have CiffA := stB.mp hB
    rw [CiffA] at nC
    contradiction
  have CorB := stAn.mp nA 
  --#check not_and
  --rw [not_and.symm] at CorB
  rw [Classical.not_and_iff_or_not_not] at CorB
  simp at CorB
  have nB : ¬B := by 
    intro hB 
    have CiffA := stB.mp hB
    simp [hB] at CorB
    rw [CiffA] at CorB 
    contradiction
  have hC : C := by 
    have CA_not_same := stBn.mp nB
    have := neq_of_not_iff CA_not_same
    have what : (¬¬C) 
    intro nC 
    have this2: C ↔ A := by 
      exact (iff_false_right nA).mpr nC
      --exact (iff_true_right nA).mpr nC
    rw [this2] at this
    contradiction
    simp at what
    assumption
   -- #check not_iff 
    --rw [CA_not_same.symm] at nA 
    --simp at nA
    --assumption

  exact ⟨nA,nB,hC⟩ 
#check iff_iff_eq
#check iff_true_right
#check Int.sign_eq_neg_one_iff_neg
--https://philosophy.hku.hk/think/logic/knights.php
-- translation of this puzzle is tricky
--Here is your puzzle:
--
--You have met a group of 3 islanders. Their names are Xavier, Gary, and Alice.
--    Gary says: Alice is my type.   Alice says: Gary never lies.    Gary says: Xavier never lies.
--example
--{Gary Xavier Alice : Prop}
--{stG : Gary ↔ Alice}
--{stA : Alice ↔ Gary}
--{stG2 : Gary ↔ Xavier}

--solution:    A knight or a knave will say they are the same type as a knight. So when Gary says they are the same type as Alice, we know that Alice is a knight.
--    All islanders will call one of their same kind a knight. So when Alice says that Gary is a knight, we know that Gary and Alice are the same type. Since Alice is a knight, then Gary is a knight.
--    All islanders will call one of their same kind a knight. So when Gary says that Xavier is a knight, we know that Xavier and Gary are the same type. Since Gary is a knight, then Xavier is a knight.
--
--For these reasons we know there were no knaves , and the knights were Alice, Xavier, and Gary.
example
  {Inhabitant : Type}
  {Gary Alice Xavier: Inhabitant}
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{Or : ∀(x :Inhabitant), x ∈ Knight ∨ x ∈ Knave}
{stG1 : Gary ∈ Knight  ↔ (Alice ∈ Knight) }
{stGn1 : Gary ∈ Knave  ↔ (Alice ∈ Knight) }
{stG2 : Gary ∈ Knight  ↔ (Xavier ∈ Knight) }
{stGn2 : Gary ∈ Knave  ↔ (Xavier ∈ Knave) }
{stA : Alice ∈ Knight ↔ (Gary ∈ Knight)}
{stAn : Alice ∈ Knave ↔ (Gary ∈ Knave)} : Gary ∈ Knight ∧ Alice ∈ Knight ∧ Xavier ∈ Knight := by{
  rcases Or Gary with GaryKnight|GaryKnave
  · have AliceKnight:= stG1.mp GaryKnight
    have XavierKnight := stG2.mp GaryKnight
    constructor
    assumption
    constructor
    assumption
    assumption

  · have AliceKnight := stGn1.mp GaryKnave
    have GaryKnight := stA.mp AliceKnight
    exfalso
    exact disjoint h GaryKnight GaryKnave
}

-- tough translation
--https://philosophy.hku.hk/think/logic/knights.php
--Here is your puzzle:
--
--You have met a group of 2 islanders. Their names are Robert and Ira.
--
--    Robert says: Ira is my type.
--    Ira says: Robert is truthful.
--solution:     A knight or a knave will say they are the same type as a knight. So when Robert says they are the same type as Ira, we know that Ira is a knight.
--    All islanders will call one of their same kind a knight. So when Ira says that Robert is a knight, we know that Robert and Ira are the same type. Since Ira is a knight, then Robert is a knight.
--
--For these reasons we know there were no knaves , and the knights were Robert and Ira.
--example
--{Robert Ira : Prop}
example
  {Robert Ira: Inhabitant}
  {Knight : Set Inhabitant} 
  {Knave : Set Inhabitant}
  {h : Knight ∩ Knave = ∅ }
  {Or : ∀(x :Inhabitant), x ∈ Knight ∨ x ∈ Knave}
  {stR : Robert ∈ Knight ↔ Ira ∈ Knight}
  {stRn : Robert ∈ Knave ↔ Ira ∈ Knight}
  {stI : Ira ∈ Knight ↔ Robert ∈ Knight}
  {stIn : Ira ∈ Knave ↔ Robert ∈ Knave} : Robert ∈ Knight ∧ Ira ∈ Knight := by 
    have IraKnight : Ira ∈ Knight := by 
      cases Or Robert
      · exact stR.mp h_1
      · exact stRn.mp h_1
    constructor
    · exact stI.mp IraKnight
    · assumption


--A ⇔ (¬C  ¬B)
--B ⇔ (¬A  C)
--A: If C is a knave, then B is a knave.
--B: If A is a knave, then C is a knight.
-- translate implications to or,and expressions
example {A B C : Prop}
{stA : A ↔ (¬C → ¬B)}
{stAn : ¬A ↔ ¬(¬C → ¬B)}
{stB : B ↔ (¬A → C)}
{stBn : ¬B ↔ ¬(¬A → C)}
: A ∧ B ∧ C := by 

  have hA : A := by 
    by_contra nA
    have CB := stAn.mp nA 
    simp [not_imp] at CB 
    have cont := stB.mp CB.right
    simp [nA] at cont
    exact CB.left cont

  have : ¬ A → C := by simp [hA] 
  have hB :=  stB.mpr this 
  simp [hA,hB] at stA
  --done
  sorry

--A ⇔ (B ∧ ¬C)
--B ⇔ (¬C ⇔ ¬A)
example {A B C : Prop}
{stA : A ↔ (B ∧ ¬C)}
{stAn : ¬A ↔ ¬(B ∧ ¬C)}
{stB : B ↔ (¬C ↔ ¬A)}
{stBn : ¬B ↔ ¬(¬C ↔ ¬A)}
: False := by
-- getting nA
  rw [stB] at stA
  have : ((¬C ↔ ¬A) ∧ ¬C) → ¬A := by 
    intro ⟨ACiff,nC⟩
    rw [ACiff] at nC
    assumption
  have := Implies.trans stA.mp this
  #check imp_not_self
  have nA : ¬A := by
   intro a 
   exact (this a) a

  have BC := stAn.mp nA
  rw [not_and_or] at BC
  simp at BC
  -- do cases then done.. ez, but similar to other levels. want to reason with implications and not or,and expressions.
  sorry

-- cant solve idk why
example {A B C : Prop}
{stA : A ↔ (¬C → ¬B)}
{stAn : ¬A ↔ ¬(¬C → ¬B)}
{stB : B ↔ (A ↔ ¬C)}
{stBn : ¬B ↔ ¬(A ↔ ¬C)}
: False := by 
  have hB : B := by 
    by_contra nB
    have AsameC := stBn.mp nB 
    rw [not_iff] at AsameC 
    have stAn2 := stAn
    rw [AsameC] at stAn2
    rw [not_imp] at stAn2
    simp at stAn2

    have hC := Function.mt stAn2 nB
    simp at hC 
    have hA := (not_iff_not.mp AsameC).mpr hC 
    simp [hA,nB,hC] at * 
    sorry
  have nB : ¬B := by 
    intro hB
    have AdiffC := stB.mp hB 
    rw [AdiffC] at stA
    have := stA.mp 
    #check and_imp
    rw [and_imp.symm] at this
    simp at this
    have := (Function.mt this)
    simp at this
    have hC := this hB

    sorry
  sorry
