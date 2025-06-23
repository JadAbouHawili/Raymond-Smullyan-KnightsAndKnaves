import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic.Have

/-
wolfram generated
A ⇔ (¬C ∧ B)
B ⇔ (C ⇔ A)
A: C is a knave and B is a knight.
B: C is a knight, if and only if A is a knight.
-/
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

theorem PQiff{P Q : Prop} (hP : P) ( hQ : Q )
: ¬P ↔ ¬Q := by 

  rw [not_iff_not]
  exact iff_of_true hP hQ 
  --exact (iff_false_right fun a ↦ a hQ).mpr fun a ↦ a hP

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
    simp [_root_.not_imp] at CB 
    have cont := stB.mp CB.right
    simp [nA] at cont
    exact CB.left cont

  have : ¬ A → C := by simp [hA] 
  have hB :=  stB.mpr this 
  simp [hA,hB] at stA
  exact ⟨hA,hB,stA⟩ 

--A ⇔ (B ∧ ¬C)
--B ⇔ (¬C ⇔ ¬A)
example {A B C : Prop}
{stA : A ↔ (B ∧ ¬C)}
{stAn : ¬A ↔ ¬(B ∧ ¬C)}
{stB : B ↔ (¬C ↔ ¬A)}
{stBn : ¬B ↔ ¬(¬C ↔ ¬A)}
: ¬A ∧ ¬B ∧ C := by
  rw [stB] at stA
  have : ((¬C ↔ ¬A) ∧ ¬C) → ¬A := by 
    intro ⟨ACiff,nC⟩
    rw [ACiff] at nC
    assumption
  have : A → ¬A  :=  by
    trans 
    exact stA.mp 
    exact this
  #check imp_not_self
  have nA : ¬A := by
   intro a 
   exact (this a) a

  have BC := stAn.mp nA
  rw [not_and_or] at BC
  simp at BC

  rcases BC with nB | hC
  simp [nA,nB] at stBn 
  exact ⟨nA,nB,stBn⟩ 
  simp [nA,hC] at stBn
  exact ⟨nA,stBn,hC⟩ 

/-
sat( (A =:= (C + ~B))  * ( B =:= (A =:= ~C) )  ), labeling([A,B,C]) .

101
A = C, C = 1,
B = 0.

-/

example {A B C : Prop}
{stA : A ↔ (¬C → ¬B)}
{stAn : ¬A ↔ ¬(¬C → ¬B)}
{stB : B ↔ (A ↔ ¬C)}
{stBn : ¬B ↔ ¬(A ↔ ¬C)}
: A ∧ ¬B ∧ C := by 
    #check imp_iff_or_not
    simp [imp_iff_or_not] at *

    have hA : A 
    by_contra nA
    have BC := stAn.mp nA
    have AdiffC := stB.mp BC.left
    have AsameC : A ↔ C := by 
      exact iff_of_false nA BC.right
    #check not_iff
    #check neq_of_not_iff
    simp [not_iff.symm] at AdiffC
    rw [not_iff_not.symm] at AdiffC
    simp at AdiffC
    have notAsameC := not_iff.mpr AdiffC
    contradiction

    have BC := stA.mp hA
    rcases BC with nB | hC
    simp [nB,hA] at stBn
    exact ⟨hA,nB,stBn⟩ 
    simp [hA,hC] at stBn 
    exact ⟨hA,stBn,hC⟩ 
