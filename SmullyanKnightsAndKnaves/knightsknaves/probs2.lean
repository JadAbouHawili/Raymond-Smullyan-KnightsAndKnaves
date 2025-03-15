import SmullyanKnightsAndKnaves.knightsknaves
import SmullyanKnightsAndKnaves.dsl_knights_knaves

import Mathlib.Tactic.Have
import SmullyanKnightsAndKnaves.settheory
  #check Classical.not_and_iff_or_not_not
  #check not_and
  #check or_iff_right_of_imp
  #check not_and_of_not_or_not
  #check not_or
example {P Q : Prop} : (P ↔ (P ↔ Q)) ↔ (P ↔ Q) := by 
  have : P ↔ (P ↔ Q) := sorry
  have : P ↔ Q := by
      constructor
      intro hP 
      simp [hP] at this 
      assumption

      intro hQ 
      simp [hQ] at this
      sorry
      -- so they are not the same...
  sorry
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

theorem PQiff{P Q : Prop} (hP : P) ( hQ : Q )
: ¬P ↔ ¬Q := by 
  #check iff_false_right
  --rw [(@not_not P).symm] at hP
  --exact (iff_false_right fun a ↦ a hQ).mpr fun a ↦ hP a
  rw [not_iff_not]
  #check iff_of_true
  #check iff_of_false
  --exact iff_of_true hP hQ 
  exact (iff_true_right hQ).mpr hP
  --exact?

    #check not_iff_not



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
  -- do cases then done.. ez, but similar to other levels. want to reason with implications and not or,and expressions.
  sorry

/-
sat( (A =:= (C + ~B))  * ( B =:= (A =:= ~C) )  ), labeling([A,B,C]) .

101
A = C, C = 1,
B = 0.

-/

example {P Q : Prop}
(h : ¬(P ↔ Q))
: P ↔ ¬Q := by  
  #check not_iff
  --exact Iff.symm ((fun {a b} ↦ Classical.not_iff.mp) fun a ↦ h (id (Iff.symm a)))
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

    -- have A ↔ ¬C as AdiffC , having an AsameC as well and running contradiction would close the goal....
    sorry

#check not_imp
#check not_iff_not
#check and_imp
