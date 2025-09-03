import SmullyanKnightsAndKnaves.logic
-- https://philosophy.hku.hk/think/logic/knights.php
--Puzzle #201 out of 382
--
--You meet six inhabitants: Joe, Bob, Ted, Zippy, Alice and Zoey. Joe claims, “At least one of the following is true: that I am a knight or that Alice is a knave.” Bob says, “I could say that Zippy is a knight.” Ted tells you that Zippy is a knight and Alice is a knave. Zippy says that it's false that Bob is a knave. Alice tells you, “Either Zippy is a knave or Zoey is a knight.” Zoey tells you that it's not the case that Joe is a knave.
--
--Can you determine who is a knight and who is a knave?

/-
prolog 
sat( (Joe =:= (Joe + ~Alice)) * (Bob =:= (Zippy)) * (Ted =:= (Zippy * ~Alice) * (Zippy =:= Bob)) * (Alice =:= (~Zippy + Zoey)) * (Zoey =:= Joe) ), labeling([Joe,Alice,Bob,Zippy,Zoey,Ted]).

Joe = Bob, Bob = Zippy, Zippy = Ted, Ted = Zoey, Zoey = 0,
Alice = 1 .
-/
example( Joe Bob Ted Zippy Alice Zoey : Prop)
(Joe_stat:Joe  ↔  Joe ∨ ¬ Alice)
(Bob_stat: Bob  ↔  Zippy)
(Ted_stat: Ted  ↔ ( Zippy ∧ ¬ Alice))
(Zippy_stat: Zippy  ↔  Bob)
(Alice_stat: Alice  ↔  (¬ Zippy ∨ Zoey))
(Zoey_stat: Zoey  ↔ Joe)
:(Alice ∧ ¬Ted)
:= by

  rw [Zoey_stat] at Alice_stat

  rcases em Joe with JoeKnight|JoeKnave
  · rcases em Ted with TedKnight|TedKnave
    · rcases em Alice with AliceKnight|AliceKnave
      · have ⟨a,b⟩ := Ted_stat.mp TedKnight
        contradiction 
      · have := Function.mt (Alice_stat.mpr) AliceKnave
        push_neg at this
        have := this.right
        contradiction
    · rcases em Alice with AliceKnight|AliceKnave
      · 
        constructor
        · assumption
        · assumption

      · 
        have := Function.mt Alice_stat.mpr AliceKnave
        rw [not_or] at this
        have := this.right
        contradiction


  · rcases em Ted with TedKnight|TedKnave
    · rcases em Alice with AliceKnight|AliceKnave
      · have := Ted_stat.mp TedKnight
        have := this.right
        contradiction

      · have := Function.mt Joe_stat.mpr JoeKnave
        push_neg at this
        have := this.right
        contradiction
    · rcases em Alice with AliceKnight|AliceKnave
      · 
        constructor
        assumption
        assumption
      · have := Function.mt Joe_stat.mpr JoeKnave
        push_neg at this
        have := this.right
        contradiction


/-
A: If C is a knave, then B is a knight.
B: A is a knight or C is a knight.
C: B is a knave, if and only if A is a knight.

A: C*  B
B: A ∨ C
C: B* ⇔ A
-/

/-
A,B,C either knight or knave. no normal
A ⇔ (¬B ∧ ¬C)
B ⇔ (A ∨ C)
A: B is a knave and C is a knave.
B: A is a knight or C is a knight.
-/
example {A B C :Prop} 
{stA : A ↔ (¬B ∧ ¬C)}
{stAn : ¬A ↔ ¬(¬B ∧ ¬C)}
{stB : B ↔ (A ∨ C)}
{stBn : ¬B ↔ ¬(A ∨ C)}
: ¬A ∧ B ∧ C := by 
  have nA: ¬A := by
   intro hA 
   have nBnC := stA.mp hA
   have nAnC := stBn.mp nBnC.left
   push_neg at nAnC
   exact nAnC.left hA

  have BC := stAn.mp nA
  have nB : B := by
    by_contra hB
    have nAnC := stBn.mp hB
    push_neg at nAnC
    #check stA.mpr
    have hA := stA.mpr (And.intro hB nAnC.right)
    contradiction

  simp [nA] at stB  
  rw [←stB]
  constructor
  assumption
  constructor
  assumption ; assumption

example
 {A B C P : Prop}
 {h1 : A  ↔ (¬B ∧ ¬C)}
{ h2 : B ↔ (A ∨ C)} 
 {h12 : ¬A  ↔ ¬(¬B ∧ ¬C)}
:  ¬A ∧ B ∧ C := by
 -- have h4 : B ↔ (¬A ∨ ¬C), from h2,
  --rw [h1] at h2
  rw [h2] at h1
  push_neg at h1
  have : ¬A := by 
    intro a
    have := h1.mp a
    exact this.left.left a
  have h2' := h2
  simp [this] at h2
  have : B := by
    by_contra hB
    have nc := (not_iff_not.mpr h2).mp hB
    simp [*] at h1
  -- now i have C
  have hC := h2.mp this

  sorry

