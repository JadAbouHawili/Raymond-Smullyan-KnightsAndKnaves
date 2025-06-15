import SmullyanKnightsAndKnaves.knightsknaves
import SmullyanKnightsAndKnaves.dsl_knights_knaves
-- https://philosophy.hku.hk/think/logic/knights.php
--Puzzle #201 out of 382
--
--A very special island is inhabited only by knights and knaves. Knights always tell the truth, and knaves always lie.
--
--You meet six inhabitants: Joe, Bob, Ted, Zippy, Alice and Zoey. Joe claims, “At least one of the following is true: that I am a knight or that Alice is a knave.” Bob says, “I could say that Zippy is a knight.” Ted tells you that Zippy is a knight and Alice is a knave. Zippy says that it's false that Bob is a knave. Alice tells you, “Either Zippy is a knave or Zoey is a knight.” Zoey tells you that it's not the case that Joe is a knave.
--
--Can you determine who is a knight and who is a knave?

--axiom
/-
prolog 
sat( (Joe =:= (Joe + ~Alice)) * (Bob =:= (Zippy)) * (Ted =:= (Zippy * ~Alice) * (Zippy =:= Bob)) * (Alice =:= (~Zippy + Zoey)) * (Zoey =:= Joe) ), labeling([Joe,Alice,Bob,Zippy,Zoey,Ted]).

Joe = Bob, Bob = Zippy, Zippy = Ted, Ted = Zoey, Zoey = 0,
Alice = 1 .

-/
#check inleft_notinright
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

--You have met a group of 3 islanders. Their names are Oberon, Tracy, and Wendy.
--
--    Tracy says: Wendy is untruthful.
--    Oberon says: Tracy is a knight and I am a knave.
--    Wendy says: Oberon is a knave.  Solution :     Because Oberon said 'Tracy is a knight and I am a knave,' we know Oberon is not making a true statement. (If it was true, the speaker would be a knight claiming to be a knave, which cannot happen.) Therefore, Oberon is a knave and Tracy is a knave.
--    All islanders will call a member of the opposite type a knave. So when Tracy says that Wendy is a knave, we know that Wendy and Tracy are opposite types. Since Tracy is a knave, then Wendy is a knight.
--For these reasons we know the knaves were Tracy and Oberon, and the only knight was Wendy.

example
  {Inhabitant : Type}
  {Tracy Oberon Wendy: Inhabitant}
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{Or : ∀(x :Inhabitant), x ∈ Knight ∨ x ∈ Knave}
{stT : Tracy ∈ Knight  ↔ (Wendy ∈ Knave) }
{stTn : Tracy ∈ Knave  ↔ ¬(Wendy ∈ Knave) }
{stO: Oberon ∈ Knight ↔ (Tracy ∈ Knight ∧ Oberon ∈ Knave) }
{stOn: Oberon ∈ Knave ↔ ¬(Tracy ∈ Knight ∧ Oberon ∈ Knave) }
{stW : Wendy ∈ Knight ↔ Oberon ∈ Knave}
{stWn : Wendy ∈ Knave ↔ ¬ (Oberon ∈ Knave)}
  : Tracy ∈ Knave ∧ Oberon ∈ Knave ∧ Wendy ∈ Knight := by
  {
    have OberonKnave : Oberon ∈ Knave := by {
      by_contra OberonKnight
      rw [notinright_inleftIff (Or Oberon) h] at OberonKnight
      have := stO.mp OberonKnight
      exact disjoint h OberonKnight this.right
    }
    have WendyKnight := stW.mpr OberonKnave
    have TracyKnave : Tracy ∈ Knave := by {
      rw [inleft_notinrightIff (Or Wendy) h] at WendyKnight
      exact stTn.mpr WendyKnight 
    }

    constructor
    assumption
    constructor
    assumption
    assumption

  }

------------------
-- inverse direction is obvious...
example {K : Type} (A : Finset K) (ge1 : A.card ≥ 1) : ∃ a:K, {a} ⊆ A := by 
  --rw [] at ge1 
  --by_contra h
  --push_neg at h
  have := gt_or_eq_of_le ge1
  rcases this with h|h
  · --#check Finset.card_le_of_subset 
    #check Finset.subset_iff_eq_of_card_le
    sorry
  · rw [Finset.card_eq_one] at h
    have ⟨a,ha⟩ := h
    use a
    rw [ha]

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
  sorry

/-
A: B* ⇔ C
B: A ∧ C
C: A*  B*

A: B is a knave, if and only if C is a knight.
B: A is a knight and C is a knight.
C: If A is a knave, then B is a knave.
-/
example
  {Inhabitant : Type}
  {A B C : Inhabitant}
  {inst : DecidableEq Inhabitant}
  {inst2 : Fintype Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
  {Normal : Finset Inhabitant} 
{hKKn : Knight ∩ Knave = ∅ }
{hKN : Knight ∩ Normal = ∅ }
{hKnN : Knave ∩ Normal = ∅ }
{all2 : ∀ (x : Inhabitant), x = A ∨ x = B ∨ x = C}
{Or : ∀(x :Inhabitant), x ∈ Knight ∨ x ∈ Knave ∨ x ∈ Normal}
{stA : A ∈ Knight → (B ∈ Knave ↔ C ∈ Knight) }
{stAn : A ∈ Knave → ¬ (B ∈ Knave ↔ C ∈ Knight) }

{stB: B ∈ Knight → (A ∈ Knight ∧  C ∈ Knight) }
{stBn: B ∈ Knave → ¬ (A ∈ Knight ∧  C ∈ Knight) }

{stC: C ∈ Knight → (A ∈ Knave → B ∈ Knave) }
{stCn: C ∈ Knave → ¬ (A ∈ Knave → B ∈ Knave) }
{atleastK : Knight.card ≥ 1}
{atleastKn : Knave.card ≥ 1} : A ∈ Normal ∧ B ∈ Knave ∧ C ∈ Knight := by 
  -- B ∉ Knight
  sorry

example
{K : Type}
{x y : K} {inst : DecidableEq K}
  (Knight : Finset K ) (Knave : Finset K)
  (h : Knight ∩ Knave = ∅ ) (h1 : x ∈ Knight ∨ x ∈ Knave) (h2 : y ∈ Knight ∨ y ∈ Knave) 

  -- x says y is a knight
  -- y says that x and y are of different type
  (stx : x ∈ Knight ↔ y ∈ Knight)
  (sty : y ∈ Knight ↔ (y ∈ Knight ∧ x ∈ Knave) ∨ (y ∈ Knave ∧ x ∈ Knight ) )
  (styn : y ∈ Knave ↔ ¬( (y ∈ Knight ∧ x ∈ Knave) ∨ (y ∈ Knave ∧ x ∈ Knight )) )
  --(styn : y ∈ Knave ↔ x ∉ Knave ∨ y ∉ Knight)
  : x ∈ Knave ∧ y ∈ Knave := by
    rw [not_or] at styn
    rw [not_and_or] at styn
    rw [not_and_or] at styn
    -- assuming x knight, we get y knight, then we get x and y are different type which is contradiction. so x knave which means y not knight i.e y knave. 

    sorry

example
  {K : Type}
  {x y : K}
  {inst : DecidableEq K}
  (Knight : Finset K ) (Knave : Finset K)
  (h : Knight ∩ Knave = ∅ ) (h1 : x ∈ Knight ∨ x ∈ Knave) (h2 : y ∈ Knight ∨ y ∈ Knave)
  -- x says y is a knight
  -- y says that x and y are of different type
  (stx : x ∈ Knight ↔ y ∈ Knight)
  (sty : y ∈ Knight ↔ x ∈ Knight ∧ y ∈ Knave ∨ x ∈ Knave ∧ y ∈ Knight)
  : x ∈ Knave ∧ y ∈ Knave := by
  #check IfToIff

  rw [not_iff_not.symm] at stx

  rw [notinleft_inrightIff h1 h] at stx
  rw [notinleft_inrightIff  h2 h] at stx
  rw [stx]
  simp 

  have this:=h2

  rcases h2  with h_1|h_1
  rw [sty] at h_1 
  rw [stx] at h_1
  nth_rw 1 [stx.symm] at h_1
  rw [inright_notinleftIff h1 h]  at h_1
  rw [inright_notinleftIff this h]  at h_1
  rcases h_1 with ⟨a,b⟩|⟨a',b'⟩
  contradiction
  contradiction

  assumption
