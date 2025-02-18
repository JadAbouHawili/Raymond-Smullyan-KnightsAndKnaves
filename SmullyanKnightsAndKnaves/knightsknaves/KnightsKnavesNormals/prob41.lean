import SmullyanKnightsAndKnaves.knightsknaves
/-
A: B is a knight. 
B: A is a knave, 
-/

variable { K : Type} {A B C : K}

example 
  {inst : DecidableEq K}
--  (A B C : K)
--  (AneB : A ≠ B)
  (Knight : Finset K ) 
  (Knave : Finset K)
  {Normal : Finset K}
--{hK : Finset Knight}
--{hKn : Finset Knave}
--{hN : Finset Normal}
--{finKnight : Fintype Knight}
--{finKnave : Fintype Knave}
--{finNormal : Fintype Normal}
--{OneKnight : Finset.card ( Knight) =1 }
--{OneKnave : Finset.card Knave =1 }
--{OneNormal : Finset.card Normal =1 }

{hKKn : Knight ∩ Knave = ∅ }
{hKN : Knight ∩ Normal = ∅ }
{hKnN : Knave ∩ Normal = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave ∨ A ∈ Normal }
{h2 : B ∈ Knight ∨ B ∈ Knave ∨ B ∈ Normal }
{stA : A ∈ Knight → (B ∈ Knight) } 
{stAn : A ∈ Knave → ¬ (B ∈ Knight) }
{stB : B ∈ Knight → (A ∈ Knave)}
{stBn : B ∈ Knave → ¬(A ∈ Knave)}
: ((A ∉ Knight ∧ B ∈ Knight) ∨ (B ∉ Knight ∧ A ∈ Knave)) ∨ ((A ∉ Knave ∧ B ∉ Knight) ∨ (B ∉ Knave ∧ A ∉ Knave)) := by 
-- the goal is :
-- Prove that either one of them is telling the truth but is not a 
--knight, or one of them is lying but is not a knave. 
-- detail which combination of left right corresponds to what, this oculd be useful from a teaching/explaining perspective
  #check trans
  have BKKn :B ∈ Knight → B∉ Knight := by 
    
    trans
    assumption
    assumption
    --intro Bknight
    --exact  stAn (stB Bknight)
  -- this gives us AnKnight
  have AKKn := Implies.trans stA stB
  have AnKnight :  A ∉ Knight := by 
    intro AKnight
    have AKnave := AKKn AKnight
    exact disjoint hKKn AKnight AKnave

  have BnKnight : B ∉ Knight := by 
    intro h
    have := BKKn h
    contradiction
   
  -- simplify h1 and h2 then do cases
  rcases h1 with AKnight|AKnaveNormal
  · 
    contradiction
  · rcases AKnaveNormal with AKnave|ANormal
    · rcases h2 with BKnight|BKnaveNormal
      · contradiction
      · rcases BKnaveNormal with BKnave|BNormal
        · have := stBn BKnave
          contradiction

        · -- B telling the truth, but is not a knight
          left
          right
          constructor
          · assumption 
          · assumption

-- Prove that either one of them is telling the truth but is not a 
--knight, or one of them is lying but is not a knave. 
    · rcases h2 with BKnight|BKnaveNormal
      · contradiction
      · rcases BKnaveNormal with BKnave|BNormal
        · right
          left
          constructor
            
          · 
            have := inright_notinleft hKnN ANormal
            assumption
          · assumption
        · right
          left
          constructor
            
          · 
            have := inright_notinleft hKnN ANormal
            assumption
          · assumption
  


theorem solution 

  (Knight : Set K ) 
  (Knave : Set K)
  {Normal : Set K}
[inst : Decidable (A ∈ Knight)]
[inst : Decidable (B ∈ Knight)]  {hKKn : Knight ∩ Knave = ∅ }
{hKN : Knight ∩ Normal = ∅ }
{hKnN : Knave ∩ Normal = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave ∨ A ∈ Normal }
{h2 : B ∈ Knight ∨ B ∈ Knave ∨ B ∈ Normal }
{stA : A ∈ Knight → (B ∈ Knight) } 
{stAn : A ∈ Knave → ¬ (B ∈ Knight) }
{stB : B ∈ Knight → (A ∈ Knave)}
{stBn : B ∈ Knave → ¬(A ∈ Knave)}

: ((A ∉ Knight ∧ B ∈ Knight) ∨ (B ∉ Knight ∧ A ∈ Knave)) ∨ ((A ∉ Knave ∧ B ∉ Knight) ∨ (B ∉ Knave ∧ A ∉ Knave)) := by
  
  have  helper1  (hKn : B ∉ Knight)  : A ∉ Knight := 
   by
    intro hAKn
    have contra : B ∈ Knight := (stA hAKn)
    exact hKn contra

  --have helper2  (hK : A ∉ Knight) : B ∉ Knave :=
  --by
  --  intro hBKn
  --  have contra : A ∉ Knave := (stBn hBKn)
  --  sorry
  --  --exact hK contra
  if hAK : A ∈ Knight then 
    if hBK : B ∈ Knight then 
      sorry
      --have hK : A ∉ Knight := helper1 hBK stAn
      --have hKn : B ∉ Knave :=sorry-- helper2 hK stBn
      
      -- A not knight, B knight
      --exact Or.inl (And.intro hK hBK)
    else 
      have hK : A ∉ Knight := helper1 hBK 
      --have hKn : B ∉ Knave := helper2 hK stBn
      --exact Or.inl (And.intro hK hBK)
      have := stA hAK
      contradiction
  else 
    if hAKn : A ∈ Knave then
      if hBKn : B ∈ Knight then 
        --have hK : A ∉ Knight := helper1 hBKn stAn
        --have hKn : B ∉ Knave := helper2 hK stBn
        --exact or.inl (and.intro hK hBKn)
        left
        left
        sorry
      else 
        --have hK : A ∉ Knight := helper1 hBKn stAn
        --have hKn : B ∉ Knave := helper2 hK stBn
        --exact or.inl (and.intro hK hBKn)
        left
        right
        sorry
    else 
      if hAn : A ∈ Normal then 
        have hNAB : A ∉ Knight := sorry
        have hAB : B ∉ Knave := sorry
        sorry
  --      exact or.inr (and.intro hNAB hAB)
      else
        sorry
