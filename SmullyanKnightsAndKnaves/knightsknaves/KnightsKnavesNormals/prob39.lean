import SmullyanKnightsAndKnaves.knightsknaves
#check Finset.mem_def
#check Set.toFinset
--#check Finset.instCoeSortFinsetType
-- should be available, #check Finset.instCoeSortType


/-
"
We are given three people, A,B,C, one of whom is a knight, one a knave, and one normal (but not necessarily in that order). 
They make the following statements: 
A: I am normal. 
B: That is true. 
C: I am not normal. 
"
-/

example
{K : Type}
  [inst : DecidableEq K]
  (A B C : K)
  (AneB : A ≠ B)
  (BneC : B ≠ C)
  (AneC : A ≠ C)
  (Knight : Finset K ) 
  (Knave : Finset K)
  {Normal : Finset K}
{OneKnight :  Knight.card =1 }
{OneKnave : Knave.card =1 }
{OneNormal : Normal.card =1 }

{hKKn : Knight ∩ Knave = ∅ }
{hKN : Knight ∩ Normal = ∅ }
{hKnN : Knave ∩ Normal = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave ∨ A ∈ Normal }
{h2 : B ∈ Knight ∨ B ∈ Knave ∨ B ∈ Normal }
{h3 : C ∈ Knight ∨ C ∈ Knave ∨ C ∈ Normal}
{stA : A ∈ Knight → (A ∈ Normal) } 
{stAn : A ∈ Knave → ¬ (A ∈ Normal) }
{stB : B ∈ Knight → (A ∈ Normal)}
{stBn : B ∈ Knave → ¬(A ∈ Normal)}
{stC : C ∈ Knight → C ∉ Normal}
{stCn : C ∈ Knave → C ∈ Normal}
: A ∈ Knave ∧ B ∈ Normal ∧ C ∈ Knight := by 
  /-
  AnKnight, If A were a knight then A would be a normal as well which is a contradiction
  -/ 
  have AnKnight : A ∉ Knight := by 
  {

    by_contra AKnight
    have ANormal := stA AKnight
    -- have to fix this
    --rw [KnightSet] at ANormal


-- disjoint here was Set version but now itsFinset version
    exact disjoint hKN AKnight ANormal
    --exact disjointfinset hKN AKnight ANormal
  }

  have CnKnave : C ∉ Knave := by 
    intro CKnave
    have CNormal := stCn CKnave 
    exact disjoint hKnN CKnave CNormal
   
  -- because AnKnight, then A either knave or normal
  -- AnNormal, if A were normal then BnKnave(maybe make a told the truth thing that would return A knight or normal)
  have AnNormal : A ∉ Normal := by
  {
    by_contra ANormal
    have BnKnave := (Function.mt stBn) (by push_neg; assumption)
    simp [BnKnave] at h2
    have BKnightNormal := h2

    -- helper theorem called full
    have BnNormal : B ∉ Normal := by
    {
      #check One
      exact full ANormal OneNormal AneB
      
      --by_contra BNormal
      --have AeqB:= by exact card_eq OneNormal  ANormal BNormal
      --contradiction
    }

    have BKnight := notleft_right (Or.symm BKnightNormal) BnNormal

    -- since A Normal, B Knight, then C Knave
    have CKnave : C ∈ Knave := by {
      rcases h3 with CKnight|CKnaveNormal
      ·   
        have BeqC := card_eq OneKnight BKnight CKnight
        contradiction
      · rcases CKnaveNormal with CKnave|CNormal
        · assumption
        · have AeqC := card_eq OneNormal ANormal CNormal
          contradiction 
    }

    have CNormal := stCn CKnave
    have AeqC := card_eq OneNormal ANormal CNormal
    contradiction
  }
  have AKnave : A ∈ Knave := by
  {
    simp [AnKnight,AnNormal] at h1
    assumption

  }
  have BnKnight :=  Function.mt stB AnNormal

  have BnKnave := full AKnave OneKnave AneB

  --have := notleft_right h2 BnKnight 
  --have BNormal := notleft_right this BnKnave   
 -- have BNormal := NotKnightKnave_Normal h2 BnKnight BnKnave
   

  -- now C is a knight by a similar reasoning... it is the only option left...
  -- A Knave , B Normal
  have CnKnave := full AKnave OneKnave  AneC
  --have CnNormal := full  BNormal  OneNormal BneC
 -- have := NotKnave_KnightNormal hKKn hKN hKnN  h3 CnKnave


 -- need to re-solve
  sorry
  --have CKnight := NotKnaveNormal_Knight h3 CnKnave CnNormal
  --constructor
  --· assumption
  --· constructor
  --  · assumption
  --  · assumption


example 
  {K : Type}
  [inst : DecidableEq K]
  (A B C : K)
  (AneB : A ≠ B)
  (BneC : B ≠ C)
  (AneC : A ≠ C)
  (Knight : Finset K ) 
  (Knave : Finset K)
  {Normal : Finset K}
{OneKnight :  Knight.card =1 }
{OneKnave : Knave.card =1 }
{OneNormal : Normal.card =1 }

{hKKn : Knight ∩ Knave = ∅ }
{hKN : Knight ∩ Normal = ∅ }
{hKnN : Knave ∩ Normal = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave ∨ A ∈ Normal }
{h2 : B ∈ Knight ∨ B ∈ Knave ∨ B ∈ Normal }
{h3 : C ∈ Knight ∨ C ∈ Knave ∨ C ∈ Normal}
{stA : A ∈ Knight → (A ∈ Normal) } 
{stAn : A ∈ Knave → ¬ (A ∈ Normal) }
{stB : B ∈ Knight → (A ∈ Normal)}
{stBn : B ∈ Knave → ¬(A ∈ Normal)}
{stC : C ∈ Knight → C ∉ Normal}
{stCn : C ∈ Knave → C ∈ Normal}
: A ∈ Knave ∧ B ∈ Normal ∧ C ∈ Knight := by 
   
  sorry
#check Membership
--#check Finset.instMembershipFinset
#check Set.mem_toFinset

