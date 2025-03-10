import SmullyanKnightsAndKnaves.knightsknaves
import SmullyanKnightsAndKnaves.dsl_knights_knaves
-- generated by https://www.wolframcloud.com/objects/demonstrations/KnightsKnavesAndNormalsPuzzleGenerator-source.nb

/-
A: B is a knave, if and only if C is a knave.
B: If A is a knave, then C is a knave.
C: A is a knave or B is a knight.
-/
-- didnt consider normal, does it matter in this case tho???
#check Islander
open Islander
example 
{A B C : Islander}
{stA : A said (B.isKnave ↔ C.isKnave)}
{stB : B said (A.isKnave → C.isKnave)}
{stC : C said (A.isKnave or B.isKnight)}
{atleastKnight : A.isKnight or B.isKnight or C.isKnight}
{atleastKnave : A.isKnave or B.isKnave or C.isKnave}
: A.isKnave and B.isKnave and C.isKnight := by 
  knight_to_knave at *

  have AKnave : A.isKnave 
  apply notisKnight_isKnave
  intro AKnight
  have AnKnave := isKnight_notisKnave AKnight
  simp [AnKnave] at stC
  simp [AnKnave] at stB 
  #check said_knight
  have BKnight := said_knight stB trivial
  have Asaid := knight_said stA AKnight
  have CKnight := said_knight stC BKnight
  --apply isKnave_notisKnight atleastKnave
  #check isKnight_notisKnaveIff
  knave_to_knight atleastKnave
  simp [AKnight,BKnight,CKnight] at atleastKnave

  have CKnight := said_knight stC (by left ; assumption)
  have BCdiff := knave_said stA AKnave 
  simp [isKnight_notisKnave CKnight] at BCdiff

  constructor <;> try constructor
  repeat assumption

-- more complicated
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
{stA : A ∈ Knight → (B ∈ Knave ↔ C ∈ Knave) }
{stAn : A ∈ Knave → ¬ (B ∈ Knave ↔ C ∈ Knave) }

{stB: B ∈ Knight → (A ∈ Knave → C ∈ Knave) }
{stBn: B ∈ Knave → ¬ (A ∈ Knave → C ∈ Knave) }

{stC: C ∈ Knight → (A ∈ Knave ∨ B ∈ Knight) }
{stCn: C ∈ Knave → ¬ (A ∈ Knave ∨ B ∈ Knight) }
{atleastK : Knight.card ≥ 1}
{atleastKn : Knave.card ≥ 1}
  : A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight := by
  {
    have U : Finset.univ = {A,B,C} := (univ_iff_all).mpr all2

    have KU: Knight ⊆ {A,B,C} := by 
        --apply set_subset_univ
        --exact inst2
        --exact fun x ↦ all2 x
        rw [←U]
        exact Finset.subset_univ Knight

    have KnU: Knave ⊆ {A,B,C} := by
        rw [←U]
        exact Finset.subset_univ Knave
    have CnKnave : C ∉ Knave := by {
      intro CKnave
      have notor := stCn CKnave 
      push_neg at notor
      -- its forced that A ∈ Knight
      -- how to get this.... 
      -- assuming A is not a knight then knight is empty, contradiction
      #check univ_iff_all

      have AKnight : A ∈ Knight := by {
        by_contra AnKnight 
        #check Finset.subset_insert_iff_of_not_mem 
        rw [Finset.subset_insert_iff_of_not_mem AnKnight] at KU

        rw [Finset.subset_insert_iff_of_not_mem notor.right] at KU
        have CnKnight := inright_notinleft hKKn CKnave
        #check Finset.subset_insert_iff_of_not_mem
        #check Finset.subset_singleton_iff
        rw [Finset.subset_singleton_iff] at KU
        -- thm here
        have Knigthemp : Knight = ∅ := by{ 
          rcases KU with h|h
          assumption
          #check mem_of_eq_singleton 
          exfalso
          exact CnKnight (mem_of_eq_singleton h)
        }
        rw [Knigthemp] at atleastK 
        contradiction

      }
      have BiffC := stA AKnight
      rw [BiffC] at stBn
      have cont := stBn CKnave
      #check implies_true
      have : A ∈ Knave → C ∈ Knave := by 
        exact fun _ => CKnave
      contradiction

--        rw [Finset.subset_insert_iff_of_not_mem CnKnight] at KU

      -- Finset.card_ge_one ∃ a , {a} ⊆ A
  }
    have AnKnight : A ∉ Knight := by 
      intro AKnight 
      have BiffC := stA AKnight
      have BnKnave := (not_iff_not.mpr BiffC ).mpr CnKnave
      -- knave empty, similar to previous reasoning
      #check Finset.subset_singleton_iff
      #check Finset.subset_insert_iff_of_not_mem 
      have AnKnave:= inleft_notinright hKKn AKnight
      rw [Finset.subset_insert_iff_of_not_mem AnKnave] at KnU
      rw [Finset.subset_insert_iff_of_not_mem BnKnave] at KnU
      rw [Finset.subset_singleton_iff] at KnU
      rcases KnU with h|h
      · rw [h] at atleastKn
        contradiction
      · have := mem_of_eq_singleton h
        contradiction
      --rw [Finset.subset_insert_iff_of_not_mem] at KnU

    have CnNormal : C ∉ Normal := by 
      intro CNormal 
      --- 
      #check gt_or_eq_of_le
      have := gt_or_eq_of_le atleastK
      cases this
      ·  
        rw [Finset.subset_insert_iff_of_not_mem AnKnight ] at KU
        #check Finset.subset_of_eq
        rw [Finset.pair_comm] at KU
        rw [Finset.subset_insert_iff_of_not_mem CnKnight ] at KU
        #check Finset.card_le_of_subset
        have cont := Finset.card_le_of_subset KU
        have := Finset.card_singleton B 
        rw [this] at cont
        #check lt_iff_not_ge
        rw [lt_iff_not_ge] at h
        contradiction

      · rw [Finset.card_eq_one] at h 
        have ⟨a,ha⟩ := h 
        have aKnight := mem_of_eq_singleton ha
        have : a=B := by
          cases all2 a
          · rw [h_1] 
            -- get contradiction
            rw [h_1] at aKnight
            contradiction
          · cases h_1
            · rw [h_2] 
            · have CnKnight := inright_notinleft hKN CNormal
              rw [←h_2] at CnKnight
              contradiction
        rw [this] at aKnight
        have Bconc := stB aKnight
        have AnKnave := Function.mt Bconc CnKnave
        have BnKnave := inleft_notinright hKKn aKnight  
        rw [Finset.subset_insert_iff_of_not_mem AnKnave] at KnU
        rw [Finset.subset_insert_iff_of_not_mem BnKnave] at KnU
        rw [Finset.subset_singleton_iff] at KnU
        cases KnU
        rw [h_1] at atleastKn
        contradiction
        have := mem_of_eq_singleton h_1
        contradiction
        --have ANormal : A ∈ Normal := by
        --  have := Or A
        --  simp [AnKnight, AnKnave] at this
        --  assumption
    have CKnight : C ∈ Knight := by
      have := Or C
      simp [CnKnave,CnNormal] at this
      assumption
    have AKnBK := stC CKnight 
    rcases AKnBK with h|h
    · have BC := stAn h  
      rw [iff_comm] at BC
      rw [not_iff] at BC 
      have BKnave := BC.mp CnKnave
      exact ⟨h,BKnave,CKnight⟩ 
    · have AC := stB h 
      have AnKnave := (Function.mt AC) CnKnave
      have BnKnave := inleft_notinright hKKn h
      rw [Finset.subset_insert_iff_of_not_mem AnKnave] at KnU
      rw [Finset.subset_insert_iff_of_not_mem BnKnave] at KnU
      rw [Finset.subset_singleton_iff] at KnU
      rcases KnU with h_1|h_1
      · rw [h_1] at atleastKn
        contradiction
      · have := mem_of_eq_singleton h_1
        contradiction
}
