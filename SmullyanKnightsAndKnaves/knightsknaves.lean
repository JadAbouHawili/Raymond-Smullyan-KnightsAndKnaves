import SmullyanKnightsAndKnaves.knightsknaves_foundation

inductive Inhabitant
| A
| B
deriving DecidableEq , Fintype

-- redundant/not needed , keep
theorem all : ∀x : Inhabitant , x = .A ∨ x = .B := by
  intro x
  cases x <;> aesop

macro "by_universe" : tactic =>
  `(tactic| (apply set_subset_univ2 ; intro x ; exact all x))

open Inhabitant
#check Finset.eq_univ_iff_forall
#check Finset.eq_univ_of_forall

-- might be useful...
example
: ({A,B} : Finset Inhabitant) = Finset.univ   ↔  ∀ (x : Inhabitant), x = A ∨ x = B := by
  exact Iff.trans Finset.eq_univ_iff_forall (by simp)

-- might be useful , more general
-- but generality doesn't matter in this context because i have inhabitant with 2 elms and 3 elems
example 
{K : Type}
{inst : Fintype K} {inst2 : DecidableEq K} {A B : K}   : Finset.univ = ({A,B} : Finset K) ↔  ∀ (x : K), x = A ∨ x = B := by
    rw [eq_comm]
    simp [Finset.eq_univ_iff_forall]


#check Finset.eq_univ_iff_forall
-- generalization , could then be used for knightsknaves and knightsknaves_3 ... if need be
example
{K : Type}
{inst : Fintype K} {inst2 : DecidableEq K} {A: K} {S : Finset K}  : Finset.univ = (insert A S: Finset K) ↔  ∀ (x : K), x = A ∨ x ∈ S := by
  simp [Finset.ext_iff,Finset.mem_univ]



#check Finset.eq_univ_iff_forall
#check Finset.eq_of_subset_of_card_le

variable {α : Type}
variable [Fintype α] {s t : Finset α}


-- call these Knight internal then do local notation
namespace hidden
axiom Knight : Finset Inhabitant
axiom Knave : Finset Inhabitant

axiom  KorKn : ∀ x : Inhabitant, x ∈ Knight ∨ x ∈ Knave
axiom dis : Knight ∩ Knave = ∅

theorem asdf : Knight ∪ Knave = (Finset.univ) := by 
  apply Finset.Subset.antisymm 

  simp

  intro x _
  simp ; exact KorKn x
end hidden

noncomputable instance world : World Inhabitant :=  by
  exact ⟨hidden.Knight,
  hidden.Knave,
  hidden.dis,
  hidden.KorKn⟩

macro_rules
| `(tactic| contradiction) =>
  do `(tactic |solve  | ( exfalso ; apply @disjoint Inhabitant  ; repeat assumption) )
