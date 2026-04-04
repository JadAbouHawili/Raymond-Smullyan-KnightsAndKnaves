import SmullyanKnightsAndKnaves.knightsknaves_foundation

--namespace settheory_approach

--open Lean Elab Tactic
--axiom Inhabitant : Type
--axiom Knight : Finset Inhabitant
--axiom Knave : Finset Inhabitant
--variable [DecidableEq Inhabitant]
--axiom A : Inhabitant
--axiom B : Inhabitant
--@[simp]
--axiom AneB : A ≠ B
--axiom dis : Knight ∩ Knave = ∅
--axiom KorKn : ∀(x : Inhabitant), x ∈ Knight ∨ x ∈ Knave
--axiom all: ∀ (x : Inhabitant), x = A ∨ x = B


--end settheory_approach







inductive Inhabitant
| A
| B
deriving DecidableEq , Fintype

-- call these Knight internal then do local notation
namespace hidden
axiom Knight : Finset Inhabitant
axiom Knave : Finset Inhabitant

axiom  KorKn : ∀ x : Inhabitant, x ∈ Knight ∨ x ∈ Knave
axiom dis : Knight ∩ Knave = ∅
end hidden
@[pp_nodot]
noncomputable instance world : World Inhabitant :=  by
  exact ⟨hidden.Knight,
  hidden.Knave,
  hidden.dis,
  hidden.KorKn⟩


#check disjoint
open Inhabitant
--
--theorem disjoint_finset2 {K : Type} {A : K}  [DecidableEq K] 
--[W : World K]
--(h : W.Knight ∩ W.Knave = ∅) (hk : A ∈ W.Knight)
--  (hkn : A ∈ W.Knave) : False := by
--  have := Finset.mem_inter_of_mem hk hkn
--  rw [h] at this
--  contradiction
--
--
--theorem disjoint22
--[World Inhabitant]
--{A : Inhabitant}
--(AKnight : A ∈ Knight)
--(AKnave : A ∈ Knave)  : False := by
--  exact disjoint_finset dis AKnight AKnave

#check disjoint
--macro_rules
--| `(tactic| contradiction) =>
--  do `(tactic |solve  | ( exfalso ; apply disjoint22  ; repeat assumption) )
--
#synth World Inhabitant

macro_rules
| `(tactic| contradiction) =>
  do `(tactic |solve  | ( exfalso ; apply @disjoint Inhabitant  ; repeat assumption) )

example (h: A ∈ world.Knight) (h': A ∈ world.Knave ) : False := by 
  contradiction

theorem all : ∀x : Inhabitant , x = .A ∨ x = .B := by
  intro x
  cases x <;> aesop

theorem KorKnInternal : ∀x : Inhabitant , x ∈ Knight ∨ x ∈ Knave := by
  apply KorKn

--example {A : Inhabitant}: A ∈ Knight ∨ A ∈ Knave := by
--
--  -- locally bind the projections
--  #check world
--
--  -- now do cases
--  cases KorKnInternal A
--  cases KorKn A
--   
--  cases KorKn A with
--  | inl hK => 
--      -- hK : A ∈ Knight   ← now prints nicely
--      sorry
--  | inr hN =>
--      -- hN : A ∈ Knave   ← prints nicely
--      sorry
--  cases KorKn A with
--  | inl h => sorry-- h : A ∈ Knight
--  | inr h => sorry-- h : A ∈ Knave
--  --cases KorKn A
--  --left
--  --assumption
--  --right ; assumption
