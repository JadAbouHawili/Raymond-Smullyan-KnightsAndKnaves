import SmullyanKnightsAndKnaves.knightsknaves_foundation

inductive Inhabitant
| A
| B
deriving DecidableEq , Fintype

noncomputable instance world : World Inhabitant :=  by exact W

macro_rules
| `(tactic| contradiction) =>
  do `(tactic |solve  | ( exfalso ; apply @disjoint Inhabitant  ; repeat assumption) )
macro "contradiction_hyp" h1:ident h2:ident : tactic =>
  `(tactic| (exact disjoint $h1 $h2) )

open Inhabitant

-- redundant/not needed , keep
theorem all : ∀x : Inhabitant , x = .A ∨ x = .B := by
  intro x
  cases x <;> aesop

macro "by_universe" : tactic =>
  `(tactic| (apply set_subset_univ2 ; intro x ; exact all x))
