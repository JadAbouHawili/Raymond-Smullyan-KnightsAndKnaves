import SmullyanKnightsAndKnaves.knightsknaves

open Inhabitant

example
{stA : A ∈ Knight  ↔ (A ∈ Knave ∨ B ∈ Knight) }
  : A ∈ Knight ∧ B ∈ Knight := by

    have AKnight : A ∈ Knight
    knave_interp
    intro AKnave
    have Or : A ∈ Knave ∨ B ∈ Knight
    left
    assumption

    have := stA.mpr Or
    contradiction

    have BKnight := stA.mp AKnight
    constructor
    assumption
    knave_interp at AKnight
    simp [AKnight] at BKnight
    assumption
  
