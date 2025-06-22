import SmullyanKnightsAndKnaves.knightsknaves

open settheory_approach
example
  {inst : DecidableEq Inhabitant}
{stA : A ∈ Knight  ↔ (A ∈ Knave ∨ B ∈ Knight) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∨ B ∈ Knight) }
  : A ∈ Knight ∧ B ∈ Knight := by
  {
    have forward := stA.mp
    rw [imp_or] at forward
    rw [inright_notinleftIff] at forward
    rw [imp_not_self] at forward

    set_knight_or_knave A with h_1 h_2
    · simp[h_1] at forward
      constructor
      assumption
      assumption
    ·
      have cont : A ∈ Knave ∨ B ∈ Knight := by left; assumption 
      have nimp := stAn.mp h_2
      contradiction
    }

example
{inst : DecidableEq Inhabitant}
{stA : A ∈ Knight  ↔ (A ∈ Knave ∨ B ∈ Knight) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∨ B ∈ Knight)}
  : A ∈ Knight ∧ B ∈ Knight := by
  {
    have AnKnave : A ∉ Knave := by
      intro AKnave
      have Or : A ∈ Knave ∨ B ∈ Knight := by
      {
        left
        assumption
      }

      have := stAn.mp AKnave
      contradiction

    have AKnight := notright_left KorKn AnKnave
    have BKnight := stA.mp AKnight
    constructor
    assumption
    exact notleft_right BKnight AnKnave
  }
