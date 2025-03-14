import SmullyanKnightsAndKnaves.knightsknaves


/-
Problem 29:
Suppose A says, "Either I am a knave or B is a knight." 
What are A and B? 
-/
example
  {Inhabitant : Type}
  {A B : Inhabitant}
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{stA : A ∈ Knight  ↔ (A ∈ Knave ∨ B ∈ Knight) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∨ B ∈ Knight) }
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

    have AKnight := notright_left h1 AnKnave
    have BKnight := stA.mp AKnight
    constructor
    assumption 
    exact notleft_right BKnight AnKnave
  }


example
  {Inhabitant : Type}
  {A B : Inhabitant}
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{stA : A ∈ Knight  ↔ (A ∈ Knave ∨ B ∈ Knight) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∨ B ∈ Knight) }
  : A ∈ Knight ∧ B ∈ Knight := by

  {
    have forward := stA.mp
    rw [imp_or] at forward 
    rw [inright_notinleftIff h1 h] at forward  
    rw [imp_not_self] at forward

    rcases h1 with h_1|h_2
    · simp[h_1] at forward
      constructor
      assumption
      assumption
    ·
      have cont : A ∈ Knave ∨ B ∈ Knight := by left; assumption 
      have nimp := stAn.mp h_2
      contradiction
    }
