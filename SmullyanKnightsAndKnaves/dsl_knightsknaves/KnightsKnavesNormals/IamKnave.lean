import SmullyanKnightsAndKnaves.knightsknaves

open settheory_approach
example
  {inst : DecidableEq Inhabitant}
  {Normal : Finset Inhabitant} 
{hKKn : Knight ∩ Knave = ∅ }
{hKN : Knight ∩ Normal = ∅ }
{hKnN : Knave ∩ Normal = ∅ }
{Or : A ∈ Knight ∨ A ∈ Knave ∨ A ∈ Normal}
{stA : A ∈ Knight → (A ∈ Knave) }
{stAn : A ∈ Knave → ¬ (A ∈ Knave) }
  : A ∈ Normal := by
  {
    #check IamKnave
    have AnKnight : A ∉ Knight := by 
      intro AKnight 
      have AKnave := stA AKnight
      contradiction

    have AnKnave : A ∉ Knave := by 
      intro AKnave 
      have AnKnave := stAn AKnave 
      exact AnKnave AKnave

    simp [AnKnight,AnKnave] at Or 
    assumption
  }

example 
  {inst : DecidableEq Inhabitant}
  {Normal : Finset Inhabitant}
{hKKn : Knight ∩ Knave = ∅ }
{hKnN : Knave ∩ Normal = ∅ }
{hKN : Knight ∩ Normal = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave ∨ A ∈ Normal }
{stA : A ∈ Knight  → (A ∈ Knave) }
{stAn : A ∈ Knave → ¬ (A ∈ Knave) }
  : A ∈ Normal := by
  have AnKnight : A ∉ Knight := by 
    intro AKnight 
    have AKnave := stA AKnight 
    contradiction

  have AnKnave : A ∉ Knave := by
    intro AKnave 
    have AnKnave := stAn AKnave
    contradiction
  simp [*] at h1
  assumption
