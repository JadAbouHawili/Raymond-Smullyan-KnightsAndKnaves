import SmullyanKnightsAndKnaves.knightsknaves

example
{Inhabitant : Type}
{A : Inhabitant}
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
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
      exact disjoint hKKn AKnight AKnave

    have AnKnave : A ∉ Knave := by 
      intro AKnave 
      have AnKnave := stAn AKnave 
      exact AnKnave AKnave

    simp [AnKnight,AnKnave] at Or 
    assumption
  }


example 
{Inhabitant : Type}
{A : Inhabitant}
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
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
    exact disjoint hKKn AKnight AKnave

  have AnKnave : A ∉ Knave := by
    intro AKnave 
    have AnKnave := stAn AKnave
    contradiction
  simp [*] at h1
  assumption
