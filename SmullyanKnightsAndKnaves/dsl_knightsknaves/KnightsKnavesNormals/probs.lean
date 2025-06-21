
/-
wolfram alpha generated
A: B* ⇔ C
B: A ∧ C
C: A*  B*

A: B is a knave, if and only if C is a knight.
B: A is a knight and C is a knight.
C: If A is a knave, then B is a knave.
-/
example
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
{stA : A ∈ Knight → (B ∈ Knave ↔ C ∈ Knight) }
{stAn : A ∈ Knave → ¬ (B ∈ Knave ↔ C ∈ Knight) }

{stB: B ∈ Knight → (A ∈ Knight ∧  C ∈ Knight) }
{stBn: B ∈ Knave → ¬ (A ∈ Knight ∧  C ∈ Knight) }

{stC: C ∈ Knight → (A ∈ Knave → B ∈ Knave) }
{stCn: C ∈ Knave → ¬ (A ∈ Knave → B ∈ Knave) }
{atleastK : Knight.card ≥ 1}
{atleastKn : Knave.card ≥ 1} : A ∈ Normal ∧ B ∈ Knave ∧ C ∈ Knight := by 
  -- B ∉ Knight
  sorry
