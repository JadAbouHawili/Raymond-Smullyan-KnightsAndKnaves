import SmullyanKnightsAndKnaves.dsl_knights_knaves

/-
We again have three inhabitants, A, B, and C, each of whom 
is a knight or a knave. Two people are said to be of the same 
type if they are both knights or both knaves. A and B make 
the following statements: 
A: B is a knave. 
B: A and C are of the same type. 
What is C? 
-/
open Islander
example
{stA : A said B.isKnave}
{stB : B said ((A.isKnight and C.isKnight) or (A.isKnave and C.isKnave))}
: C.isKnave := by 
  knight_or_knave A with AKnight AKnave
  · have BKnave := knight_said stA AKnight
    have ACnotsame := knave_said stB BKnave
    knave_to_knight at ACnotsame
    simp [AKnight] at ACnotsame
    knave_to_knight
    assumption
  · have BKnight := knave_said stA AKnave 
    knave_to_knight at BKnight
    have ACsame := knight_said stB BKnight
    knight_to_knave at ACsame
    simp [AKnave] at ACsame
    assumption

example
{stA : A said B.isKnave}
{stB : B said (A.isKnight ↔ C.isKnight)}
: C.isKnave := by
  #check not_iff_not
  knight_or_knave A with AKnight AKnave
  · have BKnave := knight_said stA AKnight
    have ACnotsame := knave_said stB BKnave
    rw [not_iff] at ACnotsame
    simp [AKnight] at ACnotsame
    knave_to_knight
    assumption
  · have BKnight := knave_said stA AKnave
    knave_to_knight at BKnight
    have ACsame := knight_said stB BKnight
    knight_to_knave at ACsame
    simp [AKnave] at ACsame
    assumption
