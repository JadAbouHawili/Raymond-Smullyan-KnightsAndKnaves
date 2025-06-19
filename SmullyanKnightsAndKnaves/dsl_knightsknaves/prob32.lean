import SmullyanKnightsAndKnaves.dsl_knights_knaves

open Islander
example
{A B C : Islander}
{stA : A said @allKnaves A B C}
{stB : B said @exactlyOneIsKnave A B C}
: A.isKnave and C.isKnight
:= by
  have AKnave : ¬A.isKnight
  intro AKnight
  have allKnave := knight_said stA AKnight
  unfold allKnaves at allKnave
  have := allKnave.left
  contradiction

  have notallKnave:= notknight_said stA AKnave
  knight_or_knave B with BKnight BKnave 
  have exactlyoneKnave := knight_said stB BKnight
  unfold exactlyOneIsKnave at exactlyoneKnave
  simp [AKnave, BKnight] at exactlyoneKnave
  assumption 

  unfold allKnaves at notallKnave 
  knight_to_knave at AKnave
  simp [AKnave,BKnave] at notallKnave
  constructor
  assumption
  knight_to_knave
  assumption

