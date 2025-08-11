import SmullyanKnightsAndKnaves.dsl_knights_knaves

open Islander

example
(stB : B said (A said @oneisknight A B C))
(stC : C said B.isKnave)
: B.isKnave and C.isKnight := by

  have : B.isKnave
  knave_to_knight
  intro BKnight
  have stA := knight_said stB BKnight
  knight_to_knave at BKnight
  have CKnave := said_knave stC BKnight

  knight_or_knave A with AKnight AKnave
  have hF := knight_said stA AKnight
  unfold oneisknight at hF
  simp [CKnave,AKnight,BKnight] at hF
  knave_to_knight at hF
  simp [CKnave,AKnight,BKnight] at hF

  have notoneknight := knave_said stA AKnave
  unfold oneisknight at notoneknight
  simp [BKnight,AKnave,CKnave] at notoneknight
  knave_to_knight at BKnight
  contradiction

  have CKnight := said_knight stC this 
  constructor
  assumption
  assumption
