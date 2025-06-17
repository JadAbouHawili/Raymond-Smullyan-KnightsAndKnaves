import SmullyanKnightsAndKnaves.dsl_knights_knaves

open Islander

example
{A B C : Islander}
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

example
{A B C : Islander}
(stB : B.isKnight ↔ (A.isKnight ↔ @oneisknight A B C))
(stC : C.isKnight ↔ B.isKnave)
: B.isKnave and C.isKnight := by

  have : B.isKnave 
  knave_to_knight
  intro BKnight
  knight_to_knave at BKnight
  simp [BKnight] at stC

  knight_or_knave A with AKnight AKnave
  knave_to_knight at BKnight
  have oneKst := stB.mp BKnight
  have oneK := oneKst.mp AKnight
  unfold oneisknight at oneK
  simp [AKnight, stC, BKnight] at oneK
  knave_to_knight at oneK 
  simp [ stC, BKnight] at oneK
  contradiction

  knave_to_knight at AKnave
  knave_to_knight at BKnight
  have onest := stB.mp BKnight
  simp [AKnave] at onest
  unfold oneisknight at onest
  simp [AKnave, stC, BKnight] at onest
  knave_to_knight at onest
  simp [AKnave] at onest
  contradiction

  have CKnight := stC.mpr this
  constructor
  assumption
  assumption
