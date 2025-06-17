import SmullyanKnightsAndKnaves.dsl_knights_knaves

open Islander

example {A : Islander} (stA : A said (A.isKnave or (2+2=5)))
: False := by
  simp at stA
  exact dsl_iamknave stA
