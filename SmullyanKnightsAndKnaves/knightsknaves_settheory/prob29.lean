import SmullyanKnightsAndKnaves.knightsknaves
import Lean
open Lean
open Lean.Elab
open Lean.Elab.Tactic
open Lean.Syntax
open Lean
open Lean.Elab
open Lean.Elab.Tactic  -- THIS is where `elabTactic` lives
open Lean.Meta         -- sometimes needed for `inferType` etc.

--open settheory_approach
open Inhabitant
#check Mathlib.Tactic.elabCheckTactic 
#check world.KorKn
-- interesting and works , look into...
--elab "set_knight_or_knave" t1:term "with" t2:rcasesPat t3:rcasesPat : tactic =>
--  do
--    logInfo m!"t1 syntax = {t1}"
--    logInfo m!"t2 syntax = {t2}"
--    logInfo m!"t3 syntax = {t3}"
--  -- log the type of KorKn
--    let korknExpr := mkConst `KorKn
--    let korknType ← inferType korknExpr
--    logInfo m!"KorKn type = {toMessageData korknType}"

  --  logInfo m!"KorKn syntax = {KorKn}"
    --return `(tactic| obtain $t2|$t3 := (KorKn $t1))
   -- let tacSyntax ← `(tactic| obtain $t2|$t3 := (KorKn $t1))
   -- Lean.Elab.Tactic.elabTactic
   -- elabTactic tacSyntax

example
--  {inst : DecidableEq Inhabitant}
{stA : A ∈ Knight  ↔ (A ∈ Knave ∨ B ∈ Knight) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∨ B ∈ Knight) }
  : A ∈ Knight ∧ B ∈ Knight := by
  {
    have forward := stA.mp
    rw [imp_or] at forward
    knight_interp at forward
    rw [imp_not_self] at forward

    have := KorKn A
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
{stA : A ∈ Knight  ↔ (A ∈ Knave ∨ B ∈ Knight) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∨ B ∈ Knight)}
  : A ∈ Knight ∧ B ∈ Knight := by
  {
    have AKnight : A ∈ Knight := by
      knave_interp
      intro AKnave
      have Or : A ∈ Knave ∨ B ∈ Knight := by
      {
        left
        assumption
      }

      have := stA.mpr Or
      contradiction

    have BKnight := stA.mp AKnight
    constructor
    assumption
    knave_interp at AKnight
    simp [AKnight] at BKnight
    assumption
  }
