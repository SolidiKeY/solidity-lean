import Lean

/-! Isolated upstream API compatibility witnesses for Tools elaborators.
These do not import or certify any assigned Tools declaration. No registration.
-/
namespace H62.ToolsMigrationFixtures
open Lean Meta Elab Command Term

/-- Intrinsic witness keeps the finite bound in the value's type. -/
def bounded (n : Nat) : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩

theorem bounded_val (n : Nat) : (bounded n).val = n := rfl

/-- The same expression-construction/evaluation boundary as Tools.Common.
This executes metaprogram code; the theorem above is a separate kernel proof.
-/
elab "#tools_api_fixture" : command => liftTermElabM do
  let expression ← mkAppM ``String.length #[toExpr "abc"]
  let expression ← instantiateMVars expression
  let result ← unsafe evalExpr Nat (mkConst ``Nat) expression
  unless result == 3 do throwError "unexpected upstream String.length result"
  logInfo m!"tools API fixture: {result}"

/-- info: tools API fixture: 3 -/
#guard_msgs in
#tools_api_fixture

/-- Expression API rejection is observable, rather than silently accepted. -/
elab "#tools_api_reject" : command => liftTermElabM do
  let rejected ← try
    let _ ← mkAppM ``Nat.succ #[toExpr "wrong type"]
    pure false
  catch _ => pure true
  unless rejected do throwError "fixture expected a type error"
  logInfo "ill-typed application rejected"

/-- info: ill-typed application rejected -/
#guard_msgs in
#tools_api_reject

end H62.ToolsMigrationFixtures
