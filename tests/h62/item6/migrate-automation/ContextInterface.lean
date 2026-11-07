import Solidity.Automation.H28.Context
import Lean

/-! Exact original signatures plus inhabited caller/option controls.
No theorem about the compiler or arbitrary owner behavior is asserted here. -/
open Solidity.Automation.H28

example : Lean.Core.Context → Lean.Core.Context := codegenContext
example (context : Lean.Core.Context) :
    { codegenContext context with options := context.options } = context :=
  codegenContext_restore_options context
example (context : Lean.Core.Context) :
    (codegenContext context).maxRecDepth = context.maxRecDepth ∧
    (codegenContext context).maxHeartbeats = context.maxHeartbeats ∧
    (codegenContext context).initHeartbeats = context.initHeartbeats ∧
    (codegenContext context).diag = context.diag ∧
    (codegenContext context).initHeartbeats + (codegenContext context).maxHeartbeats =
      context.initHeartbeats + context.maxHeartbeats := codegenContext_limits context

namespace MigrationAutomationControls

def caller : Lean.Core.Context := {
  fileName := "migration witness"
  fileMap := Lean.FileMap.ofString ""
  options := (({} : Lean.Options).setBool `compiler.extract_closed true).set `maxHeartbeats (19 : Nat)
  maxHeartbeats := 23
  initHeartbeats := 42
  maxRecDepth := 17
  diag := true
}

theorem cached_budget_preserved : (codegenContext caller).maxHeartbeats = 23 := rfl

-- Concrete option lookup is an external execution control. In v4.35 the
-- imported Options representation is private; this is not a kernel theorem
-- about its map implementation. The universal options equation below and all
-- original signatures above remain kernel checked.
run_cmd do
  let changed : Lean.Core.Context := codegenContext caller
  unless changed.maxHeartbeats == 23 &&
      changed.options.get `maxHeartbeats (200000 : Nat) == 19 do
    throwError "cached/option budget observation changed"
  Lean.logInfo "CONTEXT_RUNTIME cached=23 option=19"

theorem options_exact (context : Lean.Core.Context) :
    (codegenContext context).options = context.options.setBool `compiler.extract_closed false := rfl

#print axioms Solidity.Automation.H28.codegenContext
#print axioms Solidity.Automation.H28.codegenContext_restore_options
#print axioms Solidity.Automation.H28.codegenContext_limits
#print axioms cached_budget_preserved
#print axioms options_exact
end MigrationAutomationControls

open Lean Elab Command in
run_cmd do
  for name in [``Solidity.Automation.H28.codegenContext,
      ``Solidity.Automation.H28.codegenContext_restore_options,
      ``Solidity.Automation.H28.codegenContext_limits] do
    let info ← getConstInfo name
    logInfo m!"FROZEN_TYPE {name} {reprStr info.type}"
