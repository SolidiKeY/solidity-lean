import Lean.CoreM

/-!
# Opt-in evaluator code-generation context

Disable LCNF closed-term extraction while the original owner elaborates a
proof. This changes a compiler optimization, not certificate validation or
solver fuel. Cached caller limits, heartbeat origin and diagnostics remain
unchanged. The owner keeps its own internal scopes and behavior.
-/

namespace Solidity.Automation.H28

/-- Change only the evaluator compiler option; retain every cached context field. -/
@[inline] def codegenContext (context : Lean.Core.Context) : Lean.Core.Context :=
  { context with options := context.options.setBool `compiler.extract_closed false }

/-- Restoring the original options restores the entire original context. -/
theorem codegenContext_restore_options (context : Lean.Core.Context) :
    { codegenContext context with options := context.options } = context := rfl

/-- All cached budget fields, heartbeat origin and diagnostics are preserved. -/
theorem codegenContext_limits (context : Lean.Core.Context) :
    (codegenContext context).maxRecDepth = context.maxRecDepth ∧
    (codegenContext context).maxHeartbeats = context.maxHeartbeats ∧
    (codegenContext context).initHeartbeats = context.initHeartbeats ∧
    (codegenContext context).diag = context.diag ∧
    (codegenContext context).initHeartbeats + (codegenContext context).maxHeartbeats =
      context.initHeartbeats + context.maxHeartbeats :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end Solidity.Automation.H28
