import Solidity.Automation.H28.Context

/-! Same nondefault context for each frozen context-preservation theorem.
These fields are data in the witness, not changes to the proof-checking budget. -/
namespace Solidity.H62.AuditRoadmap.ContextWitnesses
open Solidity.Automation.H28

def context : Lean.Core.Context where
  fileName := "h62-audit-context"
  fileMap := Lean.FileMap.ofString ""
  options := Lean.Options.empty.setBool `compiler.extract_closed true
  maxRecDepth := 17
  maxHeartbeats := 19
  initHeartbeats := 23
  diag := true

theorem restore_joint : ∃ c : Lean.Core.Context,
    { codegenContext c with options := c.options } = c :=
  ⟨context, codegenContext_restore_options context⟩

theorem limits_joint : ∃ c : Lean.Core.Context,
    (codegenContext c).maxRecDepth = c.maxRecDepth ∧
    (codegenContext c).maxHeartbeats = c.maxHeartbeats ∧
    (codegenContext c).initHeartbeats = c.initHeartbeats ∧
    (codegenContext c).diag = c.diag ∧
    (codegenContext c).initHeartbeats + (codegenContext c).maxHeartbeats =
      c.initHeartbeats + c.maxHeartbeats :=
  ⟨context, codegenContext_limits context⟩

end Solidity.H62.AuditRoadmap.ContextWitnesses
#print axioms Solidity.H62.AuditRoadmap.ContextWitnesses.restore_joint
#print axioms Solidity.H62.AuditRoadmap.ContextWitnesses.limits_joint
