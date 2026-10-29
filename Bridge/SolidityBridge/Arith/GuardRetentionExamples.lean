import SolidityBridge.Arith.Lowering
import SolidityBridge.Arith.LoweringObstructions

/-! Inhabited controls for both scope flags and all three overflow modes.
The old-contract counterexamples remain unchanged in LoweringObstructions. -/
namespace Solidity.Bridge.Arith.GuardRetentionExamples
open LoweringObstructions

def scope (self retain : Bool) (mode : Option OFMode) : ElabScope :=
  { funs := [], selfFrame := self, retainFailureData := retain, overflow := mode }

def expected (self retain : Bool) (mode : Option OFMode) :
    Stmt exampleContract exampleState.1.toNCtx.ctx exampleState.1.toNCtx.ctx :=
  match mode with
  | none => if self || retain then panicStmt 17 exampleGuard else .require exampleGuard
  | some .checking => if self || retain then panicStmt 17 exampleGuard else .assert exampleGuard
  | some .ignoring => .ite exampleGuard .nil (.cons .assumeFalse .nil)

/-- The corrected public helper applies to an inhabited uint8 local for every
combination of the two flags and each ordinary/checking/ignoring mode. -/
theorem guard_matrix (self retain : Bool) (mode : Option OFMode) :
    narrowCheck exampleContract .uint 8 (.name "x") (scope self retain mode) exampleState =
      pure ([.of exampleState.1.toNCtx (expected self retain mode)], exampleState) := by
  rw [narrowCheck_guard exampleContract (scope self retain mode) exampleState
    .uint 8 (by decide) (.name "x") exampleGuard setup]
  cases mode with
  | none => cases self <;> cases retain <;> rfl
  | some mode => cases mode <;> cases self <;> cases retain <;> rfl

/-- Retaining data without a self-call is a panic guard, not the old require. -/
theorem retained_panic :
    narrowCheck exampleContract .uint 8 (.name "x") (scope false true none) exampleState =
      pure ([.of exampleState.1.toNCtx (panicStmt 17 exampleGuard)], exampleState) :=
  guard_matrix false true none

/-- info: 'Solidity.Bridge.Arith.narrowCheck_guard' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms narrowCheck_guard
/-- info: 'Solidity.Bridge.Arith.GuardRetentionExamples.guard_matrix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms guard_matrix
/-- info: 'Solidity.Bridge.Arith.GuardRetentionExamples.retained_panic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms retained_panic
end Solidity.Bridge.Arith.GuardRetentionExamples
