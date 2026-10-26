import Solidity.Tools.Upstream
import Solidity.Semantics.NumericLowering

/-! Source controls for signed shifts, powers, contextual widths and collision-free
local identities. Large exponent checks below are runtime observations. -/
solc_import "../../../tests/solc/SignedNumeric.ast.json" hash 0x48bd22f40f0bcb26 as Imported.SignedNumeric testing
solc_import "../../../tests/solc/SignedNumericIR.ast.json" hash 0x8ade83b0b9f5e2d3 as Imported.IR.SignedNumeric testing

namespace Solidity.Examples.Tactics.SignedNumericImport
open Lean Solidity.Frontend

#guard Imported.SignedNumeric.report.all fun r => r.status == .elaborated || r.status == .skipped
#guard Imported.IR.SignedNumeric.report.all fun r => r.status == .elaborated || r.status == .skipped

private def isRevert {α : Type} : TRes α → Bool
  | .error .revert => true
  | _ => false
private def isPanic {α : Type} : TRes α → Bool
  | .error .panic => true
  | _ => false

private def observe (C : Contract) (name : String) : IO Unit := do
  let .ok stmt := Solidity.Tools.runStmt C name [] | throw (IO.userError name)
  let .ok ⟨_, program⟩ := elabProgS C [stmt] | throw (IO.userError name)
  unless (Prog.run (State.init C) program).isOk do throw (IO.userError name)
#eval observe Imported.SignedNumeric "shifts"
#eval observe Imported.SignedNumeric "powers"
#eval observe Imported.SignedNumeric "uncheckedControls"
#eval observe Imported.SignedNumeric "effects"
#eval observe Imported.SignedNumeric "parity"
theorem legacy_wrongShift : isPanic (Prog.run (State.init Imported.SignedNumeric) Imported.SignedNumeric.wrongShift) = true := by
  decide +kernel
theorem legacy_checkedOverflow : isRevert (Prog.run (State.init Imported.SignedNumeric) Imported.SignedNumeric.checkedOverflow) = true := by
  decide +kernel
theorem legacy_parity : (Prog.run (State.init Imported.SignedNumeric) Imported.SignedNumeric.parity).isOk = true := by
  decide +kernel
#eval observe Imported.IR.SignedNumeric "shifts"
#eval observe Imported.IR.SignedNumeric "powers"
#eval observe Imported.IR.SignedNumeric "uncheckedControls"
#eval observe Imported.IR.SignedNumeric "effects"
#eval observe Imported.IR.SignedNumeric "parity"
theorem viaIR_wrongShift : isPanic (Prog.run (State.init Imported.IR.SignedNumeric) Imported.IR.SignedNumeric.wrongShift) = true := by
  decide +kernel
theorem viaIR_checkedOverflow : isRevert (Prog.run (State.init Imported.IR.SignedNumeric) Imported.IR.SignedNumeric.checkedOverflow) = true := by
  decide +kernel
theorem viaIR_parity : (Prog.run (State.init Imported.IR.SignedNumeric) Imported.IR.SignedNumeric.parity).isOk = true := by
  decide +kernel

/-- Full-width overflow exercises the signed range witness before any narrowing. -/
private def fullOverflow := sol[Imported.SignedNumeric]{
  int a = 2; uint n = 255; int r = a ** n;
}
private def guardedFullOverflow := sol[Imported.SignedNumeric]{
  checked { int a = 2; uint n = 255; int r = a ** n; };
}
theorem fullOverflow_reverts :
    isRevert (Prog.run (State.init Imported.SignedNumeric) fullOverflow) = true := by
  decide +kernel
/-- The model-only checking extension guards arithmetic overflow, unlike division by zero. -/
theorem fullOverflow_checked_panics :
    isPanic (Prog.run (State.init Imported.SignedNumeric) guardedFullOverflow) = true := by
  decide +kernel

#print axioms Solidity.NumericLowering.checkedSignedPower_correct
#print axioms Solidity.NumericLowering.powerLowering_correct
#print axioms Solidity.NumericLowering.abs_word
#print axioms Solidity.NumericLowering.shr_clamp
#print axioms Solidity.NumericLowering.shr_literal
#print axioms Solidity.NumericLowering.shift_count_cast
#print axioms legacy_parity
#print axioms fullOverflow_checked_panics
end Solidity.Examples.Tactics.SignedNumericImport
