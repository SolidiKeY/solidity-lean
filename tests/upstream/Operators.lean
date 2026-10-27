import Solidity.Tools.Upstream

/-! Group 03 controls: source constants, signed complement and declaration-bound ABI replay. -/
solc_import "../operators-0.8.38/OperatorBoundaries.ast.json" hash 0x8a9b1c12e756db49
  as Imported.OperatorBoundaries testing
solc_import "../operators-0.8.38/OperatorBoundariesIR.ast.json" hash 0x4971602e31f57626
  as Imported.IR.OperatorBoundaries testing

namespace Solidity.Upstream.Operators
open Solidity Lean Solidity.Frontend Solidity.Tools.Upstream

/-- Solidity signed `~x` is `-1 - x`, including the minimum signed integer. -/
theorem signedComplement_eq (x : Int) : ~~~x = -1 - x := by
  change Int.not x = -1 - x
  cases x <;> simp only [Int.not, Int.ofNat_eq_natCast] <;> omega

/-- The signed complement rewrite cannot overflow at either endpoint. -/
theorem signedComplement_range (bound x : Int) (lo : -bound ≤ x) (hi : x < bound) :
    -bound ≤ -1 - x ∧ -1 - x < bound := by omega

#guard Imported.OperatorBoundaries.report.all (fun r => r.status == .elaborated)
#guard Imported.IR.OperatorBoundaries.report.all (fun r => r.status == .elaborated)

/-- Source int8/int64/int256 boundaries, narrow constants and byte padding. -/
theorem boundaries_legacy :
    (Prog.run (State.init Imported.OperatorBoundaries) Imported.OperatorBoundaries.boundaries).isOk = true := by
  decide +kernel

/-- The same complete source boundary checks through via-IR. -/
theorem boundaries_viaIR :
    (Prog.run (State.init Imported.IR.OperatorBoundaries) Imported.IR.OperatorBoundaries.boundaries).isOk = true := by
  decide +kernel

/-- Builtin and aliased complement operands increment once. -/
theorem effects_legacy :
    (Prog.run (State.init Imported.OperatorBoundaries) Imported.OperatorBoundaries.effects).isOk = true := by
  decide +kernel

/-- Via-IR also preserves the single operand evaluation. -/
theorem effects_viaIR :
    (Prog.run (State.init Imported.IR.OperatorBoundaries) Imported.IR.OperatorBoundaries.effects).isOk = true := by
  decide +kernel

/-- Unchecked caller arithmetic preserves signed complement at the minimum value. -/
theorem uncheckedBoundaries_legacy :
    (Prog.run (State.init Imported.OperatorBoundaries) Imported.OperatorBoundaries.uncheckedBoundaries).isOk = true := by
  decide +kernel

/-- The same unchecked boundary controls in via-IR. -/
theorem uncheckedBoundaries_viaIR :
    (Prog.run (State.init Imported.IR.OperatorBoundaries) Imported.IR.OperatorBoundaries.uncheckedBoundaries).isOk = true := by
  decide +kernel

/-- A wrong complement assertion actually panics. -/
theorem falseComplement_legacy :
    (match Prog.run (State.init Imported.OperatorBoundaries) Imported.OperatorBoundaries.falseComplement with
      | .error .panic => true | _ => false) = true := by decide +kernel

/-- The via-IR wrong complement assertion also panics. -/
theorem falseComplement_viaIR :
    (match Prog.run (State.init Imported.IR.OperatorBoundaries) Imported.IR.OperatorBoundaries.falseComplement with
      | .error .panic => true | _ => false) = true := by decide +kernel

private def checkReplay (C : Contract) (rows : List ImportRow) : IO Unit := do
  let data ← IO.ofExcept (Json.parse "{\"vectors\":[
    {\"signature\":\"overloaded(int8)\",\"args\":[\"7\"],\"failure\":false,\"expected\":[\"8\"]},
    {\"signature\":\"overloaded(int64)\",\"args\":[\"7\"],\"failure\":false,\"expected\":[\"9\"]},
    {\"signature\":\"controls()\",\"args\":[],\"failure\":false,\"expected\":[]}
  ]}")
  let result := replay C rows data
  unless (result.getObjValAs? String "status").toOption == some "working" do
    throw (IO.userError result.pretty)
  let bad ← IO.ofExcept (Json.parse "{\"vectors\":[
    {\"signature\":\"overloaded(int16)\",\"args\":[\"7\"],\"failure\":false,\"expected\":[\"8\"]}
  ]}")
  unless ((replay C rows bad).getObjValAs? String "status").toOption == some "broken" do
    throw (IO.userError "ABI selection fell back to a function spelling")

#eval checkReplay Imported.OperatorBoundaries Imported.OperatorBoundaries.report
#eval checkReplay Imported.IR.OperatorBoundaries Imported.IR.OperatorBoundaries.report
#print axioms signedComplement_eq
#print axioms signedComplement_range
#print axioms boundaries_legacy
#print axioms boundaries_viaIR
#print axioms effects_legacy
#print axioms effects_viaIR
#print axioms uncheckedBoundaries_legacy
#print axioms uncheckedBoundaries_viaIR
#print axioms falseComplement_legacy
#print axioms falseComplement_viaIR
end Solidity.Upstream.Operators
