import Solidity.Backend.Executable.SendResultChecks
import Solidity.Backend.Failure.Emit

/-! Finite independent fetched-EVM fixtures from actual typed local encodings.
An encoded local frame alone does not establish transaction/world reconciliation. -/
namespace Solidity.Backend.Executable.SendResultExport
open Scalar SendResult
open PaymentCases (C caller one four)
open ValueCallChecks (recipient zero)
private def jsonBytes (xs : List UInt8) : String :=
  "[" ++ String.intercalate "," (xs.map (fun b => toString b.toNat)) ++ "]"
private def jsonStack (xs : Stack) : String :=
  "[" ++ String.intercalate "," (xs.map (fun w => "\"" ++ toString w.toNat ++ "\"")) ++ "]"
private def emit (name : String) (old : Bool) (amount : PrimTy.uint.Denote)
    (callee : Program) (variant : String := "store") : IO Unit := do
  let σ := (caller false).setLocal .here old
  let input := frame σ [17,29]
  let prelude := [Failure.pushByte 0x55,Failure.pushNat 0,.op .MSTORE8] ++ input.reverse.map pushWord
  let suffix : Program := if variant = "pop" then [.op .POP]
    else if variant = "swap2" then [.op (.SWAP ⟨1,by decide⟩),.op .POP] else store
  let body := if variant = "store" then SendResult.code recipient amount
    else ValueCall.code (StipendCall.requested amount) recipient amount ++ suffix
  IO.println ("{\"name\":\"" ++ name ++ "\",\"code\":" ++ jsonBytes (Backend.encode (prelude ++ body)) ++
    ",\"body\":" ++ jsonBytes (Backend.encode body) ++ ",\"preamble\":" ++ jsonBytes (Backend.encode prelude) ++
    ",\"input\":" ++ jsonStack input ++ ",\"initialBalance\":\"" ++ toString σ.selfBalance.1.toNat ++
    "\",\"amount\":\"" ++ toString amount.1.toNat ++ "\",\"variant\":\"" ++ variant ++
    "\",\"callee\":" ++ jsonBytes (Backend.encode callee) ++ "}")

def fixtures : IO Unit := do
  let stopped : Program := [.op .STOP]
  let reverted : Program := Failure.emit 0 (.custom [0xde,0xad])
  emit "false-to-true" false one stopped
  emit "true-stays-true" true one stopped
  emit "true-to-false" true one reverted
  emit "false-stays-false" false one reverted
  emit "funding-before-revert" true four reverted
  emit "zero-value" false zero stopped
  emit "wrong-POP" false one stopped "pop"
  emit "wrong-SWAP2" false one stopped "swap2"
end Solidity.Backend.Executable.SendResultExport

def main : IO Unit := Solidity.Backend.Executable.SendResultExport.fixtures
