import Solidity.Backend.Executable.StipendCallChecks
import Solidity.Backend.Failure.Emit

/-! Export actual Backend.encode output for bounded external Osaka tests.
IO evaluation exports test data; it is not a kernel CALL/world proof. -/
namespace Solidity.Backend.Executable.StipendCallExport
open Scalar ScalarSequence ValueCall ValueCallChecks
open ScalarSequenceChecks (caller)
open StipendCallChecks (zeroCaller)
private def jsonBytes (xs : List UInt8) : String :=
  "[" ++ String.intercalate "," (xs.map (fun b => toString b.toNat)) ++ "]"
private def jsonStack (xs : Stack) : String :=
  "[" ++ String.intercalate "," (xs.map (fun w => "\"" ++ toString w.toNat ++ "\"")) ++ "]"
private def memorySeed : Program := [Failure.pushByte 0x55, Failure.pushNat 0, .op .MSTORE8]
private def stopped : Program := [.op .STOP]
private def reverted : Program := Failure.emit 0 (.custom [0xde,0xad])
private def emit (name : String) (body : Program) (input : Stack) (to : ContractWorld.Address)
    (callee : Program) (flag transferred : Nat) (entryGas : Option Nat) (returned : String)
    (accepts : Bool := true) (desired : Nat := 0) (desiredGas : Nat := 2300) : IO Unit := do
  let preamble := memorySeed ++ input.reverse.map pushWord
  IO.println ("{\"name\":\"" ++ name ++ "\",\"body\":" ++ jsonBytes (Backend.encode body) ++
    ",\"preamble\":" ++ jsonBytes (Backend.encode preamble) ++
    ",\"code\":" ++ jsonBytes (Backend.encode (preamble ++ body)) ++
    ",\"input\":" ++ jsonStack input ++ ",\"expected\":" ++ jsonStack (BitVec.ofNat 256 flag :: input) ++
    ",\"recipient\":\"" ++ toString to.1.1.toNat ++ "\",\"callee\":" ++ jsonBytes (Backend.encode callee) ++
    ",\"transferred\":\"" ++ toString transferred ++ "\",\"entryGas\":\"" ++ (entryGas.map toString |>.getD "NONE") ++
    "\",\"returnData\":\"" ++ returned ++ "\",\"accepts\":" ++ (if accepts then "true" else "false") ++
    ",\"desiredTransfer\":\"" ++ toString desired ++ "\",\"desiredGas\":\"" ++ toString desiredGas ++ "\"}")

def fixtures : IO Unit := do
  emit "ordinary-zero" (StipendCall.code recipient) (frameTail zeroCaller [17,29]) recipient stopped 1 0 (some 2300) "" true 0
  emit "ordinary99" (StipendCall.code recipient) (frameTail caller [17,29]) recipient stopped 1 99 (some 2300) "" true 99
  emit "ordinary13-same-code" (StipendCall.code recipient) (frameTail alternate [17,29]) recipient stopped 1 13 (some 2300) "" true 13
  emit "ordinary99-revert" (StipendCall.code recipient) (frameTail caller [17,29]) recipient reverted 0 0 (some 2300) "dead" true 0
  let unfunded : State ScalarSequenceChecks.contract [.val .int,.val .uint] :=
    {caller with env := (⟨-7,by decide⟩,(⟨1001,by decide⟩,()))}
  emit "ordinary-unfunded" (StipendCall.code recipient) (frameTail unfunded [17,29]) recipient reverted 0 0 none "" true 0
  emit "wrong-fixed2300" (localCode gas recipient) (frameTail caller [17,29]) recipient stopped 1 99 (some 4600) "" false 99

end Solidity.Backend.Executable.StipendCallExport

def main : IO Unit := Solidity.Backend.Executable.StipendCallExport.fixtures
