import Solidity.Backend.Executable.ValueCallChecks
import Solidity.Backend.Failure.Emit

/-! Export actual Backend.encode output for bounded external Osaka tests.
IO evaluation exports test data; it is not a kernel CALL/world proof. -/
namespace Solidity.Backend.Executable.ValueCallExport
open Scalar ScalarSequence ValueCall ValueCallChecks
open ScalarSequenceChecks (caller)
private def jsonBytes (xs : List UInt8) : String :=
  "[" ++ String.intercalate "," (xs.map (fun b => toString b.toNat)) ++ "]"
private def jsonStack (xs : Stack) : String :=
  "[" ++ String.intercalate "," (xs.map (fun w => "\"" ++ toString w.toNat ++ "\"")) ++ "]"
private def memorySeed : Program := [Failure.pushByte 0x55, Failure.pushNat 0, .op .MSTORE8]
private def stopped : Program := [.op .STOP]
private def reverted : Program := Failure.emit 0 (.custom [0xde,0xad])
private def emit (name : String) (body : Program) (input : Stack) (to : ContractWorld.Address)
    (callee : Program) (flag transferred entryGas : Nat) (returned : String)
    (accepts : Bool := true) (desired : Nat := 0) : IO Unit := do
  let preamble := memorySeed ++ input.reverse.map pushWord
  IO.println ("{\"name\":\"" ++ name ++ "\",\"body\":" ++ jsonBytes (Backend.encode body) ++
    ",\"preamble\":" ++ jsonBytes (Backend.encode preamble) ++
    ",\"code\":" ++ jsonBytes (Backend.encode (preamble ++ body)) ++
    ",\"input\":" ++ jsonStack input ++ ",\"expected\":" ++ jsonStack (BitVec.ofNat 256 flag :: input) ++
    ",\"recipient\":\"" ++ toString to.1.1.toNat ++ "\",\"callee\":" ++ jsonBytes (Backend.encode callee) ++
    ",\"transferred\":\"" ++ toString transferred ++ "\",\"entryGas\":\"" ++ toString entryGas ++
    "\",\"returnData\":\"" ++ returned ++ "\",\"accepts\":" ++ (if accepts then "true" else "false") ++
    ",\"desiredTransfer\":\"" ++ toString desired ++ "\"}")

def fixtures : IO Unit := do
  emit "literal-nonzero-request0" (code zero recipient one) [17,29] recipient stopped 1 1 2300 "" true 1
  emit "literal-zero-request2300" (code gas recipient zero) [17,29] recipient stopped 1 0 2300 "" true 0
  emit "local99-stop" (localCode gas recipient) (frameTail caller [17,29]) recipient stopped 1 99 4600 "" true 99
  emit "local13-same-code" (localCode gas recipient) (frameTail alternate [17,29]) recipient stopped 1 13 4600 "" true 13
  emit "local99-revert-dead" (localCode gas recipient) (frameTail caller [17,29]) recipient reverted 0 0 4600 "dead" true 0
  emit "address160-max" (code gas highRecipient one) [17,29] highRecipient stopped 1 1 4600 "" true 1
  let wrong := emptyBuffers ++ LocalFrame.uintCode ++ literal .uint recipient.1 ++ literal .uint gas ++ [.op .CALL]
  emit "wrong-unshifted-DUP2" wrong (frameTail caller [17,29]) recipient stopped 1 0 2300 "" false 99
end Solidity.Backend.Executable.ValueCallExport

def main : IO Unit := Solidity.Backend.Executable.ValueCallExport.fixtures
