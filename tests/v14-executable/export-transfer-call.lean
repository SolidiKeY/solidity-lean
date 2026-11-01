import Solidity.Backend.Executable.TransferCallChecks

/-! Bounded fetched-message test data, from the actual published assembler.
Native IO evaluation exports bytes; no proof is obtained from that evaluation. -/
namespace Solidity.Backend.Executable.TransferCallExport
open Scalar ScalarSequence ValueCallChecks
open ScalarSequenceChecks (caller contract)
open StipendCallChecks (zeroCaller)
private def jsonBytes (xs : List UInt8) : String :=
  "[" ++ String.intercalate "," (xs.map (fun b => toString b.toNat)) ++ "]"
private def jsonStack (xs : Stack) : String :=
  "[" ++ String.intercalate "," (xs.map (fun w => "\"" ++ toString w.toNat ++ "\"")) ++ "]"
private def other : ContractWorld.Address := ⟨⟨4098,by decide +kernel⟩,by decide +kernel⟩
private def firstPayment : Program := ValueCall.code ValueCallChecks.zero other one ++ [.op .POP]
private def emit (name : String) (σ : State contract [.val .int,.val .uint])
    (callee : Program) (paidPrefix : Bool := false) (wrongRelative : Bool := false) : IO Unit := do
  let input := frameTail σ [17,29]
  let prelude := [Failure.pushByte 0x55,Failure.pushNat 0,.op .MSTORE8] ++ input.reverse.map pushWord
  let paid := if paidPrefix then firstPayment else []
  let prefixCode := prelude ++ paid ++ StipendCall.code recipient
  let assembledInput := if wrongRelative then StipendCall.code recipient else prefixCode
  let some out := TransferCall.assembleAfter assembledInput | throw (IO.userError (name ++ ": assembly refused"))
  let fullCode := if wrongRelative then prelude ++ out.code else out.code
  IO.println ("{\"name\":\"" ++ name ++ "\",\"code\":" ++ jsonBytes (Backend.encode fullCode) ++
    ",\"input\":" ++ jsonStack input ++ ",\"preamble\":" ++ jsonBytes (Backend.encode prelude) ++
    ",\"paidPrefix\":" ++ (if paidPrefix then "true" else "false") ++
    ",\"wrongRelative\":" ++ (if wrongRelative then "true" else "false") ++
    ",\"callBytes\":" ++ jsonBytes (Backend.encode (StipendCall.code recipient)) ++
    ",\"firstPayment\":" ++ jsonBytes (Backend.encode paid) ++
    ",\"assembledPrefix\":" ++ jsonBytes (Backend.encode assembledInput) ++
    ",\"callee\":" ++ jsonBytes (Backend.encode callee) ++ "}")

def fixtures : IO Unit := do
  let stopped : Program := [.op .STOP]
  let reverted : Program := Failure.emit 0 (.custom [0xde,0xad])
  emit "transfer-zero" zeroCaller stopped
  emit "transfer99" caller stopped
  emit "transfer13" alternate stopped
  emit "transfer99-revert" caller reverted
  let unfunded : State contract [.val .int,.val .uint] :=
    {caller with env := (⟨-7,by decide⟩,(⟨1001,by decide⟩,()))}
  emit "transfer-unfunded" unfunded reverted
  emit "paid-prefix-success" caller stopped true
  emit "paid-prefix-failure" caller reverted true
  emit "wrong-relative" caller stopped false true
end Solidity.Backend.Executable.TransferCallExport

def main : IO Unit := Solidity.Backend.Executable.TransferCallExport.fixtures
