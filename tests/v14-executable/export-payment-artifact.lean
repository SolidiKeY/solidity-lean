import Solidity.Backend.Executable.PaymentArtifactChecks

/-! Actual artifact/assembler fixture data for bounded deployment tests.
Native IO and Keccak evaluations export data, never kernel proof shortcuts.
Raw code/nonce reads in the checker are internal validation, not new source observations. -/
namespace Solidity.Backend.Executable.PaymentArtifactExport
open Creation PaymentArtifact
private def jsonBytes (xs : List UInt8) : String :=
  "[" ++ String.intercalate "," (xs.map (fun b => toString b.toNat)) ++ "]"
private def checkedImage (bytes args : List UInt8) : IO (List UInt8) := do
  if fits : bytes.length < 256^32 then
    let n : Immediate := ⟨bytes.length,fits⟩
    let off : Immediate := if bytes.isEmpty then ⟨14,by decide⟩ else ⟨18,by decide⟩
    let header := Backend.encode copyPrefix ++ Backend.encode (exitWrapper true n off)
    unless header.length = off.value do throw (IO.userError "fixture alignment refused")
    pure (header ++ bytes ++ args)
  else throw (IO.userError "fixture runtime does not fit word")
private def emit (name : String) (bytes initcode callee : List UInt8) : IO Unit := do
  IO.println ("{\"name\":\"" ++ name ++ "\",\"runtime\":" ++ jsonBytes bytes ++
    ",\"initcode\":" ++ jsonBytes initcode ++ ",\"callee\":" ++ jsonBytes callee ++
    ",\"paymentRuntime\":" ++ jsonBytes runtime ++ ",\"args\":" ++ jsonBytes PaymentArtifactChecks.args ++
    ",\"create0\":\"" ++ toString (Roadmap.Evm.withKeccak.createAddress 0xa000 0) ++
    "\",\"create1\":\"" ++ toString (Roadmap.Evm.withKeccak.createAddress 0xa000 1) ++ "\"}")

def fixtures : IO Unit := do
  let args := PaymentArtifactChecks.args
  let stopped := Backend.encode [.op .STOP]
  let reverted := Backend.encode (Failure.emit 0 (.custom [0xde,0xad]))
  emit "deploy-transfer" runtime (image true args) stopped
  emit "deploy-then-receiver-revert" runtime (image true args) reverted
  emit "constructor-revert" runtime (image false args) stopped
  let some wrong := Backend.assemble 18 TransferCall.noLink (TransferCall.items TransferCallChecks.payment)
    | throw (IO.userError "wrong-base fixture assembly refused")
  let wrongBytes := Backend.encode wrong.code
  emit "wrong-runtime-base" wrongBytes (← checkedImage wrongBytes args) stopped
  let leaked := runtime ++ args
  emit "arguments-leak" leaked (← checkedImage leaked []) stopped
  let empty := PrefixChecks.emptyPlacement
  let emptyImage := Backend.encode copyPrefix ++ Backend.encode (exitWrapper true empty.lengthWord empty.offsetWord) ++ args
  emit "empty-runtime" [] emptyImage stopped
  emit "two-instances" runtime (image true args) stopped
  emit "occupied-address" runtime (image true args) stopped
end Solidity.Backend.Executable.PaymentArtifactExport

def main : IO Unit := Solidity.Backend.Executable.PaymentArtifactExport.fixtures
