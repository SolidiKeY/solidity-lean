import Solidity.Backend.Passes.PublishedMixedCapture

/-! Published hash/value composition after a real reached capture. Byte memory
is an explicit per-run preimage, not an assertion that symbolic word memory is
byte memory. No hash injectivity, fetched EVM or public ABI claim is used. -/
namespace Solidity.Backend.Passes.ReachedHash
open Backend.Passes.Controls.Fixture

def path : MPath C Γ (.ref (.array (.prim .uint))) := .var (.there .here) rfl
def reached := CaptureControls.afterCapture
def offset : Backend.Environment.W256 := ⟨7, by decide⟩
def length : Backend.Environment.W256 := ⟨2, by decide⟩
def memory : Backend.Environment.Memory :=
  Backend.Environment.writeBytes (fun _ => 0xbb) 7 [8,9]

theorem evaluated : path.mvalT reached = .ok Evm.Memory.CompileExamples.r0 := by rfl

theorem input : Backend.Environment.HashInput ⟨[],memory⟩ offset length
    (MObj.words (.array (.prim .uint)) (reached.heap.get Evm.Memory.CompileExamples.r0)) := by
  constructor
  · decide +kernel
  · decide +kernel

def hash : Backend.Environment.ValueCertificate reached (.hash .keccak path rfl)
    PublishedMixedCapture.environment (Backend.Environment.keccakCode offset length) memory :=
  Backend.Environment.hashCertificate reached path Evm.Memory.CompileExamples.r0 evaluated
    PublishedMixedCapture.environment offset length memory input

/-- Reuse actual owner composition and its exact selected memoryOut. -/
def combined : Backend.Environment.ValuesCertificate reached
    [PublishedMixedCapture.expression, .hash .keccak path rfl] PublishedMixedCapture.environment
    (PublishedValues.code .selfAddress ⟨3,by decide⟩ ++ Backend.Environment.keccakCode offset length) memory :=
  Backend.Environment.consCertificate (PublishedMixedCapture.numeric memory)
    (Backend.Environment.consCertificate hash
      (Backend.Environment.nilCertificate reached PublishedMixedCapture.environment hash.memoryOut))

theorem source : Backend.Environment.evalValues reached
    [PublishedMixedCapture.expression, .hash .keccak path rfl] =
    .ok [PublishedMixedCapture.answer, reached.heap.hash .keccak Evm.Memory.CompileExamples.r0] :=
  combined.source

theorem target (tail : List Backend.Environment.Word) :
    Backend.Environment.runSlice PublishedMixedCapture.environment
      (PublishedValues.code .selfAddress ⟨3,by decide⟩ ++ Backend.Environment.keccakCode offset length)
      ⟨tail,memory⟩ =
      some ⟨reached.heap.hash .keccak Evm.Memory.CompileExamples.r0 ::
        PublishedMixedCapture.answer :: tail,memory⟩ :=
  combined.target tail

theorem bytes :
    Backend.decode (Backend.encode (PublishedValues.code .selfAddress ⟨3,by decide⟩ ++
      Backend.Environment.keccakCode offset length)) =
    some (PublishedValues.code .selfAddress ⟨3,by decide⟩ ++ Backend.Environment.keccakCode offset length) :=
  Backend.decode_encode _

/-- Exact byte memory, including every preimage byte and both framed neighbors. -/
theorem ordered_bytes : [0,6,7,8,9].map memory = [0xbb,0xbb,8,9,0xbb] := by decide +kernel

def staleMemory : Backend.Environment.Memory :=
  Backend.Environment.writeBytes (fun _ => 0xbb) 7 [7,9]

theorem stale_refused : ¬ Backend.Environment.HashInput ⟨[],staleMemory⟩ offset length
    (MObj.words (.array (.prim .uint)) (reached.heap.get Evm.Memory.CompileExamples.r0)) := by
  intro h
  have bad : (Backend.Environment.readMemory staleMemory 7 2).head? =
      (Backend.Environment.wireBytes [8,9]).head? := congrArg List.head? h.bytes
  change some (7 : UInt8) = some 8 at bad
  cases bad

def failedState : State C Γ :=
  {reached with env := (reached.env.1, none, reached.env.2.2)}

/-- A failed memory path has the original intrinsic failure; the successful
hashCertificate does not manufacture a target-failure compiler theorem. -/
theorem source_path_failure :
    (Val.hash .keccak path rfl : Val C Γ .uint).evalT
      failedState = .error .revert := by rfl

end Solidity.Backend.Passes.ReachedHash
