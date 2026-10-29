import Solidity.Backend.Creation.Artifact

/-! Inhabited layout controls and kernel trust pins for G44.02. -/
namespace Solidity.Backend.Creation

def sample : Artifact String :=
  ⟨[0x60, 0x2a, 0x00], [0xaa, 0xbb], by decide, 0, []⟩

example : (sample.payload.drop sample.runtimeStart).take 3 = [0x60, 0x2a, 0x00] :=
  sample.runtime_slice
example : sample.payload.drop sample.argsStart = [0xaa, 0xbb] := sample.args_slice
example : sample.runtime ≠ sample.args := by decide
example : sample.runtime.take 2 ≠ sample.runtime := by decide
example : decode (encode (wrapper sample.lengthWord)) = some (wrapper sample.lengthWord) :=
  decode_encode _

/-- An empty runtime still retains nonempty constructor arguments separately. -/
def emptyWithArgs : Artifact Unit := ⟨[], [0x60, 0xff], by decide, 0, []⟩
example : (emptyWithArgs.payload.drop emptyWithArgs.runtimeStart).take 0 = [] :=
  emptyWithArgs.runtime_slice
example : emptyWithArgs.payload.drop emptyWithArgs.argsStart = [0x60, 0xff] :=
  emptyWithArgs.args_slice

/-- Independent assembler link control: the opcode is outside the 20-byte payload. -/
example (address : Vector UInt8 20) :
    Item.emit (L := Unit) (fun _ => 0) (fun _ => 0) 0 (fun _ : Unit => some address)
      (.pushLibraryAddress ()) = .push 20 address := rfl

example (r : Assembled String) (h : (encode r.code).length < 256 ^ 32) :
    (fromAssembly 0 r [0xaa, 0xbb] h).payload.drop
      (fromAssembly 0 r [0xaa, 0xbb] h).argsStart = [0xaa, 0xbb] :=
  Artifact.args_slice _

#print axioms Immediate.read
#print axioms wrapper_size
#print axioms Artifact.runtime_slice
#print axioms Artifact.args_slice
end Solidity.Backend.Creation
