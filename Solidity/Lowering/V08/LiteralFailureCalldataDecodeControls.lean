import Solidity.Lowering.V08.LiteralFailureCalldataDecode
import Solidity.Lowering.V08.SourceExternalPhaseControls

namespace Solidity.Lowering.V08.LiteralFailureCalldataDecodeControls
open Solidity Source LiteralFailureCalldataDecode SourceCustomErrorControls

def u8 : IntTy := ⟨false,8,by decide +kernel⟩
def context := .bytes .calldata :: SourceExternalPhaseControls.ctx

def locals (off len : Nat) : Locals E.layout context :=
 .cons (.cdRef rfl off len) SourceExternalPhaseControls.caller

def F (data : Roadmap.Bytes) : Fr := {frame with cd := data}
def decode (types : List STy) (allowed : types.all (STy.decodable E) = true) :
 RExpr E context (STy.ret types) := .abiDecode (.local .here) rfl allowed

def callPrefix : Roadmap.Bytes := [8,9,0,255]
def data (n : Nat) : Roadmap.Bytes := callPrefix ++ wordBytes (toWord n) ++ [17,19]

theorem success (p : Roadmap.Pipeline) :
 (evalE (global p) (F (data 7)) 2 (decode [.int u8] rfl)).run (locals 4 32,populated) =
 (.ok (.val (.int 7 (by decide +kernel))),(locals 4 32,populated)) := by rfl

theorem dirty_uint (p : Roadmap.Pipeline) :
 (evalE (global p) (F (data 300)) 2 (decode [.int u8] rfl)).run (locals 4 32,populated) =
 (.error (.revert []),(locals 4 32,populated)) := by rfl

theorem dirty_bool (p : Roadmap.Pipeline) :
 (evalE (global p) (F (data 2)) 2 (decode [.bool] rfl)).run (locals 4 32,populated) =
 (.error (.revert []),(locals 4 32,populated)) := by rfl

theorem short_head (p : Roadmap.Pipeline) :
 (evalE (global p) (F (data 7)) 2 (decode [.int u8] rfl)).run (locals 4 31,populated) =
 (.error (.revert []),(locals 4 31,populated)) := by rfl

theorem trailing_accepted (p : Roadmap.Pipeline) :
 (evalE (global p) (F (data 1)) 2 (decode [.bool] rfl)).run (locals 4 34,populated) =
 (.ok (.val (.bool true)),(locals 4 34,populated)) := by rfl

/-- Logical calldata-reference length does not manufacture absent bytes. -/
theorem missing_input (p : Roadmap.Pipeline) :
 (evalE (global p) (F callPrefix) 2 (decode [.bool] rfl)).run (locals 4 32,populated) =
 (.error (.revert []),(locals 4 32,populated)) := by rfl

theorem exhausted (p : Roadmap.Pipeline) :
 (evalE (global p) (F (data 300)) 1 (decode [.int u8] rfl)).run (locals 4 32,populated) =
 (.error .timeout,(locals 4 32,populated)) := by rfl

def bytesData : Roadmap.Bytes := abiLayout [(true,[0,255])]
def allocated := populated.heap.alloc ⟨.bytes .memory,.bytes [0,255]⟩

theorem bytes_allocates (p : Roadmap.Pipeline) :
 (evalE (global p) (F bytesData) 2 (decode [.bytes .memory] rfl)).run
  (locals 0 bytesData.length,populated) =
 (.ok (.val (.memRef rfl allocated.2)),
  (locals 0 bytesData.length,{populated with heap := allocated.1})) := by rfl

theorem older_alias : allocated.1.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
 allocated.2 = 1 := ⟨rfl,rfl⟩

def hugeLength : Roadmap.Bytes := wordBytes (toWord 32) ++ wordBytes (toWord (2^64))

theorem allocation_panic_before_payload (p : Roadmap.Pipeline) :
 (evalE (global p) (F hugeLength) 2 (decode [.bytes .memory] rfl)).run
  (locals 0 64,populated) =
 (.error (.revert (panicData .alloc)),(locals 0 64,populated)) := by rfl

theorem missing_length (p : Roadmap.Pipeline) :
 (evalE (global p) (F (wordBytes (toWord 32))) 2 (decode [.bytes .memory] rfl)).run
  (locals 0 32,populated) =
 (.error (.revert []),(locals 0 32,populated)) := by rfl

theorem truncated_payload (p : Roadmap.Pipeline) :
 (evalE (global p) (F (bytesData.take 65)) 2 (decode [.bytes .memory] rfl)).run
  (locals 0 65,populated) =
 (.error (.revert []),(locals 0 65,populated)) := by rfl

/-- Lossless test-only byte rendering, not an encoder or decoder. -/
def render (bytes : Roadmap.Bytes) : String :=
 "[" ++ String.intercalate "," (bytes.map (fun b => toString b.toNat)) ++ "]"
#eval String.intercalate "\n" ([data 7,data 300,data 2,data 1,bytesData,hugeLength,
 wordBytes (toWord 32),bytesData.take 65].map render)

#print axioms allocation_panic_before_payload
#print axioms missing_length
#print axioms truncated_payload
#print axioms bytes_ok
#print axioms arm
#print axioms local_ok
#print axioms local_run
#print axioms success
#print axioms dirty_uint
#print axioms dirty_bool
#print axioms short_head
#print axioms trailing_accepted
#print axioms missing_input
#print axioms exhausted
#print axioms bytes_allocates
#print axioms older_alias
end Solidity.Lowering.V08.LiteralFailureCalldataDecodeControls
