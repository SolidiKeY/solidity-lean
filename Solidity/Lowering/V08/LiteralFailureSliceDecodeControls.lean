import Solidity.Lowering.V08.LiteralFailureSliceDecode
import Solidity.Lowering.V08.LiteralFailureCalldataDecodeControls

namespace Solidity.Lowering.V08.LiteralFailureSliceDecodeControls
open Solidity Source LiteralFailureSliceDecode SourceCustomErrorControls
open LiteralFailureCalldataDecodeControls

def ctx : RCtx := .bytes .calldata :: .int IntTy.u256 :: .int IntTy.u256 :: SourceExternalPhaseControls.ctx

def caller (off len : Nat) (start stop : Roadmap.Word) : Locals E.layout ctx :=
 .cons (.cdRef rfl off len) (.cons (SourceEnvironment.sourceWord start)
  (.cons (SourceEnvironment.sourceWord stop) SourceExternalPhaseControls.caller))

def expression (types : List STy) (admitted : types.all (STy.decodable E) = true)
 (toEnd : Bool) : RExpr E ctx (STy.ret types) :=
 .abiDecode (.slice (.local .here) rfl (.local (.there .here)) rfl
  (.local (.there (.there .here))) rfl toEnd) rfl admitted

def a : Roadmap.Word := ⟨4,by decide +kernel⟩
def b : Roadmap.Word := ⟨36,by decide +kernel⟩
def zero : Roadmap.Word := ⟨0,by decide +kernel⟩
def wrong : Roadmap.Word := ⟨37,by decide +kernel⟩

theorem sliced_success (p : Roadmap.Pipeline) :
 (evalE (global p) (F (data 7)) 3 (expression [.int u8] rfl false)).run
  (caller 0 38 a b,populated) =
 (.ok (.val (.int 7 (by decide +kernel))),(caller 0 38 a b,populated)) := by rfl

theorem sliced_dirty (p : Roadmap.Pipeline) :
 (evalE (global p) (F (data 300)) 3 (expression [.int u8] rfl false)).run
  (caller 0 38 a b,populated) =
 (.error (.revert []),(caller 0 38 a b,populated)) := by rfl

theorem reversed (p : Roadmap.Pipeline) :
 (evalE (global p) (F (data 7)) 3 (expression [.int u8] rfl false)).run
  (caller 0 38 b a,populated) =
 (.error (.revert []),(caller 0 38 b a,populated)) := by rfl

theorem outside_reference (p : Roadmap.Pipeline) :
 (evalE (global p) (F (data 7)) 3 (expression [.int u8] rfl false)).run
  (caller 0 36 a wrong,populated) =
 (.error (.revert []),(caller 0 36 a wrong,populated)) := by rfl

/-- Absent end ignores the end VALUE after evaluating its local expression. -/
theorem to_end (p : Roadmap.Pipeline) :
 (evalE (global p) (F (data 7)) 3 (expression [.int u8] rfl true)).run
  (caller 0 36 a zero,populated) =
 (.ok (.val (.int 7 (by decide +kernel))),(caller 0 36 a zero,populated)) := by rfl

theorem short_slice (p : Roadmap.Pipeline) :
 (evalE (global p) (F (data 7)) 3 (expression [.int u8] rfl false)).run
  (caller 0 38 a ⟨35,by decide +kernel⟩,populated) =
 (.error (.revert []),(caller 0 38 a ⟨35,by decide +kernel⟩,populated)) := by rfl

theorem fuel_before_bounds (p : Roadmap.Pipeline) :
 (evalE (global p) (F (data 7)) 2 (expression [.int u8] rfl false)).run
  (caller 0 38 b a,populated) =
 (.error .timeout,(caller 0 38 b a,populated)) := by rfl

/-- Slice reference is nonzero and output allocates a distinct memory object. -/
theorem sliced_bytes_allocates (p : Roadmap.Pipeline) :
 (evalE (global p) (F (callPrefix ++ bytesData)) 3
  (expression [.bytes .memory] rfl true)).run
  (caller 0 (4+bytesData.length) a zero,populated) =
 (.ok (.val (.memRef rfl allocated.2)),
  (caller 0 (4+bytesData.length) a zero,{populated with heap := allocated.1})) := by rfl

/-- Applied generic progress law for the actual populated caller context. -/
def generic_client (p : Roadmap.Pipeline) (n : Nat) {H : HeapTy} :=
 slice_ok (H:=H) (global p) (F (data 7)) n
  (.here : Source.Idx ctx (.bytes .calldata)) (.there .here) rfl
  (.there (.there .here)) rfl false (types:=[.int u8]) rfl

#eval String.intercalate "\n" ([data 7,data 300,callPrefix ++ bytesData].map render)
#eval "[" ++ String.intercalate "," ([a.val,b.val,wrong.val,zero.val,bytesData.length,allocated.2].map toString) ++ "]"
#print axioms generic_client
#print axioms slice_ok
#print axioms sliced_success
#print axioms sliced_dirty
#print axioms reversed
#print axioms outside_reference
#print axioms to_end
#print axioms short_slice
#print axioms fuel_before_bounds
#print axioms sliced_bytes_allocates
end Solidity.Lowering.V08.LiteralFailureSliceDecodeControls
