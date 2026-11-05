import Solidity.Lowering.V08.LiteralFailureLocatedFields
import Solidity.Lowering.V08.LiteralFailureCalldataCopyControls
namespace Solidity.Lowering.V08.LiteralFailureLocatedFieldsControls
open Solidity Source
open LiteralFailureLocatedFields
abbrev E := LiteralFailureCalldataCopyControls.environment
abbrev frame := LiteralFailureCalldataCopyControls.frame
abbrev state := LiteralFailureCalldataCopyControls.state
abbrev global := LiteralFailureCalldataCopyControls.global

def types : RCtx := [.string .memory,.bytes .calldata,.bool,.bytes .memory,.string .calldata,.int IntTy.u256,.bool,.string .memory]
def context : RCtx := types++[.bytes .memory,.bool]
def locals (address o n q m : Nat) (flag : Bool) (w : Roadmap.Word) : Locals E.layout context :=
 .cons (.memRef rfl address) (.cons (.cdRef rfl o n) (.cons (.bool flag) (.cons (.memRef rfl 0)
  (.cons (.cdRef rfl q m) (.cons (SourceEnvironment.sourceWord w) (.cons (.bool (!flag))
   (.cons (.memRef rfl 1) (.cons (.memRef rfl 0) (.cons (.bool true) .nil)))))))))
def values (address o n q m : Nat) (flag : Bool) (w : Roadmap.Word) : Source.Vals E.layout types :=
 .cons (.memRef rfl address) (.cons (.cdRef rfl o n) (.cons (.bool flag) (.cons (.memRef rfl 0)
  (.cons (.cdRef rfl q m) (.cons (SourceEnvironment.sourceWord w) (.cons (.bool (!flag)) (.cons (.memRef rfl 1) .nil)))))))
def arguments : RArgs E context types := .cons (.local .here) (.cons (.local (.there .here)) (.cons (.local (.there (.there .here))) (.cons (.local (.there (.there (.there .here)))) (.cons (.local (.there (.there (.there (.there .here))))) (.cons (.local (.there (.there (.there (.there (.there .here)))))) (.cons (.local (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.local (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.nil))))))))
theorem lookups (address o n q m : Nat) (flag : Bool) (w : Roadmap.Word) :
 LiteralFailureMixedExpression.LocalArgs (locals address o n q m flag w) arguments (values address o n q m flag w) :=
 .cons .here ( .cons (.there .here) ( .cons (.there (.there .here)) ( .cons (.there (.there (.there .here))) ( .cons (.there (.there (.there (.there .here)))) ( .cons (.there (.there (.there (.there (.there .here))))) ( .cons (.there (.there (.there (.there (.there (.there .here)))))) ( .cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.nil))))))))
def shapes : List AbiEntry.Shape := [.bytes,.bytes,.word .bool,.bytes,.bytes,.word (.uint 256),.word .bool,.bytes]
def encoded (data text : Roadmap.Bytes) (o n q m : Nat) (flag : Bool) (w : Roadmap.Word) : AbiEntry.Vals shapes :=
 .cons (.bytes text) (.cons (.bytes ((data.drop o).take n)) (.cons (.word (BoolErrorAbi.word flag))
  (.cons (.bytes [9,7]) (.cons (.bytes ((data.drop q).take m))
   (.cons (.word (LiteralFailureDynamicError.abiWord w)) (.cons (.word (BoolErrorAbi.word (!flag))) (.cons (.bytes text) .nil)))))))

theorem fields (data text : Roadmap.Bytes) (o n q m : Nat) (flag : Bool) (w : Roadmap.Word) :
 Fields (frame data) (state text) (values 1 o n q m flag w) (encoded data text o n q m flag w) :=
 .cons (.known (.string 1 text rfl .nil))
  (.cons (.calldataBytes o n) (.cons (.known (.boolean flag .nil))
   (.cons (.known (.bytes 0 [9,7] (.inl rfl) .nil)) (.cons (.calldataString q m)
    (.cons (.known (.uint w .nil)) (.cons (.known (.boolean (!flag) .nil))
     (.cons (.known (.string 1 text rfl .nil)) .nil)))))))
def expression : RExpr E context (.bytes .memory) := .abiEncode .encode arguments

theorem actual (p : Roadmap.Pipeline) (data text : Roadmap.Bytes) (o n q m : Nat) (flag : Bool) (w : Roadmap.Word) :
 (evalE (global p) (frame data) 12 expression).run (locals 1 o n q m flag w,state text)=
 (.ok (.val (.memRef rfl 3)),(locals 1 o n q m flag w,SourceKeccak.afterLiteral (state text)
  (AbiEntry.encodeArgs (encoded data text o n q m flag w)))) :=
 expression_run (global p) (frame data) 0 _ _ (lookups 1 o n q m flag w) (fields data text o n q m flag w)

theorem retained (p : Roadmap.Pipeline) (data text : Roadmap.Bytes) (o n q m : Nat) (flag : Bool) (w : Roadmap.Word) :
 Fields (frame data) ((evalE (global p) (frame data) 12 expression).run (locals 1 o n q m flag w,state text)).2.2
 (values 1 o n q m flag w) (encoded data text o n q m flag w) := by
 rw [actual]
 exact fields_after (frame data) (state text) _ (fields data text o n q m flag w)

theorem encoder_pure (data text : Roadmap.Bytes) (o n q m : Nat) (flag : Bool) (w : Roadmap.Word) :
 (encodeVals (frame data) 0 false (values 1 o n q m flag w).toR : EM E context _).run
 (locals 1 o n q m flag w,state text)=
 (.ok (AbiEntry.encodeArgs (encoded data text o n q m flag w)),(locals 1 o n q m flag w,state text)) :=
 encoding_run (frame data) 0 _ _ (fields data text o n q m flag w)

theorem dangling (data text : Roadmap.Bytes) :
 (evalE (global .legacy) (frame data) 12 expression).run (locals 99 0 0 0 0 false ⟨300,by decide +kernel⟩,state text)=
 (.error (.stuck "dangling memory reference"),(locals 99 0 0 0 0 false ⟨300,by decide +kernel⟩,state text)) := rfl

theorem timeout (data text : Roadmap.Bytes) :
 (evalE (global .legacy) (frame data) 9 expression).run (locals 1 0 0 0 0 false ⟨300,by decide +kernel⟩,state text)=
 (.error .timeout,(locals 1 0 0 0 0 false ⟨300,by decide +kernel⟩,state text)) := rfl

theorem bool_wire_equal :
 AbiEntry.encodeArgs (.cons (.word (BoolErrorAbi.word true)) .nil)=
 AbiEntry.encodeArgs (.cons (.word (LiteralFailureDynamicError.abiWord ⟨1,by decide +kernel⟩)) .nil) := rfl

theorem wrong_flag :
 AbiEntry.encodeArgs (encoded [0,255] [128] 0 2 0 2 true ⟨300,by decide +kernel⟩)≠
 AbiEntry.encodeArgs (encoded [0,255] [128] 0 2 0 2 false ⟨300,by decide +kernel⟩) := by decide +kernel

def render := LiteralFailureCalldataCopyControls.render
def observe (p : Roadmap.Pipeline) (data text : Roadmap.Bytes) (o n q m : Nat) (flag : Bool) (w : Roadmap.Word) : String :=
 match (evalE (global p) (frame data) 12 expression).run (locals 1 o n q m flag w,state text) with
 | (.ok (.val (.memRef _ address)),(_,after)) =>
  match after.heap.get address with
  | some ⟨.bytes .memory,.bytes bs⟩ => "{\"pointer\":"++toString address++",\"cursor\":"++toString after.heap.next++",\"bytes\":"++render bs++"}"
  | _ => "null"
 | _ => "null"
def suite (p : Roadmap.Pipeline) := "["++String.intercalate "," [
 observe p [] [] 0 0 0 0 false ⟨0,by decide +kernel⟩,
 observe p [99,0,255,128,7] [195,169] 1 3 1 3 true ⟨300,by decide +kernel⟩,
 observe p (List.replicate 31 255++[0]++List.replicate 33 128) (List.replicate 31 0) 0 31 32 33 false ⟨2^256-1,by decide +kernel⟩,
 observe p [0,255,128] (List.replicate 32 0) 1 33 99 31 true ⟨2^255,by decide +kernel⟩,
 observe p ([0]++List.replicate 33 128++[255]) (List.replicate 33 128) 1 33 1 33 false ⟨42,by decide +kernel⟩,
 observe p ([0]++List.replicate 32 0++[255]) [0,255] 1 32 32 2 true ⟨42,by decide +kernel⟩]++"]"
#eval "LOCATED_FIELDS_LEGACY="++suite .legacy
#eval "LOCATED_FIELDS_VIAIR="++suite .viaIR
#print axioms one_witness
#print axioms parts_witness
#print axioms go_agreement
#print axioms head_extent
#print axioms encoding_run
#print axioms encodingAt
#print axioms expression_run
#print axioms of_memory_fields
#print axioms fields_after
#print axioms bool_not_uint
#print axioms lookups
#print axioms fields
#print axioms actual
#print axioms retained
#print axioms encoder_pure
#print axioms dangling
#print axioms timeout
#print axioms bool_wire_equal
#print axioms wrong_flag
end Solidity.Lowering.V08.LiteralFailureLocatedFieldsControls
