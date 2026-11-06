import Solidity.Lowering.V08.LiteralFailureCalldataPrefix
import Solidity.Lowering.V08.LiteralFailureCalldataCopyControls
namespace Solidity.Lowering.V08.LiteralFailureCalldataPrefixControls
open Solidity Source
open LiteralFailureCalldataPrefix
abbrev E := LiteralFailureCalldataCopyControls.environment
abbrev frame := LiteralFailureCalldataCopyControls.frame
abbrev state := LiteralFailureCalldataCopyControls.state
abbrev global := LiteralFailureCalldataCopyControls.global

def types : RCtx := [.bytes .calldata,.string .calldata,.int IntTy.u256,.bytes .memory]
def context : RCtx := types++[.bool]
def locals (o n q m : Nat) (w : Roadmap.Word) : Locals E.layout context :=
 .cons (.cdRef rfl o n) (.cons (.cdRef rfl q m)
  (.cons (SourceEnvironment.sourceWord w) (.cons (.memRef rfl 0) (.cons (.bool true) .nil))))
def source (o n q m : Nat) (w : Roadmap.Word) : Source.Vals E.layout types :=
 .cons (.cdRef rfl o n) (.cons (.cdRef rfl q m)
  (.cons (SourceEnvironment.sourceWord w) (.cons (.memRef rfl 0) .nil)))
def arguments : RArgs E context types :=
 .cons (.local .here) (.cons (.local (.there .here))
  (.cons (.local (.there (.there .here))) (.cons (.local (.there (.there (.there .here)))) .nil)))
theorem lookups (o n q m : Nat) (w : Roadmap.Word) :
 LiteralFailureMixedExpression.LocalArgs (locals o n q m w) arguments (source o n q m w) :=
 .cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))
def encoded (data : Roadmap.Bytes) (o n q m : Nat) (w : Roadmap.Word) :
 AbiEntry.Vals [.bytes,.bytes,.word (.uint 256),.bytes] :=
 .cons (.bytes ((data.drop o).take n)) (.cons (.bytes ((data.drop q).take m))
  (.cons (.word (LiteralFailureDynamicError.abiWord w)) (.cons (.bytes [9,7]) .nil)))
theorem fields (data text : Roadmap.Bytes) (o n q m : Nat) (w : Roadmap.Word) :
 Located (frame data) (state text) (source o n q m w) (encoded data o n q m w)
 [(true,(data.drop o).take n),(true,(data.drop q).take m),(false,wordBytes w),(true,[9,7])] :=
 .bytes o n (.string q m (.base (.uint w (.bytes 0 [9,7] (.inl rfl) .nil))))
def expression : RExpr E context (.bytes .memory) := .abiEncode .encode arguments

theorem actual (p : Roadmap.Pipeline) (data text : Roadmap.Bytes) (o n q m : Nat) (w : Roadmap.Word) :
 (evalE (global p) (frame data) 8 expression).run (locals o n q m w,state text)=
 (.ok (.val (.memRef rfl 3)),
  (locals o n q m w,SourceKeccak.afterLiteral (state text) (AbiEntry.encodeArgs (encoded data o n q m w)))) :=
 expression_run (global p) (frame data) 0 _ _ (lookups o n q m w) (fields data text o n q m w)

theorem timeout (data text : Roadmap.Bytes) (o n q m : Nat) (w : Roadmap.Word) :
 (evalE (global .legacy) (frame data) 1 expression).run (locals o n q m w,state text)=
 (.error .timeout,(locals o n q m w,state text)) := rfl

theorem no_argument_allocation (data text : Roadmap.Bytes) (o n q m : Nat) (w : Roadmap.Word) :
 (encodeVals (frame data) 0 false (source o n q m w).toR : EM E context _).run
 (locals o n q m w,state text)=
 (.ok (AbiEntry.encodeArgs (encoded data o n q m w)),(locals o n q m w,state text)) :=
 encoding_run (frame data) 0 _ _ (fields data text o n q m w)

theorem old_object (data text : Roadmap.Bytes) (o n q m : Nat) (w : Roadmap.Word) :
 (SourceKeccak.afterLiteral (state text) (AbiEntry.encodeArgs (encoded data o n q m w))).heap.get 0=
 some ⟨.bytes .memory,.bytes [9,7]⟩ := LiteralFailureMixedExpression.old_object _ _ _ _ rfl

theorem result_cursor (p : Roadmap.Pipeline) (data text : Roadmap.Bytes) (o n q m : Nat) (w : Roadmap.Word) :
 ((evalE (global p) (frame data) 8 expression).run (locals o n q m w,state text)).2.2.heap.next=4 := by
 rw [actual]
 rfl

theorem first_head :
 (AbiEntry.encodeArgs (encoded [10,20] 0 1 1 1 ⟨300,by decide +kernel⟩)).take 32=AbiEntry.wordBytes 128 := by
 decide +kernel

theorem wrong_head :
 (AbiEntry.encodeArgs (encoded [10,20] 0 1 1 1 ⟨300,by decide +kernel⟩)).take 32≠AbiEntry.wordBytes 32 := by
 decide +kernel

theorem swapped_slices :
 AbiEntry.encodeArgs (encoded [10,20] 0 1 1 1 ⟨300,by decide +kernel⟩)≠
 AbiEntry.encodeArgs (encoded [10,20] 1 1 0 1 ⟨300,by decide +kernel⟩) := by
 decide +kernel

theorem wrong_frame :
 AbiEntry.encodeArgs (encoded [10,20] 0 1 1 1 ⟨300,by decide +kernel⟩)≠
 AbiEntry.encodeArgs (encoded [10,21] 0 1 1 1 ⟨300,by decide +kernel⟩) := by
 decide +kernel

def render := LiteralFailureCalldataCopyControls.render
def observe (p : Roadmap.Pipeline) (data : Roadmap.Bytes) (o n q m : Nat) (w : Roadmap.Word) : String :=
 match (evalE (global p) (frame data) 8 expression).run (locals o n q m w,state [0,255]) with
 | (.ok (.val (.memRef _ address)),(_,after)) =>
  match after.heap.get address with
  | some ⟨.bytes .memory,.bytes packet⟩ =>
   "{\"pointer\":"++toString address++",\"cursor\":"++toString after.heap.next++",\"bytes\":"++render packet++"}"
  | _ => "null"
 | _ => "null"
def suite (p : Roadmap.Pipeline) := "["++String.intercalate "," [
 observe p [] 0 0 0 0 ⟨0,by decide +kernel⟩,
 observe p [99,0,255,128,7] 1 3 1 3 ⟨300,by decide +kernel⟩,
 observe p (List.replicate 31 255++[0]++List.replicate 33 128) 0 31 32 33 ⟨2^256-1,by decide +kernel⟩,
 observe p [0,255,128] 1 33 99 31 ⟨2^255,by decide +kernel⟩,
 observe p (List.replicate 32 0++[255]) 0 32 31 2 ⟨42,by decide +kernel⟩]++"]"
#eval "CALLDATA_PREFIX_LEGACY="++suite .legacy
#eval "CALLDATA_PREFIX_VIAIR="++suite .viaIR
#print axioms parts_run
#print axioms go_agreement
#print axioms head_extent
#print axioms encoding_run
#print axioms expression_run
#print axioms encodingAt
#print axioms lookups
#print axioms fields
#print axioms actual
#print axioms timeout
#print axioms no_argument_allocation
#print axioms old_object
#print axioms result_cursor
#print axioms first_head
#print axioms wrong_head
#print axioms swapped_slices
#print axioms wrong_frame
end Solidity.Lowering.V08.LiteralFailureCalldataPrefixControls
