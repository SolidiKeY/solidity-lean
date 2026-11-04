import Solidity.Lowering.V08.LiteralFailureSliceEncoding
import Solidity.Lowering.V08.LiteralFailureCalldataPrefixControls
namespace Solidity.Lowering.V08.LiteralFailureSliceEncodingControls
open Solidity Source
open LiteralFailureSliceEncoding
abbrev E := LiteralFailureCalldataPrefixControls.E
abbrev frame := LiteralFailureCalldataPrefixControls.frame
abbrev state := LiteralFailureCalldataPrefixControls.state
abbrev global := LiteralFailureCalldataPrefixControls.global

def types : RCtx := [.string .calldata,.int IntTy.u256,.bytes .memory]
def olderTypes : RCtx := types++[.bool]
def older (q m : Nat) (w : Roadmap.Word) : Locals E.layout olderTypes :=
 .cons (.cdRef rfl q m) (.cons (SourceEnvironment.sourceWord w) (.cons (.memRef rfl 0) (.cons (.bool true) .nil)))
def values (q m : Nat) (w : Roadmap.Word) : Source.Vals E.layout types :=
 .cons (.cdRef rfl q m) (.cons (SourceEnvironment.sourceWord w) (.cons (.memRef rfl 0) .nil))
def tail : RArgs E (context olderTypes) types :=
 .cons (.local (.there (.there (.there .here))))
  (.cons (.local (.there (.there (.there (.there .here)))))
   (.cons (.local (.there (.there (.there (.there (.there .here)))))) .nil))
theorem lookups (off len : Nat) (start stop : Roadmap.Word) (q m : Nat) (w : Roadmap.Word) :
 LiteralFailureMixedExpression.LocalArgs (caller off len start stop (older q m w)) tail (values q m w) :=
 .cons (.there (.there (.there .here)))
  (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil))
def encodedTail (data : Roadmap.Bytes) (q m : Nat) (w : Roadmap.Word) :
 AbiEntry.Vals [.bytes,.word (.uint 256),.bytes] :=
 .cons (.bytes ((data.drop q).take m)) (.cons (.word (LiteralFailureDynamicError.abiWord w)) (.cons (.bytes [9,7]) .nil))
theorem fields (data text : Roadmap.Bytes) (q m : Nat) (w : Roadmap.Word) :
 LiteralFailureCalldataPrefix.Located (frame data) (state text) (values q m w) (encodedTail data q m w)
 [(true,(data.drop q).take m),(false,wordBytes w),(true,[9,7])] :=
 .string q m (.base (.uint w (.bytes 0 [9,7] (.inl rfl) .nil)))
def expression : RExpr E (context olderTypes) (.bytes .memory) := .abiEncode .encode (arguments tail)

theorem actual (p : Roadmap.Pipeline) (data text : Roadmap.Bytes) (off len : Nat)
 (start stop : Roadmap.Word) (ordered : start.val≤stop.val) (bounded : stop.val≤len)
 (q m : Nat) (w : Roadmap.Word) :
 (evalE (global p) (frame data) 8 expression).run (caller off len start stop (older q m w),state text)=
 (.ok (.val (.memRef rfl 3)),(caller off len start stop (older q m w),
  SourceKeccak.afterLiteral (state text)
   (AbiEntry.encodeArgs (LiteralFailureCalldataPrefixControls.encoded data
    (off+start.val) (stop.val-start.val) q m w)))) :=
 expression_run (global p) (frame data) 0 off len start stop ordered bounded _ _
 (lookups off len start stop q m w) (fields data text q m w)

theorem invalid (p : Roadmap.Pipeline) (data text : Roadmap.Bytes) (off len : Nat)
 (start stop : Roadmap.Word) (wrong : stop.val<start.val ∨ len<stop.val)
 (q m : Nat) (w : Roadmap.Word) :
 (evalE (global p) (frame data) 8 expression).run (caller off len start stop (older q m w),state text)=
 (.error (.revert []),(caller off len start stop (older q m w),state text)) :=
 expression_revert (global p) (frame data) 0 off len start stop wrong _ _ tail

def effectTail : RArgs E (context olderTypes) [.bytes .memory] := .cons (.abiEncode .encode .nil) .nil
def effectExpression : RExpr E (context olderTypes) (.bytes .memory) := .abiEncode .encode (arguments effectTail)
theorem skipped_effect (data text : Roadmap.Bytes) :
 (evalE (global .legacy) (frame data) 6 effectExpression).run
 (caller 0 1 ⟨1,by decide +kernel⟩ ⟨0,by decide +kernel⟩ (older 0 0 ⟨300,by decide +kernel⟩),state text)=
 (.error (.revert []),(caller 0 1 ⟨1,by decide +kernel⟩ ⟨0,by decide +kernel⟩ (older 0 0 ⟨300,by decide +kernel⟩),state text)) :=
 expression_revert (global .legacy) (frame data) 0 0 1 _ _ (.inl (by decide +kernel)) _ _ effectTail

theorem reached_effect :
 ((evalE (global .legacy) (frame [0,255]) 6 effectExpression).run
 (caller 0 2 ⟨0,by decide +kernel⟩ ⟨1,by decide +kernel⟩ (older 0 0 ⟨300,by decide +kernel⟩),state [])).2.2.heap.next=5 := by
 rfl

theorem exhausted (data text : Roadmap.Bytes) :
 (evalE (global .legacy) (frame data) 2 expression).run
 (caller 0 1 ⟨1,by decide +kernel⟩ ⟨0,by decide +kernel⟩ (older 0 0 ⟨0,by decide +kernel⟩),state text)=
 (.error .timeout,(caller 0 1 ⟨1,by decide +kernel⟩ ⟨0,by decide +kernel⟩ (older 0 0 ⟨0,by decide +kernel⟩),state text)) := rfl

theorem wrong_relative_offset :
 AbiEntry.encodeArgs (LiteralFailureCalldataPrefixControls.encoded [9,10,20] 2 1 0 1 ⟨300,by decide +kernel⟩)≠
 AbiEntry.encodeArgs (LiteralFailureCalldataPrefixControls.encoded [9,10,20] 1 1 0 1 ⟨300,by decide +kernel⟩) := by decide +kernel

def render := LiteralFailureCalldataCopyControls.render
def observe (p : Roadmap.Pipeline) (data : Roadmap.Bytes) (off len : Nat)
 (start stop : Roadmap.Word) (q m : Nat) (w : Roadmap.Word) : String :=
 match (evalE (global p) (frame data) 8 expression).run (caller off len start stop (older q m w),state [0,255]) with
 | (.ok (.val (.memRef _ address)),(_,after)) =>
  match after.heap.get address with
  | some ⟨.bytes .memory,.bytes packet⟩ =>
   "{\"pointer\":"++toString address++",\"cursor\":"++toString after.heap.next++",\"bytes\":"++render packet++"}"
  | _ => "null"
 | (.error (.revert packet),(_,after)) => "{\"revert\":"++render packet++",\"cursor\":"++toString after.heap.next++"}"
 | _ => "null"
def suite (p : Roadmap.Pipeline) := "["++String.intercalate "," [
 observe p [] 0 0 ⟨0,by decide +kernel⟩ ⟨0,by decide +kernel⟩ 0 0 ⟨0,by decide +kernel⟩,
 observe p [99,0,255,128,7] 1 4 ⟨1,by decide +kernel⟩ ⟨3,by decide +kernel⟩ 2 2 ⟨300,by decide +kernel⟩,
 observe p ([0]++List.replicate 31 255++[0]++List.replicate 33 128) 1 65 ⟨0,by decide +kernel⟩ ⟨31,by decide +kernel⟩ 33 33 ⟨2^256-1,by decide +kernel⟩,
 observe p [0,255,128] 1 33 ⟨0,by decide +kernel⟩ ⟨33,by decide +kernel⟩ 99 31 ⟨2^255,by decide +kernel⟩,
 observe p [10,20] 0 2 ⟨2,by decide +kernel⟩ ⟨1,by decide +kernel⟩ 0 1 ⟨42,by decide +kernel⟩,
 observe p [10,20] 0 1 ⟨0,by decide +kernel⟩ ⟨2,by decide +kernel⟩ 0 1 ⟨42,by decide +kernel⟩]++"]"
#eval "SLICE_ENCODING_LEGACY="++suite .legacy
#eval "SLICE_ENCODING_VIAIR="++suite .viaIR
#print axioms arguments_run
#print axioms expression_run
#print axioms arguments_revert
#print axioms expression_revert
#print axioms lookups
#print axioms fields
#print axioms actual
#print axioms invalid
#print axioms skipped_effect
#print axioms reached_effect
#print axioms exhausted
#print axioms wrong_relative_offset
end Solidity.Lowering.V08.LiteralFailureSliceEncodingControls
