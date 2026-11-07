import Solidity.Lowering.V08.LiteralFailureNestedSlice
import Solidity.Lowering.V08.LiteralFailureSliceEncodingControls
namespace Solidity.Lowering.V08.LiteralFailureNestedSliceControls
open Solidity Source
open LiteralFailureNestedSlice
abbrev E := LiteralFailureSliceEncodingControls.E
abbrev frame := LiteralFailureSliceEncodingControls.frame
abbrev state := LiteralFailureSliceEncodingControls.state
abbrev global := LiteralFailureSliceEncodingControls.global
abbrev olderTypes := LiteralFailureSliceEncodingControls.olderTypes
abbrev older := LiteralFailureSliceEncodingControls.older
abbrev types := LiteralFailureSliceEncodingControls.types
abbrev values := LiteralFailureSliceEncodingControls.values
abbrev encodedTail := LiteralFailureSliceEncodingControls.encodedTail

def tail : RArgs E (context olderTypes) types :=
 .cons (.local (.there (.there (.there (.there (.there .here))))))
  (.cons (.local (.there (.there (.there (.there (.there (.there .here)))))))
   (.cons (.local (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil))
theorem lookups (off len : Nat) (s e u v : Roadmap.Word) (q m : Nat) (w : Roadmap.Word) :
 LiteralFailureMixedExpression.LocalArgs (caller off len s e u v (older q m w)) tail (values q m w) :=
 .cons (.there (.there (.there (.there (.there .here)))))
  (.cons (.there (.there (.there (.there (.there (.there .here))))))
   (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil))
def packet (data : Roadmap.Bytes) (off : Nat) (s u v : Roadmap.Word) (q m : Nat) (w : Roadmap.Word) :=
 AbiEntry.encodeArgs (LiteralFailureCalldataPrefixControls.encoded data
  (off+s.val+u.val) (v.val-u.val) q m w)
def encodedExpression : RExpr E (context olderTypes) (.bytes .memory) := .abiEncode .encode (arguments tail)

theorem actual (p : Roadmap.Pipeline) (data text : Roadmap.Bytes) (off len : Nat)
 (s e u v : Roadmap.Word) (ordered : s.val≤e.val) (bounded : e.val≤len)
 (ordered2 : u.val≤v.val) (bounded2 : v.val≤e.val-s.val) (q m : Nat) (w : Roadmap.Word) :
 (evalE (global p) (frame data) 8 encodedExpression).run (caller off len s e u v (older q m w),state text)=
 (.ok (.val (.memRef rfl 3)),(caller off len s e u v (older q m w),SourceKeccak.afterLiteral (state text) (packet data off s u v q m w))) :=
 encode_run (global p) (frame data) 0 off len s e u v ordered bounded ordered2 bounded2 _ _
 (lookups off len s e u v q m w) (LiteralFailureSliceEncodingControls.fields data text q m w)

theorem invalid (p : Roadmap.Pipeline) (data text : Roadmap.Bytes) (off len : Nat)
 (s e u v : Roadmap.Word) (wrong : (e.val<s.val ∨ len<e.val) ∨ (v.val<u.val ∨ e.val-s.val<v.val))
 (q m : Nat) (w : Roadmap.Word) :
 (evalE (global p) (frame data) 8 encodedExpression).run (caller off len s e u v (older q m w),state text)=
 (.error (.revert []),(caller off len s e u v (older q m w),state text)) :=
 encode_revert (global p) (frame data) 0 off len s e u v wrong _ _ tail

theorem old_alias (p : Roadmap.Pipeline) (data text : Roadmap.Bytes) (off len : Nat)
 (s e u v : Roadmap.Word) (ordered : s.val≤e.val) (bounded : e.val≤len)
 (ordered2 : u.val≤v.val) (bounded2 : v.val≤e.val-s.val) (q m : Nat) (w : Roadmap.Word) :
 ((evalE (global p) (frame data) 8 encodedExpression).run
  (caller off len s e u v (older q m w),state text)).2.2.heap.get 0=some ⟨.bytes .memory,.bytes [9,7]⟩ := by
 rw [actual p data text off len s e u v ordered bounded ordered2 bounded2 q m w]
 exact LiteralFailureMixedExpression.old_object _ _ _ _ rfl

theorem timeout (data text : Roadmap.Bytes) :
 (evalE (global .legacy) (frame data) 3 encodedExpression).run
 (caller 0 1 ⟨1,by decide +kernel⟩ ⟨0,by decide +kernel⟩ ⟨0,by decide +kernel⟩ ⟨0,by decide +kernel⟩ (older 0 0 ⟨0,by decide +kernel⟩),state text)=
 (.error .timeout,(caller 0 1 ⟨1,by decide +kernel⟩ ⟨0,by decide +kernel⟩ ⟨0,by decide +kernel⟩ ⟨0,by decide +kernel⟩ (older 0 0 ⟨0,by decide +kernel⟩),state text)) := rfl

theorem wrong_base : packet [9,10,20,30] 1 ⟨1,by decide +kernel⟩ ⟨1,by decide +kernel⟩ ⟨2,by decide +kernel⟩ 0 1 ⟨300,by decide +kernel⟩ ≠
 packet [9,10,20,30] 0 ⟨1,by decide +kernel⟩ ⟨1,by decide +kernel⟩ ⟨2,by decide +kernel⟩ 0 1 ⟨300,by decide +kernel⟩ := by decide +kernel

def render := LiteralFailureCalldataCopyControls.render
def observe (p : Roadmap.Pipeline) (data : Roadmap.Bytes) (off len : Nat)
 (s e u v : Roadmap.Word) (q m : Nat) (w : Roadmap.Word) : String :=
 match (evalE (global p) (frame data) 8 encodedExpression).run (caller off len s e u v (older q m w),state [0,255]) with
 | (.ok (.val (.memRef _ address)),(_,after)) =>
  match after.heap.get address with
  | some ⟨.bytes .memory,.bytes bs⟩ => "{\"pointer\":"++toString address++",\"cursor\":"++toString after.heap.next++",\"bytes\":"++render bs++"}"
  | _ => "null"
 | (.error (.revert bs),(_,after)) => "{\"revert\":"++render bs++",\"cursor\":"++toString after.heap.next++"}"
 | _ => "null"
def word (n : Nat) (h : n<2^256 := by decide +kernel) : Roadmap.Word := ⟨n,h⟩
def suite (p : Roadmap.Pipeline) := "["++String.intercalate "," [
 observe p [] 0 0 (word 0) (word 0) (word 0) (word 0) 0 0 (word 0),
 observe p [9,10,20,30,40] 1 4 (word 1) (word 4) (word 1) (word 2) 3 1 (word 300),
 observe p ([0]++List.replicate 31 255++[0]++List.replicate 33 128) 0 66 (word 1) (word 66) (word 31) (word 64) 32 33 (word (2^256-1)),
 observe p [0,255,128] 1 65 (word 1) (word 65) (word 0) (word 33) 99 31 (word (2^255)),
 observe p [10,20] 0 2 (word 2) (word 1) (word 0) (word 0) 0 1 (word 42),
 observe p [10,20] 0 1 (word 0) (word 2) (word 0) (word 0) 0 1 (word 42),
 observe p [10,20] 0 2 (word 0) (word 2) (word 2) (word 1) 0 1 (word 42),
 observe p [10,20] 0 2 (word 1) (word 2) (word 0) (word 2) 0 1 (word 42)]++"]"
#eval "NESTED_SLICE_LEGACY="++suite .legacy
#eval "NESTED_SLICE_VIAIR="++suite .viaIR
#print axioms after_first
#print axioms accepted
#print axioms first_revert
#print axioms second_revert
#print axioms arguments_run
#print axioms encode_run
#print axioms encode_revert
#print axioms lookups
#print axioms actual
#print axioms invalid
#print axioms old_alias
#print axioms timeout
#print axioms wrong_base
#print axioms flattened_bounds
end Solidity.Lowering.V08.LiteralFailureNestedSliceControls
