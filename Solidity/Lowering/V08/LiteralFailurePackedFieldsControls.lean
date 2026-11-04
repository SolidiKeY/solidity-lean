import Solidity.Lowering.V08.LiteralFailurePackedFields
import Solidity.Lowering.V08.LiteralFailureCopyEncodingControls
namespace Solidity.Lowering.V08.LiteralFailurePackedFieldsControls
open Solidity Source
open LiteralFailureCopySequenceControls
open LiteralFailurePackedFields

def parts (data : Roadmap.Bytes) (x y z : Bool) (o n q m r l : Nat) (w : Roadmap.Word) : List (Bool × Roadmap.Bytes) :=
 [(false,[if x then 1 else 0]),(true,(data.drop o).take n),(false,AbiEntry.wordBytes w.val),
 (false,[if y then 1 else 0]),(true,(data.drop q).take m),(true,(data.drop r).take l),(false,[if z then 1 else 0])]
def payload (data : Roadmap.Bytes) (x y z : Bool) (o n q m r l : Nat) (w : Roadmap.Word) :=
 (parts data x y z o n q m r l w).foldr (fun part tail=>part.2++tail) []

theorem pieces (data : Roadmap.Bytes) (x y z : Bool) (o n q m r l : Nat) (w : Roadmap.Word) :
 Pieces (encoded data x y z o n q m r l w) (parts data x y z o n q m r l w) :=
 .cons (.boolean x) (.cons (.bytes _) (.cons (.uint w) (.cons (.boolean y) (.cons (.bytes _) (.cons (.bytes _) (.cons (.boolean z) .nil))))))

theorem encoded_run (p : Roadmap.Pipeline) (data first second third : Roadmap.Bytes)
 (x y z : Bool) (o n q m r l : Nat) (w : Roadmap.Word) :
 (encodeVals (frame data) 11 true (values x y z w).toR : EM E context _).run
 (locals x y z o n q m r l w,final data first second third o n q m r l)=
 (.ok (payload data x y z o n q m r l w),(locals x y z o n q m r l w,final data first second third o n q m r l)) := by
 rcases encoding_run (frame data) 11 (locals x y z o n q m r l w) _
  (facts p data first second third x y z o n q m r l w).1 with ⟨actual,related,run⟩
 have equal := pieces_unique related (pieces data x y z o n q m r l w)
 cases equal
 exact run

def expression : RExpr E context (.bytes .memory) := .abiEncode .encodePacked (LiteralFailureCopyEncoding.expressions arguments)
def result (data first second third : Roadmap.Bytes) (x y z : Bool) (o n q m r l : Nat) (w : Roadmap.Word) :=
 SourceKeccak.afterLiteral (final data first second third o n q m r l) (payload data x y z o n q m r l w)

theorem actual_expression (p : Roadmap.Pipeline) (data first second third : Roadmap.Bytes)
 (x y z : Bool) (o n q m r l : Nat) (w : Roadmap.Word) :
 (evalE (global p) (frame data) 12 expression).run (locals x y z o n q m r l w,state first second third)=
 (.ok (.val (.memRef rfl 7)),(locals x y z o n q m r l w,result data first second third x y z o n q m r l w)) :=
 SourceAbi.execute (global p) (frame data) 11 true _ _ _ _ _ _ _ _ _
 (LiteralFailureCopyEncodingControls.arguments_actual p data first second third x y z o n q m r l w)
 (encoded_run p data first second third x y z o n q m r l w)

theorem applied (p : Roadmap.Pipeline) (data first second third : Roadmap.Bytes)
 (x y z : Bool) (o n q m r l : Nat) (w : Roadmap.Word) :
 ∃ (middle : St E) (ps : List (Bool × Roadmap.Bytes)),
 Pieces (encoded data x y z o n q m r l w) ps ∧
 (evalE (global p) (frame data) 12 expression).run (locals x y z o n q m r l w,state first second third)=
 (.ok (.val (.memRef rfl middle.heap.next)),
 (locals x y z o n q m r l w,SourceKeccak.afterLiteral middle (ps.foldr (fun part tail=>part.2++tail) []))) ∧
 middle.heap.next=7 ∧
 (SourceKeccak.afterLiteral middle (ps.foldr (fun part tail=>part.2++tail) [])).heap.next=8 := by
 rcases expression_run (global p) (frame data) 0 _ _ (plan data first second third x y z o n q m r l w) with
  ⟨middle,ps,related,actual,kept,next,count,nonheap⟩
 exact ⟨middle,ps,related,actual,next,count⟩

theorem packet_object (data first second third : Roadmap.Bytes) (x y z : Bool) (o n q m r l : Nat) (w : Roadmap.Word) :
 (result data first second third x y z o n q m r l w).heap.get 7=
 some ⟨.bytes .memory,.bytes (payload data x y z o n q m r l w)⟩ := SourceKeccak.allocated _ _

theorem old_alias (data first second third : Roadmap.Bytes) (x y z : Bool) (o n q m r l : Nat) (w : Roadmap.Word) :
 (result data first second third x y z o n q m r l w).heap.get 1=some ⟨.string .memory,.string first⟩ :=
 LiteralFailureMixedExpression.old_object _ _ _ _ (LiteralFailureCopySequenceControls.old_alias data first second third o n q m r l)

theorem timeout_copies (data first second third : Roadmap.Bytes) :
 (evalE (global .legacy) (frame data) 9 expression).run (locals true false true 0 1 1 1 0 1 ⟨300,by decide +kernel⟩,state first second third)=
 (.error .timeout,(locals true false true 0 1 1 1 0 1 ⟨300,by decide +kernel⟩,final data first second third 0 1 1 1 0 1)) := rfl

/-- Finite positive baseline: packed bool/word widths differ from standard heads. -/
theorem not_standard : payload [0,255,128] true false true 0 1 1 1 2 1 ⟨300,by decide +kernel⟩ ≠
 AbiEntry.encodeArgs (encoded [0,255,128] true false true 0 1 1 1 2 1 ⟨300,by decide +kernel⟩) := by decide +kernel

/-- Two different dynamic field boundaries can have identical packed bytes. -/
theorem split_collision :
 payload [1,2,3] true false true 0 1 1 1 2 1 ⟨300,by decide +kernel⟩=
 payload [1,2,3] true false true 0 1 1 2 3 0 ⟨300,by decide +kernel⟩ := by decide +kernel

theorem standard_distinguishes_split :
 AbiEntry.encodeArgs (encoded [1,2,3] true false true 0 1 1 1 2 1 ⟨300,by decide +kernel⟩)≠
 AbiEntry.encodeArgs (encoded [1,2,3] true false true 0 1 1 2 3 0 ⟨300,by decide +kernel⟩) := by decide +kernel
def observe (p : Roadmap.Pipeline) (data : Roadmap.Bytes) (x y z : Bool) (o n q m r l : Nat) (w : Roadmap.Word) : String :=
 match (evalE (global p) (frame data) 12 expression).run (locals x y z o n q m r l w,state [195,169] [128] [171,0]) with
 | (.ok (.val (.memRef _ ptr)),(_,after)) =>
  match after.heap.get ptr,after.heap.get 4,after.heap.get 5,after.heap.get 6,after.heap.get 1 with
  | some ⟨.bytes .memory,.bytes bs⟩,some ⟨.string .memory,.string first⟩,some ⟨.bytes .memory,.bytes second⟩,some ⟨.string .memory,.string third⟩,some ⟨.string .memory,.string old⟩ =>
   "{\"pointer\":"++toString ptr++",\"cursor\":"++toString after.heap.next++",\"first\":"++render first++",\"second\":"++render second++",\"third\":"++render third++",\"old\":"++render old++",\"bytes\":"++render bs++"}"
  | _,_,_,_,_ => "null"
 | _ => "null"
def suite (p : Roadmap.Pipeline) := "["++String.intercalate "," [
 observe p [] false false true 0 0 0 0 0 0 ⟨0,by decide +kernel⟩,
 observe p [99,0,255,128,7] true false true 1 3 1 3 1 3 ⟨300,by decide +kernel⟩,
 observe p (List.replicate 31 255++[0]++List.replicate 33 128) false true false 0 31 32 33 31 1 ⟨2^256-1,by decide +kernel⟩,
 observe p [0,255,128] true true false 1 33 99 31 2 33 ⟨2^255,by decide +kernel⟩,
 observe p ([0]++List.replicate 33 128++[255]) false true true 1 33 1 33 1 33 ⟨42,by decide +kernel⟩,
 observe p ([0]++List.replicate 32 0++[255]) true false false 1 32 32 2 0 1 ⟨2^256-1,by decide +kernel⟩]++"]"
#eval "PACKED_FIELDS_LEGACY="++suite .legacy
#eval "PACKED_FIELDS_VIAIR="++suite .viaIR


#print axioms piece_unique
#print axioms pieces_unique
#print axioms one_witness
#print axioms parts_witness
#print axioms encoding_run
#print axioms expression_run
#print axioms pieces
#print axioms encoded_run
#print axioms actual_expression
#print axioms applied
#print axioms packet_object
#print axioms old_alias
#print axioms timeout_copies
#print axioms not_standard
#print axioms split_collision
#print axioms standard_distinguishes_split
end Solidity.Lowering.V08.LiteralFailurePackedFieldsControls
