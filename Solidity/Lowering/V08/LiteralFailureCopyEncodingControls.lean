import Solidity.Lowering.V08.LiteralFailureCopyEncoding
import Solidity.Lowering.V08.LiteralFailureCopySequenceControls
namespace Solidity.Lowering.V08.LiteralFailureCopyEncodingControls
open Solidity Source
open LiteralFailureCopySequenceControls

def expression : RExpr E context (.bytes .memory) := .abiEncode .encode (LiteralFailureCopyEncoding.expressions arguments)
def result (data first second third : Roadmap.Bytes) (x y z : Bool) (o n q m r l : Nat) (w : Roadmap.Word) :=
 SourceKeccak.afterLiteral (final data first second third o n q m r l) (AbiEntry.encodeArgs (encoded data x y z o n q m r l w))

theorem arguments_actual (p : Roadmap.Pipeline) (data first second third : Roadmap.Bytes)
 (x y z : Bool) (o n q m r l : Nat) (w : Roadmap.Word) :
 (evalArgs (global p) (frame data) 11 (LiteralFailureCopyEncoding.expressions arguments)).run
 (locals x y z o n q m r l w,state first second third)=
 (.ok (values x y z w).toR,(locals x y z o n q m r l w,final data first second third o n q m r l)) := rfl

theorem actual_expression (p : Roadmap.Pipeline) (data first second third : Roadmap.Bytes)
 (x y z : Bool) (o n q m r l : Nat) (w : Roadmap.Word) :
 (evalE (global p) (frame data) 12 expression).run (locals x y z o n q m r l w,state first second third)=
 (.ok (.val (.memRef rfl 7)),(locals x y z o n q m r l w,result data first second third x y z o n q m r l w)) :=
 SourceAbi.execute (global p) (frame data) 11 false _ _ _ _ _ _ _ _ _
 (arguments_actual p data first second third x y z o n q m r l w)
 (LiteralFailureLocatedFields.encoding_run (frame data) 11 _ _
  (LiteralFailureCopySequenceControls.facts p data first second third x y z o n q m r l w).1)

theorem applied (p : Roadmap.Pipeline) (data first second third : Roadmap.Bytes)
 (x y z : Bool) (o n q m r l : Nat) (w : Roadmap.Word) :
 ∃ middle : St E,
 (evalE (global p) (frame data) 12 expression).run (locals x y z o n q m r l w,state first second third)=
 (.ok (.val (.memRef rfl middle.heap.next)),
  (locals x y z o n q m r l w,SourceKeccak.afterLiteral middle (AbiEntry.encodeArgs (encoded data x y z o n q m r l w)))) ∧
 LiteralFailureConvertedFields.Keeps (frame data) (state first second third)
  (SourceKeccak.afterLiteral middle (AbiEntry.encodeArgs (encoded data x y z o n q m r l w))) ∧
 middle.heap.next=(state first second third).heap.next+3 ∧
 (SourceKeccak.afterLiteral middle (AbiEntry.encodeArgs (encoded data x y z o n q m r l w))).heap.next=
  (state first second third).heap.next+3+1 ∧
 SourceKeccak.afterLiteral middle (AbiEntry.encodeArgs (encoded data x y z o n q m r l w))=
  {state first second third with heap:=(SourceKeccak.afterLiteral middle (AbiEntry.encodeArgs (encoded data x y z o n q m r l w))).heap} :=
 LiteralFailureCopyEncoding.expression_run (global p) (frame data) 0 _ _ (plan data first second third x y z o n q m r l w)

theorem packet_object (data first second third : Roadmap.Bytes) (x y z : Bool) (o n q m r l : Nat) (w : Roadmap.Word) :
 (result data first second third x y z o n q m r l w).heap.get 7=
 some ⟨.bytes .memory,.bytes (AbiEntry.encodeArgs (encoded data x y z o n q m r l w))⟩ := SourceKeccak.allocated _ _

theorem old_alias (data first second third : Roadmap.Bytes) (x y z : Bool) (o n q m r l : Nat) (w : Roadmap.Word) :
 (result data first second third x y z o n q m r l w).heap.get 1=some ⟨.string .memory,.string first⟩ :=
 LiteralFailureMixedExpression.old_object _ _ _ _ (LiteralFailureCopySequenceControls.old_alias data first second third o n q m r l)

theorem timeout_copies (data first second third : Roadmap.Bytes) :
 (evalE (global .legacy) (frame data) 9 expression).run (locals true false true 0 1 1 1 0 1 ⟨300,by decide +kernel⟩,state first second third)=
 (.error .timeout,(locals true false true 0 1 1 1 0 1 ⟨300,by decide +kernel⟩,final data first second third 0 1 1 1 0 1)) := rfl

theorem wrong_pointer (p : Roadmap.Pipeline) (data first second third : Roadmap.Bytes)
 (x y z : Bool) (o n q m r l : Nat) (w : Roadmap.Word) :
 (evalE (global p) (frame data) 12 expression).run (locals x y z o n q m r l w,state first second third)≠
 (.ok (.val (.memRef rfl 4)),(locals x y z o n q m r l w,result data first second third x y z o n q m r l w)) := by
 rw [actual_expression]
 intro equal
 have bad := Except.ok.inj (congrArg Prod.fst equal)
 cases bad

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
#eval "COPY_ENCODING_LEGACY="++suite .legacy
#eval "COPY_ENCODING_VIAIR="++suite .viaIR

#print axioms LiteralFailureCopyEncoding.arguments_run
#print axioms LiteralFailureCopyEncoding.expression_run
#print axioms arguments_actual
#print axioms actual_expression
#print axioms applied
#print axioms packet_object
#print axioms old_alias
#print axioms timeout_copies
#print axioms wrong_pointer
end Solidity.Lowering.V08.LiteralFailureCopyEncodingControls
