import Solidity.Lowering.V08.LiteralFailureCopySequence
import Solidity.Lowering.V08.LiteralFailureTypedFieldsControls
namespace Solidity.Lowering.V08.LiteralFailureCopySequenceControls
open Solidity Source
open LiteralFailureCopySequence
abbrev E := LiteralFailureTypedFieldsControls.environment
abbrev types := LiteralFailureTypedFieldsControls.types
abbrev declaration := LiteralFailureTypedFieldsControls.declaration
abbrev typed := LiteralFailureTypedFieldsControls.typed
abbrev state := LiteralFailureTypedFieldsControls.state
abbrev global := LiteralFailureTypedFieldsControls.global
def frame (data : Roadmap.Bytes) : Fr := {LiteralFailureTypedFieldsControls.frame with cd:=data}
def context : RCtx := [.bool,.string .calldata,.int IntTy.u256,.bool,.bytes .calldata,.string .calldata,.bool,.bytes .memory,.string .memory,.bytes .memory,.string .memory,.bool]
def locals (x y z : Bool) (o n q m r l : Nat) (w : Roadmap.Word) : Locals E.layout context :=
 .cons (.bool x) (.cons (.cdRef rfl o n) (.cons (SourceEnvironment.sourceWord w) (.cons (.bool y)
  (.cons (.cdRef rfl q m) (.cons (.cdRef rfl r l) (.cons (.bool z) (.cons (.memRef rfl 0)
   (.cons (.memRef rfl 1) (.cons (.memRef rfl 2) (.cons (.memRef rfl 3) (.cons (.bool true) .nil)))))))))))
def arguments : RConvArgs E context types := .cons (.local .here) rfl (.cons (.local (.there .here)) rfl (.cons (.local (.there (.there .here))) rfl (.cons (.local (.there (.there (.there .here)))) rfl (.cons (.local (.there (.there (.there (.there .here))))) rfl (.cons (.local (.there (.there (.there (.there (.there .here)))))) rfl (.cons (.local (.there (.there (.there (.there (.there (.there .here))))))) rfl (.nil)))))))
def encoded (data : Roadmap.Bytes) (x y z : Bool) (o n q m r l : Nat) (w : Roadmap.Word) :=
 LiteralFailureTypedFieldsControls.encoded x y z ((data.drop o).take n) ((data.drop q).take m) ((data.drop r).take l) w

theorem plan (data first second third : Roadmap.Bytes) (x y z : Bool) (o n q m r l : Nat) (w : Roadmap.Word) :
 Plan (frame data) (state first second third) (locals x y z o n q m r l w) arguments (encoded data x y z o n q m r l w) 3 :=
 .cons .here rfl (.read .here rfl (.known (.boolean x .nil))) (.cons (.there .here) rfl (.string (.there .here) o n rfl) (.cons (.there (.there .here)) rfl (.read (.there (.there .here)) rfl (.known (.uint w .nil))) (.cons (.there (.there (.there .here))) rfl (.read (.there (.there (.there .here))) rfl (.known (.boolean y .nil))) (.cons (.there (.there (.there (.there .here)))) rfl (.bytes (.there (.there (.there (.there .here)))) q m rfl) (.cons (.there (.there (.there (.there (.there .here))))) rfl (.string (.there (.there (.there (.there (.there .here))))) r l rfl) (.cons (.there (.there (.there (.there (.there (.there .here)))))) rfl (.read (.there (.there (.there (.there (.there (.there .here)))))) rfl (.known (.boolean z .nil))) (.nil)))))))
def final (data first second third : Roadmap.Bytes) (o n q m r l : Nat) :=
 LiteralFailureStringConversion.afterString
  (SourceKeccak.afterLiteral (LiteralFailureStringConversion.afterString (state first second third) ((data.drop o).take n)) ((data.drop q).take m))
  ((data.drop r).take l)
def values (x y z : Bool) (w : Roadmap.Word) : Source.Vals E.layout types :=
 .cons (.bool x) (.cons (.memRef rfl 4) (.cons (SourceEnvironment.sourceWord w) (.cons (.bool y)
  (.cons (.memRef rfl 5) (.cons (.memRef rfl 6) (.cons (.bool z) .nil))))))

theorem arguments_actual (p : Roadmap.Pipeline) (data first second third : Roadmap.Bytes)
 (x y z : Bool) (o n q m r l : Nat) (w : Roadmap.Word) :
 (evalConvArgs (global p) (frame data) 10 arguments).run (locals x y z o n q m r l w,state first second third)=
 (.ok (values x y z w),(locals x y z o n q m r l w,final data first second third o n q m r l)) := rfl

theorem facts (p : Roadmap.Pipeline) (data first second third : Roadmap.Bytes)
 (x y z : Bool) (o n q m r l : Nat) (w : Roadmap.Word) :
 LiteralFailureLocatedFields.Fields (frame data) (final data first second third o n q m r l) (values x y z w) (encoded data x y z o n q m r l w) ∧
 LiteralFailureConvertedFields.Keeps (frame data) (state first second third) (final data first second third o n q m r l) ∧
 (final data first second third o n q m r l).heap.next=7 ∧
 final data first second third o n q m r l={state first second third with heap:=(final data first second third o n q m r l).heap} := by
 rcases run (global p) (frame data) 0 (locals x y z o n q m r l w) (state first second third)
  (plan data first second third x y z o n q m r l w) with ⟨returned,reached,actual,fields,kept,next,nonheap⟩
 change (evalConvArgs (global p) (frame data) 10 arguments).run (locals x y z o n q m r l w,state first second third)=
  (.ok returned,(locals x y z o n q m r l w,reached)) at actual
 rw [arguments_actual] at actual
 have stateEq := congrArg (fun result=>result.2.2) actual
 have valueEq := Except.ok.inj (congrArg Prod.fst actual)
 cases stateEq
 cases valueEq
 exact ⟨fields,kept,next,nonheap⟩

def packet (p : Roadmap.Pipeline) (data : Roadmap.Bytes) (x y z : Bool) (o n q m r l : Nat) (w : Roadmap.Word) :=
 (global p).selector (sigOf E.layout declaration.name types)++AbiEntry.encodeArgs (encoded data x y z o n q m r l w)
def statement : RStmt E [] false .body context context := .revertError declaration typed arguments

theorem actual_error (p : Roadmap.Pipeline) (data first second third : Roadmap.Bytes)
 (x y z : Bool) (o n q m r l : Nat) (w : Roadmap.Word) :
 (execS (global p) (frame data) 11 0 none statement (locals x y z o n q m r l w)).run (L0 E,state first second third)=
 (.error (.revert (packet p data x y z o n q m r l w)),(L0 E,final data first second third o n q m r l)) :=
 SourceCustomErrors.execute (global p) (frame data) 10 declaration typed arguments _ _ _ _ _ _ _
 (arguments_actual p data first second third x y z o n q m r l w)
 (LiteralFailureLocatedFields.encoding_run (frame data) 10 (L0 E) _ (facts p data first second third x y z o n q m r l w).1)

theorem applied_error (p : Roadmap.Pipeline) (data first second third : Roadmap.Bytes)
 (x y z : Bool) (o n q m r l : Nat) (w : Roadmap.Word) :
 ∃ reached : St E,
 (execS (global p) (frame data) 11 0 none statement (locals x y z o n q m r l w)).run (L0 E,state first second third)=
 (.error (.revert (packet p data x y z o n q m r l w)),(L0 E,reached)) ∧
 LiteralFailureConvertedFields.Keeps (frame data) (state first second third) reached ∧
 reached.heap.next=(state first second third).heap.next+3 ∧ reached={state first second third with heap:=reached.heap} :=
 error_run (global p) (frame data) 0 declaration typed _ _ (plan data first second third x y z o n q m r l w)

theorem timeout_before (data first second third : Roadmap.Bytes) :
 (execS (global .legacy) (frame data) 1 0 none statement (locals true false true 0 1 1 1 0 1 ⟨300,by decide +kernel⟩)).run (L0 E,state first second third)=
 (.error .timeout,(L0 E,(state first second third))) := rfl

theorem timeout_one (data first second third : Roadmap.Bytes) :
 (execS (global .legacy) (frame data) 4 0 none statement (locals true false true 0 1 1 1 0 1 ⟨300,by decide +kernel⟩)).run (L0 E,state first second third)=
 (.error .timeout,(L0 E,LiteralFailureStringConversion.afterString (state first second third) (data.take 1))) := rfl

theorem timeout_two (data first second third : Roadmap.Bytes) :
 (execS (global .legacy) (frame data) 7 0 none statement (locals true false true 0 1 1 1 0 1 ⟨300,by decide +kernel⟩)).run (L0 E,state first second third)=
 (.error .timeout,(L0 E,SourceKeccak.afterLiteral (LiteralFailureStringConversion.afterString (state first second third) (data.take 1)) ((data.drop 1).take 1))) := rfl

theorem timeout_three (data first second third : Roadmap.Bytes) :
 (execS (global .legacy) (frame data) 8 0 none statement (locals true false true 0 1 1 1 0 1 ⟨300,by decide +kernel⟩)).run (L0 E,state first second third)=
 (.error .timeout,(L0 E,final data first second third 0 1 1 1 0 1)) := rfl

def render := LiteralFailureTypedFieldsControls.render

theorem old_alias (data first second third : Roadmap.Bytes) (o n q m r l : Nat) :
 (final data first second third o n q m r l).heap.get 1=some ⟨.string .memory,.string first⟩ :=
 LiteralFailureStringConversion.old_lookup _ _ _ _
  (LiteralFailureMixedExpression.old_object _ _ _ _
   (LiteralFailureStringConversion.old_lookup (state first second third) _ _ _ rfl))

theorem first_copy (data first second third : Roadmap.Bytes) (o n q m r l : Nat) :
 (final data first second third o n q m r l).heap.get 4=some ⟨.string .memory,.string ((data.drop o).take n)⟩ :=
 LiteralFailureStringConversion.old_lookup _ _ _ _
  (LiteralFailureMixedExpression.old_object _ _ _ _ (LiteralFailureStringConversion.allocated (state first second third) _))

theorem second_copy (data first second third : Roadmap.Bytes) (o n q m r l : Nat) :
 (final data first second third o n q m r l).heap.get 5=some ⟨.bytes .memory,.bytes ((data.drop q).take m)⟩ :=
 LiteralFailureStringConversion.old_lookup _ _ _ _
  (SourceKeccak.allocated (LiteralFailureStringConversion.afterString (state first second third) ((data.drop o).take n)) _)

theorem third_copy (data first second third : Roadmap.Bytes) (o n q m r l : Nat) :
 (final data first second third o n q m r l).heap.get 6=some ⟨.string .memory,.string ((data.drop r).take l)⟩ :=
 LiteralFailureStringConversion.allocated
  (SourceKeccak.afterLiteral (LiteralFailureStringConversion.afterString (state first second third) ((data.drop o).take n)) ((data.drop q).take m)) _

theorem wrong_counter (p : Roadmap.Pipeline) (data first second third : Roadmap.Bytes)
 (x y z : Bool) (o n q m r l : Nat) (w : Roadmap.Word) :
 (execS (global p) (frame data) 11 0 none statement (locals x y z o n q m r l w)).run (L0 E,state first second third)≠
 (.error (.revert (packet p data x y z o n q m r l w)),(L0 E,state first second third)) := by
 rw [actual_error]
 intro equal
 have bad := congrArg (fun result=>result.2.2.heap.next) equal
 change (7 : Nat)=4 at bad
 cases bad

def observe (p : Roadmap.Pipeline) (data : Roadmap.Bytes) (x y z : Bool) (o n q m r l : Nat) (w : Roadmap.Word) : String :=
 match (execS (global p) (frame data) 11 0 none statement (locals x y z o n q m r l w)).run (L0 E,state [195,169] [128] [171,0]) with
 | (.error (.revert bs),(_,after)) =>
  match after.heap.get 4,after.heap.get 5,after.heap.get 6,after.heap.get 1 with
  | some ⟨.string .memory,.string first⟩,some ⟨.bytes .memory,.bytes second⟩,some ⟨.string .memory,.string third⟩,some ⟨.string .memory,.string old⟩ =>
   "{\"pointers\":[4,5,6],\"kinds\":[\"string\",\"bytes\",\"string\"],\"cursor\":"++toString after.heap.next++",\"first\":"++render first++",\"second\":"++render second++",\"third\":"++render third++",\"old\":"++render old++",\"bytes\":"++render bs++"}"
  | _,_,_,_ => "null"
 | _ => "null"
def suite (p : Roadmap.Pipeline) := "["++String.intercalate "," [
 observe p [] false false true 0 0 0 0 0 0 ⟨0,by decide +kernel⟩,
 observe p [99,0,255,128,7] true false true 1 3 1 3 1 3 ⟨300,by decide +kernel⟩,
 observe p (List.replicate 31 255++[0]++List.replicate 33 128) false true false 0 31 32 33 31 1 ⟨2^256-1,by decide +kernel⟩,
 observe p [0,255,128] true true false 1 33 99 31 2 33 ⟨2^255,by decide +kernel⟩,
 observe p ([0]++List.replicate 33 128++[255]) false true true 1 33 1 33 1 33 ⟨42,by decide +kernel⟩,
 observe p ([0]++List.replicate 32 0++[255]) true false false 1 32 32 2 0 1 ⟨2^256-1,by decide +kernel⟩]++"]"
#eval "COPY_SEQUENCE_LEGACY="++suite .legacy
#eval "COPY_SEQUENCE_VIAIR="++suite .viaIR
#print axioms step_transport
#print axioms plan_transport
#print axioms step_run
#print axioms run
#print axioms error_run
#print axioms of_bytes_plan
#print axioms plan
#print axioms arguments_actual
#print axioms facts
#print axioms actual_error
#print axioms applied_error
#print axioms timeout_before
#print axioms timeout_one
#print axioms timeout_two
#print axioms timeout_three
#print axioms old_alias
#print axioms first_copy
#print axioms second_copy
#print axioms third_copy
#print axioms wrong_counter
end Solidity.Lowering.V08.LiteralFailureCopySequenceControls
