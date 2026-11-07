import Solidity.Lowering.V08.LiteralFailureConvertedFields
import Solidity.Lowering.V08.LiteralFailureMixedCustomErrorControls
namespace Solidity.Lowering.V08.LiteralFailureConvertedFieldsControls
open Solidity Source
open LiteralFailureConvertedFields
abbrev E := LiteralFailureMixedCustomErrorControls.environment
abbrev types := LiteralFailureMixedCustomErrorControls.types
abbrev declaration := LiteralFailureMixedCustomErrorControls.declaration
abbrev typed := LiteralFailureMixedCustomErrorControls.typed
abbrev state := LiteralFailureMixedCustomErrorControls.state
abbrev global := LiteralFailureMixedCustomErrorControls.global
def frame (data : Roadmap.Bytes) : Fr := {LiteralFailureMixedCustomErrorControls.frame with cd:=data}
def context : RCtx := [.bytes .calldata,.int IntTy.u256,.bytes .calldata,.int IntTy.u256,.bytes .memory,.bytes .memory,.bytes .memory,.bool]
def locals (o n q m : Nat) (a b : Roadmap.Word) : Locals E.layout context :=
 .cons (.cdRef rfl o n) (.cons (SourceEnvironment.sourceWord a) (.cons (.cdRef rfl q m)
  (.cons (SourceEnvironment.sourceWord b) (.cons (.memRef rfl 0) (.cons (.memRef rfl 1) (.cons (.memRef rfl 2) (.cons (.bool true) .nil)))))))
def arguments : RConvArgs E context types :=
 .cons (.local .here) rfl (.cons (.local (.there .here)) rfl
  (.cons (.local (.there (.there .here))) rfl (.cons (.local (.there (.there (.there .here)))) rfl .nil)))
def encoded (data : Roadmap.Bytes) (o n q m : Nat) (a b : Roadmap.Word) :=
 LiteralFailureMixedCustomErrorControls.encoded ((data.drop o).take n) ((data.drop q).take m) a b

theorem plan (data first second : Roadmap.Bytes) (o n q m : Nat) (a b : Roadmap.Word) :
 Plan (frame data) (state first second) (locals o n q m a b) arguments (encoded data o n q m a b) 2 :=
 .bytes .here o n rfl (.read (.there .here) rfl (.known (.uint a .nil))
  (.bytes (.there (.there .here)) q m rfl (.read (.there (.there (.there .here))) rfl (.known (.uint b .nil)) .nil)))
def final (data first second : Roadmap.Bytes) (o n q m : Nat) :=
 SourceKeccak.afterLiteral (SourceKeccak.afterLiteral (state first second) ((data.drop o).take n)) ((data.drop q).take m)
def values (a b : Roadmap.Word) : Source.Vals E.layout types :=
 .cons (.memRef rfl 3) (.cons (SourceEnvironment.sourceWord a) (.cons (.memRef rfl 4) (.cons (SourceEnvironment.sourceWord b) .nil)))

theorem arguments_actual (p : Roadmap.Pipeline) (data first second : Roadmap.Bytes)
 (o n q m : Nat) (a b : Roadmap.Word) :
 (evalConvArgs (global p) (frame data) 7 arguments).run (locals o n q m a b,state first second)=
 (.ok (values a b),(locals o n q m a b,final data first second o n q m)) := rfl

theorem facts (p : Roadmap.Pipeline) (data first second : Roadmap.Bytes) (o n q m : Nat) (a b : Roadmap.Word) :
 LiteralFailureLocatedFields.Fields (frame data) (final data first second o n q m) (values a b) (encoded data o n q m a b) ∧
 Keeps (frame data) (state first second) (final data first second o n q m) ∧
 (final data first second o n q m).heap.next=5 ∧
 final data first second o n q m={state first second with heap:=(final data first second o n q m).heap} := by
 rcases run (global p) (frame data) 0 (locals o n q m a b) (state first second)
  (plan data first second o n q m a b) with ⟨returned,reached,actual,fields,kept,next,nonheap⟩
 change (evalConvArgs (global p) (frame data) 7 arguments).run (locals o n q m a b,state first second)=
  (.ok returned,(locals o n q m a b,reached)) at actual
 rw [arguments_actual] at actual
 have stateEq := congrArg (fun result => result.2.2) actual
 have valueEq := Except.ok.inj (congrArg Prod.fst actual)
 cases stateEq
 cases valueEq
 exact ⟨fields,kept,next,nonheap⟩

def packet (p : Roadmap.Pipeline) (data : Roadmap.Bytes) (o n q m : Nat) (a b : Roadmap.Word) :=
 (global p).selector (sigOf E.layout declaration.name types)++AbiEntry.encodeArgs (encoded data o n q m a b)
def statement : RStmt E [] false .body context context := .revertError declaration typed arguments

theorem actual_error (p : Roadmap.Pipeline) (data first second : Roadmap.Bytes) (o n q m : Nat) (a b : Roadmap.Word) :
 (execS (global p) (frame data) 8 0 none statement (locals o n q m a b)).run (L0 E,state first second)=
 (.error (.revert (packet p data o n q m a b)),(L0 E,final data first second o n q m)) :=
 SourceCustomErrors.execute (global p) (frame data) 7 declaration typed arguments
  _ _ _ _ _ _ _ (arguments_actual p data first second o n q m a b)
  (LiteralFailureLocatedFields.encoding_run (frame data) 7 (L0 E) _ (facts p data first second o n q m a b).1)

theorem applied_error (p : Roadmap.Pipeline) (data first second : Roadmap.Bytes) (o n q m : Nat) (a b : Roadmap.Word) :
 ∃ reached : St E,
 (execS (global p) (frame data) 8 0 none statement (locals o n q m a b)).run (L0 E,state first second)=
 (.error (.revert (packet p data o n q m a b)),(L0 E,reached)) ∧
 Keeps (frame data) (state first second) reached ∧ reached.heap.next=(state first second).heap.next+2 ∧
 reached={state first second with heap:=reached.heap} :=
 error_run (global p) (frame data) 0 declaration typed _ _ (plan data first second o n q m a b)

theorem timeout_before (data first second : Roadmap.Bytes) :
 (execS (global .legacy) (frame data) 1 0 none statement (locals 0 0 0 0 ⟨0,by decide +kernel⟩ ⟨300,by decide +kernel⟩)).run
 (L0 E,state first second)=(.error .timeout,(L0 E,state first second)) := rfl

theorem timeout_one (data first second : Roadmap.Bytes) :
 (execS (global .legacy) (frame data) 3 0 none statement (locals 0 1 1 1 ⟨0,by decide +kernel⟩ ⟨300,by decide +kernel⟩)).run
 (L0 E,state first second)=
 (.error .timeout,(L0 E,SourceKeccak.afterLiteral (state first second) (data.take 1))) := rfl

theorem timeout_two (data first second : Roadmap.Bytes) :
 (execS (global .legacy) (frame data) 5 0 none statement (locals 0 1 1 1 ⟨0,by decide +kernel⟩ ⟨300,by decide +kernel⟩)).run
 (L0 E,state first second)=(.error .timeout,(L0 E,final data first second 0 1 1 1)) := rfl

theorem wrong_initial (p : Roadmap.Pipeline) (data first second : Roadmap.Bytes) (o n q m : Nat) (a b : Roadmap.Word) :
 (execS (global p) (frame data) 8 0 none statement (locals o n q m a b)).run (L0 E,state first second)≠
 (.error (.revert (packet p data o n q m a b)),(L0 E,state first second)) := by
 rw [actual_error]
 intro equal
 have bad := congrArg (fun result=>result.2.2.heap.next) equal
 change (5 : Nat)=3 at bad
 cases bad

def render := LiteralFailureMixedCustomErrorControls.render

theorem old_alias (data first second : Roadmap.Bytes) (o n q m : Nat) :
 (final data first second o n q m).heap.get 0=some ⟨.bytes .memory,.bytes [9,7]⟩ :=
 LiteralFailureMixedExpression.old_object _ _ _ _
  (LiteralFailureMixedExpression.old_object (state first second) _ _ _ rfl)

theorem first_copy (data first second : Roadmap.Bytes) (o n q m : Nat) :
 (final data first second o n q m).heap.get 3=some ⟨.bytes .memory,.bytes ((data.drop o).take n)⟩ :=
 LiteralFailureMixedExpression.old_object _ _ _ _ (SourceKeccak.allocated (state first second) _)

theorem second_copy (data first second : Roadmap.Bytes) (o n q m : Nat) :
 (final data first second o n q m).heap.get 4=some ⟨.bytes .memory,.bytes ((data.drop q).take m)⟩ :=
 SourceKeccak.allocated (SourceKeccak.afterLiteral (state first second) ((data.drop o).take n)) _

def observe (p : Roadmap.Pipeline) (data : Roadmap.Bytes) (o n q m : Nat) (a b : Roadmap.Word) : String :=
 match (execS (global p) (frame data) 8 0 none statement (locals o n q m a b)).run (L0 E,state [195,169] [128]) with
 | (.error (.revert bs),(_,after)) =>
  match after.heap.get 3,after.heap.get 4,after.heap.get 0 with
  | some ⟨.bytes .memory,.bytes first⟩,some ⟨.bytes .memory,.bytes second⟩,some ⟨.bytes .memory,.bytes old⟩ =>
   "{\"pointers\":[3,4],\"cursor\":"++toString after.heap.next++",\"first\":"++render first++",\"second\":"++render second++",\"old\":"++render old++",\"bytes\":"++render bs++"}"
  | _,_,_ => "null"
 | _ => "null"
def suite (p : Roadmap.Pipeline) := "["++String.intercalate "," [
 observe p [] 0 0 0 0 ⟨0,by decide +kernel⟩ ⟨300,by decide +kernel⟩,
 observe p [99,0,255,128,7] 1 3 1 3 ⟨300,by decide +kernel⟩ ⟨42,by decide +kernel⟩,
 observe p (List.replicate 31 255++[0]++List.replicate 33 128) 0 31 32 33 ⟨2^256-1,by decide +kernel⟩ ⟨2^255,by decide +kernel⟩,
 observe p [0,255,128] 1 33 99 31 ⟨2^255,by decide +kernel⟩ ⟨0,by decide +kernel⟩,
 observe p ([0]++List.replicate 33 128++[255]) 1 33 1 33 ⟨42,by decide +kernel⟩ ⟨300,by decide +kernel⟩,
 observe p ([0]++List.replicate 32 0++[255]) 1 32 32 2 ⟨0,by decide +kernel⟩ ⟨2^256-1,by decide +kernel⟩]++"]"
#eval "CONVERTED_FIELDS_LEGACY="++suite .legacy
#eval "CONVERTED_FIELDS_VIAIR="++suite .viaIR
#print axioms kept_head
#print axioms after_copy
#print axioms run
#print axioms error_run
#print axioms plan
#print axioms arguments_actual
#print axioms facts
#print axioms actual_error
#print axioms applied_error
#print axioms timeout_before
#print axioms timeout_one
#print axioms timeout_two
#print axioms wrong_initial
#print axioms old_alias
#print axioms first_copy
#print axioms second_copy
end Solidity.Lowering.V08.LiteralFailureConvertedFieldsControls
