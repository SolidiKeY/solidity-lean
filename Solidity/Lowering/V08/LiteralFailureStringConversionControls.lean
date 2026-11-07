import Solidity.Lowering.V08.LiteralFailureStringConversion
import Solidity.Lowering.V08.LiteralFailureStringPrefixControls
namespace Solidity.Lowering.V08.LiteralFailureStringConversionControls
open Solidity Source
open LiteralFailureStringConversion
abbrev E := LiteralFailureStringPrefixControls.environment
abbrev types := LiteralFailureStringPrefixControls.types
abbrev declaration := LiteralFailureStringPrefixControls.declaration
abbrev typed := LiteralFailureStringPrefixControls.typed
abbrev state := LiteralFailureStringPrefixControls.state
abbrev global := LiteralFailureStringPrefixControls.global
def frame (data : Roadmap.Bytes) : Fr := {LiteralFailureStringPrefixControls.frame with cd:=data}
def context : RCtx := [.string .calldata,.int IntTy.u256,.bytes .calldata,.int IntTy.u256,.bytes .memory,.string .memory,.bytes .memory,.bool]
def locals (o n q m : Nat) (a b : Roadmap.Word) : Locals E.layout context :=
 .cons (.cdRef rfl o n) (.cons (SourceEnvironment.sourceWord a) (.cons (.cdRef rfl q m)
  (.cons (SourceEnvironment.sourceWord b) (.cons (.memRef rfl 0) (.cons (.memRef rfl 1) (.cons (.memRef rfl 2) (.cons (.bool true) .nil)))))))
def tailTypes : RCtx := [.int IntTy.u256,.bytes .memory,.int IntTy.u256]
def tail : RConvArgs E context tailTypes :=
 .cons (.local (.there .here)) rfl (.cons (.local (.there (.there .here))) rfl
  (.cons (.local (.there (.there (.there .here)))) rfl .nil))
def convertedArguments : RConvArgs E context types := arguments .here tail
def encodedTail (data : Roadmap.Bytes) (q m : Nat) (a b : Roadmap.Word) :
 AbiEntry.Vals [.word (.uint 256),.bytes,.word (.uint 256)] :=
 .cons (.word (LiteralFailureDynamicError.abiWord a))
  (.cons (.bytes ((data.drop q).take m)) (.cons (.word (LiteralFailureDynamicError.abiWord b)) .nil))
def encoded (data : Roadmap.Bytes) (o n q m : Nat) (a b : Roadmap.Word) :=
 AbiEntry.Vals.cons (.bytes ((data.drop o).take n)) (encodedTail data q m a b)
theorem plan (data first second : Roadmap.Bytes) (o n q m : Nat) (a b : Roadmap.Word) :
 LiteralFailureConvertedFields.Plan (frame data) (state first second) (locals o n q m a b) tail (encodedTail data q m a b) 1 :=
 .read (.there .here) rfl (.known (.uint a .nil))
  (.bytes (.there (.there .here)) q m rfl (.read (.there (.there (.there .here))) rfl (.known (.uint b .nil)) .nil))
def final (data first second : Roadmap.Bytes) (o n q m : Nat) :=
 SourceKeccak.afterLiteral (afterString (state first second) ((data.drop o).take n)) ((data.drop q).take m)
def values (a b : Roadmap.Word) : Source.Vals E.layout types :=
 .cons (.memRef rfl 3) (.cons (SourceEnvironment.sourceWord a) (.cons (.memRef rfl 4) (.cons (SourceEnvironment.sourceWord b) .nil)))

theorem arguments_actual (p : Roadmap.Pipeline) (data first second : Roadmap.Bytes) (o n q m : Nat) (a b : Roadmap.Word) :
 (evalConvArgs (global p) (frame data) 7 convertedArguments).run (locals o n q m a b,state first second)=
 (.ok (values a b),(locals o n q m a b,final data first second o n q m)) := rfl

theorem facts (p : Roadmap.Pipeline) (data first second : Roadmap.Bytes) (o n q m : Nat) (a b : Roadmap.Word) :
 LiteralFailureLocatedFields.Fields (frame data) (final data first second o n q m) (values a b) (encoded data o n q m a b) ∧
 LiteralFailureConvertedFields.Keeps (frame data) (state first second) (final data first second o n q m) ∧
 (final data first second o n q m).heap.next=5 ∧
 final data first second o n q m={state first second with heap:=(final data first second o n q m).heap} := by
 rcases run (global p) (frame data) 0 o n (locals o n q m a b) (state first second) .here rfl
  (plan data first second o n q m a b) with ⟨returned,reached,actual,fields,kept,next,nonheap⟩
 change (evalConvArgs (global p) (frame data) 7 convertedArguments).run (locals o n q m a b,state first second)=
  (.ok returned,(locals o n q m a b,reached)) at actual
 rw [arguments_actual] at actual
 have stateEq := congrArg (fun result=>result.2.2) actual
 have valueEq := Except.ok.inj (congrArg Prod.fst actual)
 cases stateEq
 cases valueEq
 exact ⟨fields,kept,next,nonheap⟩

def packet (p : Roadmap.Pipeline) (data : Roadmap.Bytes) (o n q m : Nat) (a b : Roadmap.Word) :=
 (global p).selector (sigOf E.layout declaration.name types)++AbiEntry.encodeArgs (encoded data o n q m a b)
def statement : RStmt E [] false .body context context := .revertError declaration typed convertedArguments

theorem actual_error (p : Roadmap.Pipeline) (data first second : Roadmap.Bytes) (o n q m : Nat) (a b : Roadmap.Word) :
 (execS (global p) (frame data) 8 0 none statement (locals o n q m a b)).run (L0 E,state first second)=
 (.error (.revert (packet p data o n q m a b)),(L0 E,final data first second o n q m)) :=
 SourceCustomErrors.execute (global p) (frame data) 7 declaration typed convertedArguments _ _ _ _ _ _ _
 (arguments_actual p data first second o n q m a b)
 (LiteralFailureLocatedFields.encoding_run (frame data) 7 (L0 E) _ (facts p data first second o n q m a b).1)

theorem applied_error (p : Roadmap.Pipeline) (data first second : Roadmap.Bytes) (o n q m : Nat) (a b : Roadmap.Word) :
 ∃ reached : St E,
 (execS (global p) (frame data) 8 0 none statement (locals o n q m a b)).run (L0 E,state first second)=
 (.error (.revert (packet p data o n q m a b)),(L0 E,reached)) ∧
 LiteralFailureConvertedFields.Keeps (frame data) (state first second) reached ∧
 reached.heap.next=(state first second).heap.next+2 ∧ reached={state first second with heap:=reached.heap} :=
 error_run (global p) (frame data) 0 o n declaration typed _ _ .here rfl (plan data first second o n q m a b)

theorem timeout_one (data first second : Roadmap.Bytes) :
 (execS (global .legacy) (frame data) 3 0 none statement (locals 0 1 1 1 ⟨0,by decide +kernel⟩ ⟨300,by decide +kernel⟩)).run (L0 E,state first second)=
 (.error .timeout,(L0 E,afterString (state first second) (data.take 1))) := rfl

theorem timeout_two (data first second : Roadmap.Bytes) :
 (execS (global .legacy) (frame data) 5 0 none statement (locals 0 1 1 1 ⟨0,by decide +kernel⟩ ⟨300,by decide +kernel⟩)).run (L0 E,state first second)=
 (.error .timeout,(L0 E,final data first second 0 1 1 1)) := rfl

theorem first_copy (data first second : Roadmap.Bytes) (o n q m : Nat) :
 (final data first second o n q m).heap.get 3=some ⟨.string .memory,.string ((data.drop o).take n)⟩ :=
 LiteralFailureMixedExpression.old_object _ _ _ _ (allocated (state first second) _)

theorem second_copy (data first second : Roadmap.Bytes) (o n q m : Nat) :
 (final data first second o n q m).heap.get 4=some ⟨.bytes .memory,.bytes ((data.drop q).take m)⟩ :=
 SourceKeccak.allocated (afterString (state first second) ((data.drop o).take n)) _

theorem wrong_tag (data first second : Roadmap.Bytes) (o n q m : Nat) :
 (final data first second o n q m).heap.get 3≠some ⟨.bytes .memory,.bytes ((data.drop o).take n)⟩ := by
 rw [first_copy]
 intro equal
 cases equal

theorem old_alias (data first second : Roadmap.Bytes) (o n q m : Nat) :
 (final data first second o n q m).heap.get 1=some ⟨.string .memory,.string first⟩ :=
 LiteralFailureMixedExpression.old_object _ _ _ _ (old_lookup (state first second) _ _ _ rfl)

def render := LiteralFailureStringPrefixControls.render

theorem timeout_before (data first second : Roadmap.Bytes) :
 (execS (global .legacy) (frame data) 1 0 none statement (locals 0 1 1 1 ⟨0,by decide +kernel⟩ ⟨300,by decide +kernel⟩)).run (L0 E,state first second)=
 (.error .timeout,(L0 E,state first second)) := rfl

theorem wrong_initial (p : Roadmap.Pipeline) (data first second : Roadmap.Bytes) (o n q m : Nat) (a b : Roadmap.Word) :
 (execS (global p) (frame data) 8 0 none statement (locals o n q m a b)).run (L0 E,state first second)≠
 (.error (.revert (packet p data o n q m a b)),(L0 E,state first second)) := by
 rw [actual_error]
 intro equal
 have bad := congrArg (fun result=>result.2.2.heap.next) equal
 change (5 : Nat)=3 at bad
 cases bad

def observe (p : Roadmap.Pipeline) (data : Roadmap.Bytes) (o n q m : Nat) (a b : Roadmap.Word) : String :=
 match (execS (global p) (frame data) 8 0 none statement (locals o n q m a b)).run (L0 E,state [195,169] [128]) with
 | (.error (.revert bs),(_,after)) =>
  match after.heap.get 3,after.heap.get 4,after.heap.get 1 with
  | some ⟨.string .memory,.string first⟩,some ⟨.bytes .memory,.bytes second⟩,some ⟨.string .memory,.string old⟩ =>
   "{\"pointers\":[3,4],\"kinds\":[\"string\",\"bytes\"],\"cursor\":"++toString after.heap.next++",\"first\":"++render first++",\"second\":"++render second++",\"old\":"++render old++",\"bytes\":"++render bs++"}"
  | _,_,_ => "null"
 | _ => "null"
def suite (p : Roadmap.Pipeline) := "["++String.intercalate "," [
 observe p [] 0 0 0 0 ⟨0,by decide +kernel⟩ ⟨300,by decide +kernel⟩,
 observe p [99,0,255,128,7] 1 3 1 3 ⟨300,by decide +kernel⟩ ⟨42,by decide +kernel⟩,
 observe p (List.replicate 31 255++[0]++List.replicate 33 128) 0 31 32 33 ⟨2^256-1,by decide +kernel⟩ ⟨2^255,by decide +kernel⟩,
 observe p [0,255,128] 1 33 99 31 ⟨2^255,by decide +kernel⟩ ⟨0,by decide +kernel⟩,
 observe p ([0]++List.replicate 33 128++[255]) 1 33 1 33 ⟨42,by decide +kernel⟩ ⟨300,by decide +kernel⟩,
 observe p ([0]++List.replicate 32 0++[255]) 1 32 32 2 ⟨0,by decide +kernel⟩ ⟨2^256-1,by decide +kernel⟩]++"]"
#eval "STRING_CONVERSION_LEGACY="++suite .legacy
#eval "STRING_CONVERSION_VIAIR="++suite .viaIR
#print axioms old_lookup
#print axioms typed_fields_after
#print axioms head_after
#print axioms fields_after
#print axioms plan_after
#print axioms copy_run
#print axioms allocated
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
#print axioms first_copy
#print axioms second_copy
#print axioms wrong_tag
#print axioms old_alias
#print axioms wrong_initial
end Solidity.Lowering.V08.LiteralFailureStringConversionControls
