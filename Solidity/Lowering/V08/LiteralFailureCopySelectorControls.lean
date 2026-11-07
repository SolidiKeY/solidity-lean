import Solidity.Lowering.V08.LiteralFailureCopySelector
import Solidity.Lowering.V08.LiteralFailureCopySequenceControls
namespace Solidity.Lowering.V08.LiteralFailureCopySelectorControls
open Solidity Source
open LiteralFailureCopySelector
abbrev E := LiteralFailureCopySequenceControls.E
abbrev state := LiteralFailureCopySequenceControls.state
abbrev frame := LiteralFailureCopySequenceControls.frame
abbrev global := LiteralFailureCopySequenceControls.global
abbrev context : RCtx := [Selector,.bytes .calldata,.int IntTy.u256,.string .memory,.bool,.bytes .memory]
abbrev types : RCtx := [.bytes .memory,.int IntTy.u256,.string .memory,.bool]
def locals (sel : Roadmap.Bytes) (extent : sel.length=4) (off len : Nat) (w : Roadmap.Word) (flag : Bool) : Locals E.layout context :=
 .cons (.fixedBytes sel extent) (.cons (.cdRef rfl off len) (.cons (SourceEnvironment.sourceWord w)
  (.cons (.memRef rfl 1) (.cons (.bool flag) (.cons (.memRef rfl 0) .nil)))))
def arguments : RConvArgs E context types :=
 .cons (.local (.there .here)) rfl (.cons (.local (.there (.there .here))) rfl
  (.cons (.local (.there (.there (.there .here)))) rfl (.cons (.local (.there (.there (.there (.there .here))))) rfl .nil)))
def encoded (data first : Roadmap.Bytes) (off len : Nat) (w : Roadmap.Word) (flag : Bool) :=
 AbiEntry.Vals.cons (AbiEntry.Val.bytes ((data.drop off).take len)) (.cons (.word (LiteralFailureDynamicError.abiWord w))
  (.cons (.bytes first) (.cons (.word (BoolErrorAbi.word flag)) .nil)))
def values (w : Roadmap.Word) (flag : Bool) : Source.Vals E.layout types :=
 .cons (.memRef rfl 4) (.cons (SourceEnvironment.sourceWord w) (.cons (.memRef rfl 1) (.cons (.bool flag) .nil)))
def middle (data first second third : Roadmap.Bytes) (off len : Nat) :=
 SourceKeccak.afterLiteral (state first second third) ((data.drop off).take len)
def packet (sel data first : Roadmap.Bytes) (off len : Nat) (w : Roadmap.Word) (flag : Bool) :=
 sel++AbiEntry.encodeArgs (encoded data first off len w flag)
def result (sel data first second third : Roadmap.Bytes) (off len : Nat) (w : Roadmap.Word) (flag : Bool) :=
 SourceKeccak.afterLiteral (middle data first second third off len) (packet sel data first off len w flag)
def expression : RExpr E context (.bytes .memory) :=
 .abiEncode .encodeWithSelector (.cons (.local .here) (LiteralFailureCopyEncoding.expressions arguments))

theorem plan (sel data first second third : Roadmap.Bytes) (extent : sel.length=4)
 (off len : Nat) (w : Roadmap.Word) (flag : Bool) :
 LiteralFailureCopySequence.Plan (frame data) (state first second third) (locals sel extent off len w flag)
 arguments (encoded data first off len w flag) 1 :=
 .cons (.there .here) rfl (.bytes (.there .here) off len rfl)
  (.cons (.there (.there .here)) rfl (.read (.there (.there .here)) rfl (.known (.uint w .nil)))
   (.cons (.there (.there (.there .here))) rfl (.read (.there (.there (.there .here))) rfl (.known (.string 1 first rfl .nil)))
    (.cons (.there (.there (.there (.there .here)))) rfl (.read (.there (.there (.there (.there .here)))) rfl (.known (.boolean flag .nil))) .nil)))

theorem actual_arguments (p : Roadmap.Pipeline) (sel data first second third : Roadmap.Bytes) (extent : sel.length=4)
 (off len : Nat) (w : Roadmap.Word) (flag : Bool) :
 (evalArgs (global p) (frame data) 9 (.cons (.local .here) (LiteralFailureCopyEncoding.expressions arguments))).run
 (locals sel extent off len w flag,state first second third)=
 (.ok (.cons (.val (.fixedBytes sel extent)) (values w flag).toR),
 (locals sel extent off len w flag,middle data first second third off len)) := rfl

theorem fields (p : Roadmap.Pipeline) (sel data first second third : Roadmap.Bytes) (extent : sel.length=4)
 (off len : Nat) (w : Roadmap.Word) (flag : Bool) :
 LiteralFailureLocatedFields.Fields (frame data) (middle data first second third off len) (values w flag) (encoded data first off len w flag) := by
 rcases arguments_run (global p) (frame data) 0 .here _ _ (plan sel data first second third extent off len w flag) with
  ⟨vs,mid,actual,fields,kept,next,nonheap⟩
 change (evalArgs (global p) (frame data) 9 (.cons (.local .here) (LiteralFailureCopyEncoding.expressions arguments))).run
  (locals sel extent off len w flag,state first second third)=
  (.ok (.cons (.val (.fixedBytes sel extent)) vs.toR),(locals sel extent off len w flag,mid)) at actual
 rw [actual_arguments] at actual
 have stateEq := congrArg (fun r=>r.2.2) actual
 have valueEq := Except.ok.inj (congrArg Prod.fst actual)
 cases stateEq
 injection valueEq with _ _ _ tailEq
 have valuesEq := values_injective tailEq
 cases valuesEq
 exact fields

theorem actual_expression (p : Roadmap.Pipeline) (sel data first second third : Roadmap.Bytes) (extent : sel.length=4)
 (off len : Nat) (w : Roadmap.Word) (flag : Bool) :
 (evalE (global p) (frame data) 10 expression).run (locals sel extent off len w flag,state first second third)=
 (.ok (.val (.memRef rfl 5)),(locals sel extent off len w flag,result sel data first second third off len w flag)) :=
 SourceAbi.selector_execute (global p) (frame data) 9 _ _ _ _ _ _ _ _ _
 (.val (.fixedBytes sel extent)) (values w flag).toR (.fixedBytes sel extent) _
 (actual_arguments p sel data first second third extent off len w flag)
 (LiteralFailureSelectorBytes.conversion_run (frame data) 9 _ _ _)
 (LiteralFailureLocatedFields.encoding_run (frame data) 9 _ _ (fields p sel data first second third extent off len w flag))

theorem applied (p : Roadmap.Pipeline) (sel data first second third : Roadmap.Bytes) (extent : sel.length=4)
 (off len : Nat) (w : Roadmap.Word) (flag : Bool) :
 ∃ mid : St E,
 (evalE (global p) (frame data) 10 expression).run (locals sel extent off len w flag,state first second third)=
 (.ok (.val (.memRef rfl mid.heap.next)),(locals sel extent off len w flag,SourceKeccak.afterLiteral mid (packet sel data first off len w flag))) ∧
 LiteralFailureConvertedFields.Keeps (frame data) (state first second third) (SourceKeccak.afterLiteral mid (packet sel data first off len w flag)) ∧
 mid.heap.next=5 ∧ (SourceKeccak.afterLiteral mid (packet sel data first off len w flag)).heap.next=6 := by
 rcases expression_run (global p) (frame data) 0 .here _ _ (plan sel data first second third extent off len w flag) with
  ⟨mid,actual,kept,next,count,nonheap⟩
 exact ⟨mid,actual,kept,next,count⟩

theorem selector_prefix (sel data first : Roadmap.Bytes) (extent : sel.length=4)
 (off len : Nat) (w : Roadmap.Word) (flag : Bool) :
 (packet sel data first off len w flag).take 4=sel :=
 by
  have actual := LiteralFailureSelectorBytes.prefix_readback (D:=E.layout) (.fixedBytes sel extent) (AbiEntry.encodeArgs (encoded data first off len w flag))
  exact actual

theorem old_alias (sel data first second third : Roadmap.Bytes) (off len : Nat) (w : Roadmap.Word) (flag : Bool) :
 (result sel data first second third off len w flag).heap.get 1=some ⟨.string .memory,.string first⟩ :=
 LiteralFailureMixedExpression.old_object _ _ _ _ (LiteralFailureMixedExpression.old_object _ _ _ _ rfl)

theorem timeout_after_copy (data first second third : Roadmap.Bytes) :
 (evalE (global .legacy) (frame data) 5 expression).run
 (locals [0,255,128,1] rfl 0 1 ⟨300,by decide +kernel⟩ true,state first second third)=
 (.error .timeout,(locals [0,255,128,1] rfl 0 1 ⟨300,by decide +kernel⟩ true,middle data first second third 0 1)) := rfl

theorem wrong_selector : packet [0,255,128,1] [7] [8] 0 1 ⟨300,by decide +kernel⟩ true ≠
 packet [1,255,128,1] [7] [8] 0 1 ⟨300,by decide +kernel⟩ true := by decide +kernel

def render := LiteralFailureTypedFieldsControls.render
def observe (p : Roadmap.Pipeline) (sel data first : Roadmap.Bytes) (extent : sel.length=4)
 (off len : Nat) (w : Roadmap.Word) (flag : Bool) : String :=
 match (evalE (global p) (frame data) 10 expression).run (locals sel extent off len w flag,state first [128] [171,0]) with
 | (.ok (.val (.memRef _ ptr)),(_,after)) =>
  match after.heap.get ptr,after.heap.get 4,after.heap.get 1 with
  | some ⟨.bytes .memory,.bytes bs⟩,some ⟨.bytes .memory,.bytes copied⟩,some ⟨.string .memory,.string old⟩ =>
   "{\"pointer\":"++toString ptr++",\"cursor\":"++toString after.heap.next++",\"copy\":"++render copied++",\"old\":"++render old++",\"bytes\":"++render bs++"}"
  | _,_,_ => "null"
 | _ => "null"
def suite (p : Roadmap.Pipeline) := "["++String.intercalate "," [
 observe p [0,255,128,1] [] [] rfl 0 0 ⟨0,by decide +kernel⟩ false,
 observe p [1,2,3,4] [99,0,255,128,7] [195,169] rfl 1 3 ⟨300,by decide +kernel⟩ true,
 observe p [255,0,255,0] (List.replicate 31 255++[0]++List.replicate 33 128) (List.replicate 33 255) rfl 32 33 ⟨2^256-1,by decide +kernel⟩ false,
 observe p [128,0,0,255] [0,255,128] (List.replicate 31 0) rfl 99 33 ⟨2^255,by decide +kernel⟩ true,
 observe p [0,0,0,0] ([0]++List.replicate 33 128++[255]) (List.replicate 32 0) rfl 1 32 ⟨42,by decide +kernel⟩ false]++"]"
#eval "COPY_SELECTOR_LEGACY="++suite .legacy
#eval "COPY_SELECTOR_VIAIR="++suite .viaIR
#print axioms values_injective
#print axioms arguments_run
#print axioms expression_run
#print axioms plan
#print axioms actual_arguments
#print axioms fields
#print axioms actual_expression
#print axioms applied
#print axioms selector_prefix
#print axioms old_alias
#print axioms timeout_after_copy
#print axioms wrong_selector
end Solidity.Lowering.V08.LiteralFailureCopySelectorControls
