import Solidity.Lowering.V08.LiteralFailureCopyReturn
import Solidity.Lowering.V08.LiteralFailureCopySelectorControls
namespace Solidity.Lowering.V08.LiteralFailureCopyReturnControls
open Solidity Source
open LiteralFailureCopyReturn
abbrev E := LiteralFailureCopySelectorControls.E
abbrev state := LiteralFailureCopySelectorControls.state
abbrev frame := LiteralFailureCopySelectorControls.frame
abbrev global := LiteralFailureCopySelectorControls.global
abbrev types := LiteralFailureCopySelectorControls.types
abbrev Parameters := LiteralFailureCopySelectorControls.context
abbrev parameters := LiteralFailureCopySelectorControls.locals
abbrev values := LiteralFailureCopySelectorControls.values
abbrev encoded := LiteralFailureCopySelectorControls.encoded
abbrev final := LiteralFailureCopySelectorControls.middle
abbrev Selector := LiteralFailureCopySelector.Selector

def old : Source.Vals E.layout types := .cons (.memRef rfl 0)
 (.cons (SourceEnvironment.sourceWord ⟨7,by decide +kernel⟩) (.cons (.memRef rfl 1) (.cons (.bool false) .nil)))
abbrev context := types.reverseAux Parameters
abbrev liftIndex {τ} (i : Source.Idx Parameters τ) : Source.Idx context τ := .there (.there (.there (.there i)))
def arguments : RConvArgs E context types :=
 .cons (.local (liftIndex (.there .here))) rfl (.cons (.local (liftIndex (.there (.there .here)))) rfl
  (.cons (.local (liftIndex (.there (.there (.there .here))))) rfl
   (.cons (.local (liftIndex (.there (.there (.there (.there .here)))))) rfl .nil)))
def statement : RStmt E types false .body context context := .retTuple arguments

theorem plan (sel data first second third : Roadmap.Bytes) (extent : sel.length=4)
 (off len : Nat) (w : Roadmap.Word) (flag : Bool) :
 LiteralFailureCopySequence.Plan (frame data) (state first second third)
 (old.onto (parameters sel extent off len w flag)) arguments (encoded data first off len w flag) 1 :=
 .cons (liftIndex (.there .here)) rfl (.bytes (liftIndex (.there .here)) off len rfl)
  (.cons (liftIndex (.there (.there .here))) rfl (.read (liftIndex (.there (.there .here))) rfl (.known (.uint w .nil)))
   (.cons (liftIndex (.there (.there (.there .here)))) rfl (.read (liftIndex (.there (.there (.there .here)))) rfl (.known (.string 1 first rfl .nil)))
    (.cons (liftIndex (.there (.there (.there (.there .here))))) rfl (.read (liftIndex (.there (.there (.there (.there .here))))) rfl (.known (.boolean flag .nil))) .nil)))

theorem actual_arguments (p : Roadmap.Pipeline) (sel data first second third : Roadmap.Bytes) (extent : sel.length=4)
 (off len : Nat) (w : Roadmap.Word) (flag : Bool) :
 (evalConvArgs (global p) (frame data) 7 arguments).run
 (old.onto (parameters sel extent off len w flag),state first second third)=
 (.ok (values w flag),(old.onto (parameters sel extent off len w flag),final data first second third off len)) := rfl

theorem actual_return (p : Roadmap.Pipeline) (sel data first second third : Roadmap.Bytes) (extent : sel.length=4)
 (off len : Nat) (w : Roadmap.Word) (flag : Bool) :
 (execS (global p) (frame data) 8 Parameters.length none statement (old.onto (parameters sel extent off len w flag))).run
 (L0 E,state first second third)=
 (.ok (.ret ((values w flag).onto (parameters sel extent off len w flag))),(L0 E,final data first second third off len)) :=
 LiteralFailureReturnSlots.tuple_statement (global p) (frame data) 7 old (values w flag) _ _ _ _ _
 (actual_arguments p sel data first second third extent off len w flag)

theorem derived_encoding (p : Roadmap.Pipeline) (sel data first second third : Roadmap.Bytes) (extent : sel.length=4)
 (off len : Nat) (w : Roadmap.Word) (flag : Bool) :
 (encodeVals (frame data) 7 false (values w flag).toR : EM E [] _).run (L0 E,final data first second third off len)=
 (.ok (AbiEntry.encodeArgs (encoded data first off len w flag)),(L0 E,final data first second third off len)) ∧
 LiteralFailureConvertedFields.Keeps (frame data) (state first second third) (final data first second third off len) ∧
 (final data first second third off len).heap.next=5 := by
 rcases return_run (global p) (frame data) 0 old (parameters sel extent off len w flag) _
  (plan sel data first second third extent off len w flag) with ⟨vs,reached,actual,extracted,encoding,kept,next,nonheap⟩
 change (execS (global p) (frame data) 8 Parameters.length none statement (old.onto (parameters sel extent off len w flag))).run
  (L0 E,state first second third)=(.ok (.ret (vs.onto (parameters sel extent off len w flag))),(L0 E,reached)) at actual
 rw [actual_return] at actual
 have stateEq := congrArg (fun r=>r.2.2) actual
 have returnedEq := Except.ok.inj (congrArg Prod.fst actual)
 cases stateEq
 injection returnedEq with localsEq
 have observed := congrArg (fun l=>retVals l 0 types) localsEq
 dsimp only at observed
 rw [LiteralFailureReturnSlots.extraction,LiteralFailureReturnSlots.extraction] at observed
 have valueEq := LiteralFailureCopySelector.values_injective (Except.ok.inj observed)
 cases valueEq
 exact ⟨encoding,kept,next⟩

theorem older_selector (sel : Roadmap.Bytes) (extent : sel.length=4) (off len : Nat) (w : Roadmap.Word) (flag : Bool) :
 ((values w flag).onto (parameters sel extent off len w flag)).getAt 4 Selector=.ok (.fixedBytes sel extent) :=
 LiteralFailureReturnSlots.get_older (values w flag) (parameters sel extent off len w flag) 0 Selector

theorem old_alias (data first second third : Roadmap.Bytes) (off len : Nat) :
 (final data first second third off len).heap.get 1=some ⟨.string .memory,.string first⟩ :=
 LiteralFailureMixedExpression.old_object _ _ _ _ rfl

theorem no_packet_object (data first second third : Roadmap.Bytes) (off len : Nat) :
 (final data first second third off len).heap.get 5=none := rfl

theorem timeout_after_copy (data first second third : Roadmap.Bytes) :
 (execS (global .legacy) (frame data) 4 Parameters.length none statement
 (old.onto (parameters [0,255,128,1] rfl 0 1 ⟨300,by decide +kernel⟩ true))).run (L0 E,state first second third)=
 (.error .timeout,(L0 E,final data first second third 0 1)) := rfl

theorem empty_return (p : Roadmap.Pipeline) (sel data first second third : Roadmap.Bytes) (extent : sel.length=4)
 (off len : Nat) (w : Roadmap.Word) (flag : Bool) :
 (execS (global p) (frame data) 4 Parameters.length none (.retTuple .nil : RStmt E [] false .body Parameters Parameters)
 (parameters sel extent off len w flag)).run (L0 E,state first second third)=
 (.ok (.ret (parameters sel extent off len w flag)),(L0 E,state first second third)) := rfl

theorem wrong_return_order (sel : Roadmap.Bytes) (extent : sel.length=4) (off len : Nat) (w : Roadmap.Word) (flag : Bool) :
 retVals ((values w flag).onto (parameters sel extent off len w flag)) 0 [.int IntTy.u256,.bytes .memory,.string .memory,.bool]=
 .error (.stuck "local type") := rfl

def render := LiteralFailureTypedFieldsControls.render
def observe (p : Roadmap.Pipeline) (sel data first : Roadmap.Bytes) (extent : sel.length=4)
 (off len : Nat) (w : Roadmap.Word) (flag : Bool) : String :=
 match (execS (global p) (frame data) 8 Parameters.length none statement
 (old.onto (parameters sel extent off len w flag))).run (L0 E,state first [128] [171,0]) with
 | (.ok (.ret returned),(_,after)) =>
  match retVals returned 0 types,returned.getAt 4 Selector with
  | .ok vs@(.cons (.val (.memRef _ ptr)) _),.ok (.fixedBytes retained _) =>
   match (encodeVals (frame data) 7 false vs : EM E [] _).run (L0 E,after) with
   | (.ok bs,(_,last)) =>
    match last.heap.get ptr,last.heap.get 1,last.heap.get 5 with
    | some ⟨.bytes .memory,.bytes copied⟩,some ⟨.string .memory,.string oldBytes⟩,none =>
     "{\"return_pointer\":"++toString ptr++",\"cursor\":"++toString last.heap.next++",\"copy\":"++render copied++",\"old\":"++render oldBytes++",\"selector\":"++render retained++",\"bytes\":"++render bs++"}"
    | _,_,_ => "null"
   | _ => "null"
  | _,_ => "null"
 | _ => "null"
def suite (p : Roadmap.Pipeline) := "["++String.intercalate "," [
 observe p [0,255,128,1] [] [] rfl 0 0 ⟨0,by decide +kernel⟩ false,
 observe p [1,2,3,4] [99,0,255,128,7] [195,169] rfl 1 3 ⟨300,by decide +kernel⟩ true,
 observe p [255,0,255,0] (List.replicate 31 255++[0]++List.replicate 33 128) (List.replicate 33 255) rfl 32 33 ⟨2^256-1,by decide +kernel⟩ false,
 observe p [128,0,0,255] [0,255,128] (List.replicate 31 0) rfl 99 33 ⟨2^255,by decide +kernel⟩ true,
 observe p [0,0,0,0] ([0]++List.replicate 33 128++[255]) (List.replicate 32 0) rfl 1 32 ⟨42,by decide +kernel⟩ false]++"]"
#eval "COPY_RETURN_LEGACY="++suite .legacy
#eval "COPY_RETURN_VIAIR="++suite .viaIR
#print axioms return_run
#print axioms plan
#print axioms actual_arguments
#print axioms actual_return
#print axioms derived_encoding
#print axioms older_selector
#print axioms old_alias
#print axioms no_packet_object
#print axioms timeout_after_copy
#print axioms empty_return
#print axioms wrong_return_order
end Solidity.Lowering.V08.LiteralFailureCopyReturnControls
