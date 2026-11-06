import Solidity.Lowering.Readonly.CallSupportEffects
import Solidity.Lowering.Readonly.TupleCopyEffects
import Solidity.Lowering.Readonly.CopyControls

/-! Populated actual helper runs. Allocation and events remain observable in static
mode; partial failures retain reached state. No ABI/native adequacy is asserted. -/
namespace Solidity.Lowering.Readonly.HelperControls
open Solidity.Source Solidity.Source.SemanticsExamples
open SourceHistory
namespace C
abbrev E := CopyControls.E
abbrev frame := CopyControls.frame
abbrev checkpoint := CopyControls.checkpoint
abbrev memory := CopyControls.loaded.2.2
end C

def event : Solidity.Roadmap.Event := .call ext (word 0) [7] true
def eventResult := (emitEvent event : EM EB [] Unit).run (L0 EB, sB)
def answer (out : Solidity.Roadmap.Outcome) := (reraise out : EM EB [] _).run (L0 EB, sB)
def lookup (a : Solidity.Roadmap.Address) :=
  (instanceAt (GB (fun _ => .answer (.success []))) a : EM EB [] _).run (L0 EB, sB)
def marked := (mark : EM C.E [] _).run (L0 C.E, C.checkpoint)
def action (x : Bool) : EM EB [] Bool := do
  if x then emitEvent event; pure true else EM.halt (.revert [9])
def mapped := (List.mapM action [true, false, true]).run (L0 EB, sB)
def converted := (convRV {C.frame with static := true} 12 (.bytes .memory)
  (RVal.val CopyControls.sourceRef) : EM C.E [] _).run (L0 C.E, C.checkpoint)
def conversionRefused := (convRV {C.frame with static := true} 12 .bool
  (RVal.val (Solidity.Source.Val.memRef (τ := .bytes .memory) rfl 0)) :
  EM C.E [] _).run (L0 C.E, C.memory)
def explicitBytes := (convExplicitRV {C.frame with static := true} 12
  (.fixedBytes 2 (by decide)) (RVal.val CopyControls.sourceRef) :
  EM C.E [] _).run (L0 C.E, C.checkpoint)
def shortRead := (bytesOfRV {C.frame with static := true} 0
  (RVal.val CopyControls.sourceRef) : EM C.E [] _).run (L0 C.E, C.checkpoint)
def calldataCopy := (cdToMem {C.frame with static := true, cd := [7,9]}
  (.bytes .memory) 0 2 : EM C.E [] _).run (L0 C.E, C.checkpoint)
def calldataRefused := (cdToMem {C.frame with static := true} .bool 0 1 :
  EM C.E [] _).run (L0 C.E, C.checkpoint)

theorem observations : Solidity.Lowering.Readonly.HelperControls.eventResult.1 = .ok () ∧
 Solidity.Lowering.Readonly.HelperControls.eventResult.2.2.events = [Solidity.Lowering.Readonly.HelperControls.event] ∧
 Solidity.Lowering.Readonly.HelperControls.eventResult.2.2.ex = Solidity.Source.SemanticsExamples.sB.ex ∧
 (Solidity.Lowering.Readonly.HelperControls.answer (.success [7,9])).1 = .ok [7,9] ∧
 (Solidity.Lowering.Readonly.HelperControls.answer (.revert [7,9])).1 = .error (.revert [7,9]) ∧
 (Solidity.Lowering.Readonly.HelperControls.lookup Solidity.Source.SemanticsExamples.thisC).1 = .ok (some "C") ∧
 (Solidity.Lowering.Readonly.HelperControls.lookup Solidity.Source.SemanticsExamples.ext).1 = .ok none ∧
 Solidity.Lowering.Readonly.HelperControls.marked.1 = .ok (7,0,Solidity.Lowering.Readonly.HelperControls.C.checkpoint.heap) ∧
 Solidity.Lowering.Readonly.HelperControls.mapped.1 = .error (.revert [9]) ∧
 Solidity.Lowering.Readonly.HelperControls.mapped.2.2.events = [Solidity.Lowering.Readonly.HelperControls.event] ∧
 Solidity.Lowering.Readonly.HelperControls.mapped.2.2.ex = Solidity.Source.SemanticsExamples.sB.ex ∧
 Solidity.Lowering.Readonly.HelperControls.converted.1 = .ok (.val (.memRef (by rfl) 0)) ∧
 Solidity.Lowering.Readonly.HelperControls.converted.2.2.heap.get 0 = some ⟨.bytes .memory, .bytes [7,9]⟩ ∧
 Solidity.Lowering.Readonly.HelperControls.converted.2.2.ex = Solidity.Lowering.Readonly.HelperControls.C.checkpoint.ex ∧
 Solidity.Lowering.Readonly.HelperControls.conversionRefused.1 = .error (.stuck "memory to non-memory") ∧
 Solidity.Lowering.Readonly.HelperControls.conversionRefused.2.2.heap.get 0 = some ⟨.bytes .memory, .bytes [7,9]⟩ ∧
 Solidity.Lowering.Readonly.HelperControls.explicitBytes.1 = .ok (.val (.fixedBytes [7,9] (by rfl))) ∧
 Solidity.Lowering.Readonly.HelperControls.explicitBytes.2.2.ex = Solidity.Lowering.Readonly.HelperControls.C.checkpoint.ex ∧
 Solidity.Lowering.Readonly.HelperControls.shortRead.1 = .error .timeout ∧
 Solidity.Lowering.Readonly.HelperControls.calldataCopy.1 = .ok (.val (.memRef (by rfl) 0)) ∧
 Solidity.Lowering.Readonly.HelperControls.calldataCopy.2.2.heap.get 0 = some ⟨.bytes .memory, .bytes [7,9]⟩ ∧
 Solidity.Lowering.Readonly.HelperControls.calldataCopy.2.2.ex = Solidity.Lowering.Readonly.HelperControls.C.checkpoint.ex ∧
 Solidity.Lowering.Readonly.HelperControls.calldataRefused.1 = .error (.stuck "calldata conversion") := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

theorem action_effect : ∀ mode x, Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Lowering.Readonly.HelperControls.action x) := by
  intro mode x
  unfold Solidity.Lowering.Readonly.HelperControls.action
  split
  · exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (Solidity.Lowering.Readonly.SourceHistory.emitEvent_effect mode _) (fun _ => Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _)
  · exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _

theorem failure_keeps_event : Solidity.Lowering.Readonly.HelperControls.mapped.2.2.events ≠ Solidity.Source.SemanticsExamples.sB.events := by
  decide

def tupleValues : RVals C.E.layout [.bytes .storage] :=
  .cons (.val CopyControls.sourceRef) .nil
def tupleGood := (pushVals (Γ' := []) {C.frame with static := true} 12
  [some (.bytes .memory)] tupleValues (Locals.nil : Locals C.E.layout []) :
  EM C.E [] _).run (L0 C.E, C.checkpoint)
def tuplePartial := (pushVals (Γ' := []) {C.frame with static := true} 12
  [some (.bytes .memory), some .bool] tupleValues (Locals.nil : Locals C.E.layout []) :
  EM C.E [] _).run (L0 C.E, C.checkpoint)
def tupleSkip := (pushVals (Γ' := []) {C.frame with static := true} 0
  [none] tupleValues (Locals.nil : Locals C.E.layout []) :
  EM C.E [] _).run (L0 C.E, C.checkpoint)


theorem tuple_observations : Solidity.Lowering.Readonly.HelperControls.tupleGood.1 = .ok (.cons (.memRef (by rfl) 0) .nil) ∧
 Solidity.Lowering.Readonly.HelperControls.tupleGood.2.2.heap.next = 1 ∧
 Solidity.Lowering.Readonly.HelperControls.tupleGood.2.2.ex = Solidity.Lowering.Readonly.HelperControls.C.checkpoint.ex ∧
 Solidity.Lowering.Readonly.HelperControls.tuplePartial.1 = .error (.stuck "tuple declaration arity") ∧
 Solidity.Lowering.Readonly.HelperControls.tuplePartial.2.2.heap.get 0 = some ⟨.bytes .memory, .bytes [7,9]⟩ ∧
 Solidity.Lowering.Readonly.HelperControls.tuplePartial.2.2.ex = Solidity.Lowering.Readonly.HelperControls.C.checkpoint.ex ∧
 Solidity.Lowering.Readonly.HelperControls.tupleSkip.1 = .ok .nil ∧
 Solidity.Lowering.Readonly.HelperControls.tupleSkip.2.2.heap.next = 0 ∧
 Solidity.Lowering.Readonly.HelperControls.tupleSkip.2.2.ex = Solidity.Lowering.Readonly.HelperControls.C.checkpoint.ex := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

end Solidity.Lowering.Readonly.HelperControls
