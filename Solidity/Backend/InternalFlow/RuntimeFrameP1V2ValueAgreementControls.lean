import Solidity.Backend.InternalFlow.RuntimeFrameP1V2ValueAgreement
import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducerControls

/-! Regression: restoring caller locals must not overwrite a primitive call
result. The real Composition.compileCall readAt image returns seven at index
zero and bare-reverts at index two on the SAME physical family. Nonempty saved
stack, private result export, cursor, arbitrary V2 journal/buffer and refusal of
an insufficient capture arena remain explicit. No approved domain is invented. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.P1V2ValueAgreementControls
open Evm Evm.Memory V3CallProducer.Controls

def positive (journal : List CallRec) (buffer : List UInt8) : P1LangV2.Input P Γ :=
  ⟨1,16,initial,bases,{base := machine, calls := journal, returndata := buffer},10⟩

def negative (journal : List CallRec) (buffer : List UInt8) : P1LangV2.Input P Γ :=
  ⟨1,16,failing,bases,{base := failedMachine, calls := journal, returndata := buffer},10⟩

/-- The returned seven is exported AFTER restoration; the old caller value
cannot silently replace it. The saved input stack and cursor are retained. -/
theorem exported (journal : List CallRec) (buffer : List UInt8) :
    ∃ target,
      runV2 (lift (V3CallProducer.plan selected 8 8).code) (positive journal buffer).machine =
        .ok ((positive journal buffer).machine.withBase target) 0 ∧
      target.mem 3 = w[7] ∧ target.stack = [w[77]] ∧ target.mem 8 = w[10] := by
  obtain ⟨target,addresses,executed,represented,stack,extended,growth,cursor,older⟩ :=
    P1V2ValueAgreement.returns selected 8 8 flags (positive journal buffer) positive_entry
      ⟨output,List.prefix_refl _⟩ source_success
  have value := represented.core.vals (.here : Idx Γ (.val .uint))
  change ReprV .uint (uint 7 (by decide)) (target.mem 3) at value
  exact ⟨target,executed,Restored.value_unique value (ReprV.uint_of rfl),stack,cursor⟩

theorem success_prefix (journal : List CallRec) (buffer : List UInt8) :
    P1LangV2.targetSem (lift (V3CallProducer.plan selected 8 8).code)
      (positive journal buffer) = ⟨[],some (.success [])⟩ := by
  rw [P1V2ValueAgreement.agree selected 8 8 flags (positive journal buffer) positive_entry]
  change P1LangV2.sourcePrefix (call.run initial) = _
  rw [source_success]
  rfl

/-- The SAME selected source call and target image reach the other outcome. -/
theorem failure_run (journal : List CallRec) (buffer : List UInt8) :
    runV2 (lift (V3CallProducer.plan selected 8 8).code) (negative journal buffer).machine =
      .revert journal [] :=
  P1V2ValueAgreement.bare_revert selected 8 8 (negative journal buffer) negative_entry source_revert

theorem failure_prefix (journal : List CallRec) (buffer : List UInt8) :
    P1LangV2.targetSem (lift (V3CallProducer.plan selected 8 8).code)
      (negative journal buffer) = ⟨[],some (.revert [])⟩ := by
  rw [P1V2ValueAgreement.agree selected 8 8 flags (negative journal buffer) negative_entry]
  change P1LangV2.sourcePrefix (call.run failing) = _
  rw [source_revert]
  rfl

/-- A represented caller and matching cursor alone cannot admit an arena
that overlaps the frame boundary. V2 metadata provides no missing capacity. -/
theorem capacity_refused (journal : List CallRec) (buffer : List UInt8) :
    ¬ V3CallProducer.admitted selected 8 8 1 16 initial bases
      ({base := capacityMachine, calls := journal, returndata := buffer} : MachineV2).base 14 :=
  refuses_arena_capacity

end Solidity.Backend.InternalFlow.RuntimeFrame.P1V2ValueAgreementControls
