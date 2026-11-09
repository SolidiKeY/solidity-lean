import Solidity.Backend.InternalFlow.RuntimeFrameP1V2ReferenceAgreement
import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducerRefStructDefaultControls

/-! Regression: nested finite reference-bearing struct defaults must retain
fresh children and old aliases across a captured return. The existing public
compileMemoryCall selector supplies actual cost-five construction and a real
index-zero success/index-two failure. General V2 simulation remains separate
from diagnostic word snapshots; missing export and capacity are refused. This
adds no reference-element-array, recursive-copy or actual-Source admission. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.P1V2ReferenceControls
open Evm Evm.Memory V3CallProducerRef.StructDefault.Controls

/-- Actual populated caller and cursor; every legal index and preexisting
journal/buffer is retained, rather than a two-input admission whitelist. -/
def input (n : Fin W) (journal : List CallRec) (buffer : List UInt8) : P1LangV2.Input C Γ :=
  ⟨1,64,caller n,bases,{base := machine n,calls := journal,returndata := buffer},20⟩

theorem physical_success (journal : List CallRec) (buffer : List UInt8) :
    ∃ (out : Solidity.Out C (caller (wmod 0)).H (.mem S :: Γ)), ∃ target addresses,
      call.run (caller (wmod 0)) = .ok out ∧
      runV2 (lift (V3CallProducerRef.plan selected 16 16).code) (input (wmod 0) journal buffer).machine =
        .ok ((input (wmod 0) journal buffer).machine.withBase target) 0 ∧
      StateRepr 1 1 64 selected.checked.frag out.st addresses target ∧
      target.stack = (machine (wmod 0)).stack ∧
      BaseExtends (caller (wmod 0)).H bases addresses ∧
      GrowsAllocator 1 64 (selected.checked.cost (caller (wmod 0)))
        (caller (wmod 0)) bases (machine (wmod 0)) out.st addresses target ∧
      target.mem 16 = .val (wmod 20) ∧
      Footprint.Words 16 20 (machine (wmod 0)) target := by
  obtain ⟨out,source⟩ := source_success
  obtain ⟨target,addresses,executed,represented,stack,extended,growth,cursor,older⟩ :=
    P1V2ReferenceAgreement.returns form selected 16 16 flags (input (wmod 0) journal buffer)
      (entered (wmod 0)) out source
  exact ⟨out,target,addresses,source,executed,represented,stack,extended,growth,cursor,older⟩

/-- Universal agreement for the SAME selected family, not only the witnesses. -/
theorem all_indices (n : Fin W) (journal : List CallRec) (buffer : List UInt8) :
    P1LangV2.targetSem (lift (V3CallProducerRef.plan selected 16 16).code)
      (input n journal buffer) = P1LangV2.sourcePrefix (call.run (caller n)) :=
  P1V2ReferenceAgreement.agree form selected 16 16 flags (input n journal buffer) (entered n)

/-- Default allocation is reached before the OOB failure; no post-revert
machine, restored allocator or rollback is inferred from this error outcome. -/
theorem allocated_failure (journal : List CallRec) (buffer : List UInt8) :
    runV2 (lift (V3CallProducerRef.plan selected 16 16).code)
      (input (wmod 2) journal buffer).machine = .revert journal [] :=
  P1V2ReferenceAgreement.bare_revert selected 16 16 (input (wmod 2) journal buffer)
    (entered (wmod 2)) source_revert

/-- Diagnostic graph observation of actual V2 execution. Physical simulation
and all V2 metadata are retained separately by physical_success above. -/
theorem graph_snapshot (journal : List CallRec) (buffer : List UInt8) :
    targetObservation (runV2 (lift (V3CallProducerRef.plan selected 16 16).code)
      (input (wmod 0) journal buffer).machine).forget =
      some [77,135,128,0,133,20,99,1,0,0,0,130,131,0,0] := by
  rw [forget_run_lift]
  exact target_observation

/-- Actually omitting result compaction cannot reproduce the graph snapshot. -/
theorem missing_export (journal : List CallRec) (buffer : List UInt8) :
    targetObservation (runV2 (lift missingExport) (input (wmod 0) journal buffer).machine).forget ≠
      some [77,135,128,0,133,20,99,1,0,0,0,130,131,0,0] := by
  rw [forget_run_lift]
  exact missing_export_refused

/-- Cost-five capacity is a real input duty, never an inferred runtime error. -/
theorem capacity_refusal (journal : List CallRec) (buffer : List UInt8) :
    ¬ AllocationInput 1 64 (selected.checked.cost (caller (wmod 0))) (caller (wmod 0)) bases
      ({base := writeMachine (machine (wmod 0)) 0 (.val (wmod (W-1))),
        calls := journal,returndata := buffer} : MachineV2).base :=
  capacity_refused

end Solidity.Backend.InternalFlow.RuntimeFrame.P1V2ReferenceControls
