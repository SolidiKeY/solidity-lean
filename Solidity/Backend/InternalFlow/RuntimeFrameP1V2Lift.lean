import Solidity.Backend.InternalFlow.RuntimeFrameP1LangV2Migration

/-! H121 producer support: guard against treating frozen-code lifting as a
payload or event producer. The exact canonical V2 observation is derived from
the actual lifted execution for every machine and code image. No new language,
admission restriction or complete P1/library producer is introduced. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.P1LangV2
open Evm
open Solidity.Roadmap (Event Outcome Prefix)

/-- A journal prefix that was already present contributes no new events. -/
theorem eventsAfter_existing (self : Fin W) (calls : List CallRec) :
    eventsAfter self calls.length calls = [] := by
  simp only [eventsAfter,List.drop_length,List.filter_nil,List.map_nil,List.flatten_nil]

/-- Frozen instructions cannot acquire additional observed events or revert
payload merely by lifting. This is exact, not just an equality after coarsening. -/
theorem lift_prefix_exact (code : List Instr) (machine : MachineV2) :
    targetPrefix machine.base.self machine.calls.length (runV2 (lift code) machine) =
      P1Lang.targetPrefix (run code machine.base) := by
  rw [run_lift]
  cases h : run code machine.base with
  | ok state skip =>
    cases skip <;>
      simp only [OutV2.ofOut,targetPrefix,P1Lang.targetPrefix,MachineV2.withBase,eventsAfter_existing]
  | revert => simp only [OutV2.ofOut,targetPrefix,P1Lang.targetPrefix,eventsAfter_existing]
  | fault => rfl

/-- Exact target endpoint equation for the existing canonical P1 languages.
It supplies no Source/frame admission or all-outcome agreement premise. -/
theorem targetSem_lift_exact {C : Contract} {Γ : Ctx} (code : List Instr) (e : Input C Γ) :
    targetSem (lift code) e = P1Lang.targetPrefix (run code e.machine.base) :=
  lift_prefix_exact code e.machine

end Solidity.Backend.InternalFlow.RuntimeFrame.P1LangV2
