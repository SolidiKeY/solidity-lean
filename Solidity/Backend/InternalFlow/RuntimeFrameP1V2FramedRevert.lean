import Solidity.Backend.InternalFlow.RuntimeFrameV3BareRevertProducer
import Solidity.Backend.InternalFlow.RuntimeFrameP1V2Lift

/-! Guard against dropping the physical Entry or the reverting-entry witness
when moving a captured call to the canonical V2 endpoint. The actual certified
save/body/restore image is executed; arbitrary V2 journals are retained. This
bare-failure transport is not an all-outcome P1 or library adequacy producer. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.P1V2FramedRevert
open Evm Evm.Memory

/-- Captured execution, with all original physical premises and the actual
source failure. No target-execution premise is supplied. -/
theorem run_revert {C : Contract} {Γ Δ : Ctx} {b : Nat} {F : Frag Γ}
    {statement : Stmt C Γ Δ}
    (selected : Composition.Program b F (.cons statement .nil)) (lo pointer : Nat)
    (e : P1LangV2.Input C Γ)
    (entry : InterfaceV1.Entry (V3BareRevertProducer.plan selected lo pointer)
      e.L b e.frame F e.caller e.base e.machine.base e.start)
    (source : statement.run e.caller = .error .revert) :
    runV2 (lift (V3BareRevertProducer.plan selected lo pointer).code) e.machine =
      .revert e.machine.calls [] := by
  exact run_lift_revert
    (V3BareRevertProducer.bare_revert selected lo pointer e.L e.frame e.caller
      e.base e.machine.base e.start entry source)

/-- The SAME canonical source and target observations, under the SAME Entry.
This proves the bare-revert branch without imposing it as an Approved filter. -/
theorem prefix_revert {C : Contract} {Γ Δ : Ctx} {b : Nat} {F : Frag Γ}
    {statement : Stmt C Γ Δ}
    (selected : Composition.Program b F (.cons statement .nil)) (lo pointer : Nat)
    (e : P1LangV2.Input C Γ)
    (entry : InterfaceV1.Entry (V3BareRevertProducer.plan selected lo pointer)
      e.L b e.frame F e.caller e.base e.machine.base e.start)
    (source : statement.run e.caller = .error .revert) :
    P1LangV2.targetSem (lift (V3BareRevertProducer.plan selected lo pointer).code) e =
      P1LangV2.sourcePrefix (statement.run e.caller) := by
  rw [source]
  simp only [P1LangV2.targetSem, run_revert selected lo pointer e entry source,
    P1LangV2.targetPrefix, P1LangV2.sourcePrefix, P1LangV2.eventsAfter_existing]

end Solidity.Backend.InternalFlow.RuntimeFrame.P1V2FramedRevert
