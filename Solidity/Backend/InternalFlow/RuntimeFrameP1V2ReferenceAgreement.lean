import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducerRef
import Solidity.Backend.InternalFlow.RuntimeFrameP1V2CallAgreement

/-! Regression: a reference/tuple call must preserve its fresh result and old
aliases through caller restoration. Execute the existing certified reference
plan on MachineV2, retaining its complete physical return tuple and all prior
V2 fields. Source classification uses the same actual checked input, not a
success-only approved domain. Form is the existing typed CallRet certificate,
not a new AST. No Source admission, recursive graph copying or full P1/session
adequacy is introduced. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.P1V2ReferenceAgreement
open Evm Evm.Memory
variable {C : Contract} {Γ Δ ps rs Γf : Ctx} {b : Nat} {F : Frag Γ}
  {f : Name} {args : Args C Γ ps} {ret : CallRet Γ rs Δ}
  {body : Prog C (rs ++ ps) Γf} {scope : Ext Γ Δ}

/-- The larger result/context bound supplies only the checked-body Entry used
for source classification; actual execution retains the reference plan. -/
theorem checked_entry
    (selected : Composition.Program b F (.cons (.call f args ret body) .nil))
    (lo pointer : Nat) (e : P1LangV2.Input C Γ)
    (entry : InterfaceV1.Entry (V3CallProducerRef.plan selected lo pointer)
      e.L b e.frame F e.caller e.base e.machine.base e.start) :
    InterfaceV1.Entry (V3BareRevertProducer.plan selected lo pointer)
      e.L b e.frame F e.caller e.base e.machine.base e.start := by
  have workspace := entry.workspace
  change b + max selected.checked.need (max Γ.length Δ.length) ≤ lo at workspace
  exact ⟨entry.represented,entry.callerBound,entry.resultBound,
    by change b + selected.checked.need ≤ lo; omega,
    entry.pointerAbove,entry.pointerBelow,entry.payloadAbove,entry.reserve,
    entry.controlSpace,entry.separate,entry.noWrap,entry.cursor,entry.capacity⟩

/-- Actual V2 execution accompanies every original physical return fact,
including the heap/base extension, allocation growth and protected old words. -/
theorem returns (form : V3CallProducerRef.Form Γ ret scope)
    (selected : Composition.Program b F (.cons (.call f args ret body) .nil))
    (lo pointer : Nat)
    (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag scope)
    (e : P1LangV2.Input C Γ)
    (entry : InterfaceV1.Entry (V3CallProducerRef.plan selected lo pointer)
      e.L b e.frame F e.caller e.base e.machine.base e.start)
    (out : Solidity.Out C e.caller.H Δ)
    (source : (Stmt.call f args ret body).run e.caller = .ok out) :
    ∃ target addresses,
      runV2 (lift (V3CallProducerRef.plan selected lo pointer).code) e.machine =
        .ok (e.machine.withBase target) 0 ∧
      StateRepr e.L b e.frame selected.checked.frag out.st addresses target ∧
      target.stack = e.machine.base.stack ∧
      BaseExtends e.caller.H e.base addresses ∧
      GrowsAllocator b e.frame (selected.checked.cost e.caller) e.caller e.base
        e.machine.base out.st addresses target ∧
      target.mem pointer = .val (wmod e.start) ∧
      Footprint.Words lo e.start e.machine.base target := by
  obtain ⟨target,addresses,executed,represented,stack,extended,growth,cursor,older⟩ :=
    V3CallProducerRef.returns form selected lo pointer flags e.L e.frame e.caller
      e.base e.machine.base e.start entry out source
  exact ⟨target,addresses,run_lift_ok executed,represented,stack,extended,growth,cursor,older⟩

/-- Bare failure of the same allocating call image retains the journal; it
supplies no post-failure machine and does not relabel panic/payload failure. -/
theorem bare_revert
    (selected : Composition.Program b F (.cons (.call f args ret body) .nil))
    (lo pointer : Nat) (e : P1LangV2.Input C Γ)
    (entry : InterfaceV1.Entry (V3CallProducerRef.plan selected lo pointer)
      e.L b e.frame F e.caller e.base e.machine.base e.start)
    (source : (Stmt.call f args ret body).run e.caller = .error .revert) :
    runV2 (lift (V3CallProducerRef.plan selected lo pointer).code) e.machine =
      .revert e.machine.calls [] :=
  run_lift_revert (V3CallProducerRef.bare_revert selected lo pointer e.L e.frame
    e.caller e.base e.machine.base e.start entry source)

/-- Both actual source outcomes agree in the existing canonical V2 language,
under the original physical and alias conditions for this typed return form. -/
theorem agree (form : V3CallProducerRef.Form Γ ret scope)
    (selected : Composition.Program b F (.cons (.call f args ret body) .nil))
    (lo pointer : Nat)
    (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag scope)
    (e : P1LangV2.Input C Γ)
    (entry : InterfaceV1.Entry (V3CallProducerRef.plan selected lo pointer)
      e.L b e.frame F e.caller e.base e.machine.base e.start) :
    P1LangV2.targetSem (lift (V3CallProducerRef.plan selected lo pointer).code) e =
      P1LangV2.sourcePrefix ((Stmt.call f args ret body).run e.caller) := by
  rcases P1V2CallAgreement.source_outcomes selected lo pointer e
      (checked_entry selected lo pointer e entry) with ⟨out,source⟩ | source
  · obtain ⟨target,addresses,executed,represented,stack,extended,growth,cursor,older⟩ :=
      returns form selected lo pointer flags e entry out source
    simp only [P1LangV2.targetSem,executed,P1LangV2.targetPrefix,MachineV2.withBase,
      P1LangV2.eventsAfter_existing,source,P1LangV2.sourcePrefix]
  · simp only [P1LangV2.targetSem,bare_revert selected lo pointer e entry source,
      P1LangV2.targetPrefix,P1LangV2.eventsAfter_existing,source,P1LangV2.sourcePrefix]

end Solidity.Backend.InternalFlow.RuntimeFrame.P1V2ReferenceAgreement
