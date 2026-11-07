import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducer
import Solidity.Backend.InternalFlow.RuntimeFrameP1V2CallAgreement

/-! Regression: observing success is insufficient for a value-returning call
if caller restoration overwrites the result. Execute the existing certified
private-result/capture/restore/export image on MachineV2, retaining every physical
return fact. Source outcome classification is derived from the same checked
compiler input; Approved is neither defined nor filtered. No second language or
complete P1/profile/library adequacy producer is introduced here. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.P1V2ValueAgreement
open Evm Evm.Memory
variable {C : Contract} {Γ ps Γf : Ctx} {b : Nat} {F : Frag Γ}
  {f : Name} {args : Args C Γ ps} {p : PrimTy} {r : Var}
  {destination : Idx Γ (.val p)} {body : Prog C (.val p :: ps) Γf}

/-- The value plan's larger private-cell bound supplies the checked-body Entry
used only for source classification. It does not replace the executed image. -/
theorem checked_entry
    (selected : Composition.Program b F
      (.cons (.call f args (.val p r (some destination)) body) .nil))
    (lo pointer : Nat) (e : P1LangV2.Input C Γ)
    (entry : InterfaceV1.Entry (V3CallProducer.plan selected lo pointer)
      e.L b e.frame F e.caller e.base e.machine.base e.start) :
    InterfaceV1.Entry (V3BareRevertProducer.plan selected lo pointer)
      e.L b e.frame F e.caller e.base e.machine.base e.start := by
  have workspace := entry.workspace
  change b + (max selected.checked.need Γ.length + 1) ≤ lo at workspace
  exact ⟨entry.represented,entry.callerBound,entry.resultBound,by change b + selected.checked.need ≤ lo; omega,
    entry.pointerAbove,entry.pointerBelow,entry.payloadAbove,entry.reserve,
    entry.controlSpace,entry.separate,entry.noWrap,entry.cursor,entry.capacity⟩

/-- Every original physical return fact accompanies the actual V2 run.
Arbitrary preexisting V2 fields are retained through MachineV2.withBase. -/
theorem returns
    (selected : Composition.Program b F
      (.cons (.call f args (.val p r (some destination)) body) .nil))
    (lo pointer : Nat)
    (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag .refl)
    (e : P1LangV2.Input C Γ)
    (entry : InterfaceV1.Entry (V3CallProducer.plan selected lo pointer)
      e.L b e.frame F e.caller e.base e.machine.base e.start)
    (out : Solidity.Out C e.caller.H Γ)
    (source : (Stmt.call f args (.val p r (some destination)) body).run e.caller = .ok out) :
    ∃ target addresses,
      runV2 (lift (V3CallProducer.plan selected lo pointer).code) e.machine =
        .ok (e.machine.withBase target) 0 ∧
      StateRepr e.L b e.frame selected.checked.frag out.st addresses target ∧
      target.stack = e.machine.base.stack ∧
      BaseExtends e.caller.H e.base addresses ∧
      GrowsAllocator b e.frame (selected.checked.cost e.caller) e.caller e.base
        e.machine.base out.st addresses target ∧
      target.mem pointer = .val (wmod e.start) ∧
      Footprint.Words lo e.start e.machine.base target := by
  obtain ⟨target,addresses,executed,represented,stack,extended,growth,cursor,older⟩ :=
    V3CallProducer.returns selected lo pointer flags e.L e.frame e.caller e.base
      e.machine.base e.start entry out source
  exact ⟨target,addresses,run_lift_ok executed,represented,stack,extended,growth,cursor,older⟩

/-- The same private-result image, not the simpler void plan, handles failure. -/
theorem bare_revert
    (selected : Composition.Program b F
      (.cons (.call f args (.val p r (some destination)) body) .nil))
    (lo pointer : Nat) (e : P1LangV2.Input C Γ)
    (entry : InterfaceV1.Entry (V3CallProducer.plan selected lo pointer)
      e.L b e.frame F e.caller e.base e.machine.base e.start)
    (source : (Stmt.call f args (.val p r (some destination)) body).run e.caller = .error .revert) :
    runV2 (lift (V3CallProducer.plan selected lo pointer).code) e.machine =
      .revert e.machine.calls [] :=
  run_lift_revert (V3CallProducer.bare_revert selected lo pointer e.L e.frame
    e.caller e.base e.machine.base e.start entry source)

/-- Both actual source outcomes agree with the SAME canonical V2 endpoint.
No successful-run or no-failure predicate narrows the physical input domain. -/
theorem agree
    (selected : Composition.Program b F
      (.cons (.call f args (.val p r (some destination)) body) .nil))
    (lo pointer : Nat)
    (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag .refl)
    (e : P1LangV2.Input C Γ)
    (entry : InterfaceV1.Entry (V3CallProducer.plan selected lo pointer)
      e.L b e.frame F e.caller e.base e.machine.base e.start) :
    P1LangV2.targetSem (lift (V3CallProducer.plan selected lo pointer).code) e =
      P1LangV2.sourcePrefix ((Stmt.call f args (.val p r (some destination)) body).run e.caller) := by
  rcases P1V2CallAgreement.source_outcomes selected lo pointer e
      (checked_entry selected lo pointer e entry) with ⟨out,source⟩ | source
  · obtain ⟨target,addresses,executed,represented,stack,extended,growth,cursor,older⟩ :=
      returns selected lo pointer flags e entry out source
    simp only [P1LangV2.targetSem, executed, P1LangV2.targetPrefix, MachineV2.withBase,
      P1LangV2.eventsAfter_existing, source, P1LangV2.sourcePrefix]
  · simp only [P1LangV2.targetSem, bare_revert selected lo pointer e entry source,
      P1LangV2.targetPrefix, P1LangV2.eventsAfter_existing, source, P1LangV2.sourcePrefix]

end Solidity.Backend.InternalFlow.RuntimeFrame.P1V2ValueAgreement
