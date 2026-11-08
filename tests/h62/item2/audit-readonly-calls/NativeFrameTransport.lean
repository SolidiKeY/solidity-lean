import CheckedExecutionCall

/-! Guard loss of the actual child machine when a compiler-selected void call's
Returned contract is lifted to V2. Representation, base extension, allocator,
cursor and protected older words refer to the SAME executed child base. V2
journal, return buffer and reply function are retained as well. This is the
existing typed-core void family, not resolved Source/world selection, child
state commit to CALLIN, general P1, reference returns or full H121 adequacy. -/
namespace Solidity.H62.ReadonlyCalls.NativeFrameTransport
open Solidity Solidity.Evm Solidity.Evm.Memory
open Solidity.Backend.InternalFlow.RuntimeFrame
open Solidity.H62.ReadonlyCalls.ExecutionReplies

/-- The frozen Returned physical obligations, indexed by the executed V2 child.
This adds no admission assumption and changes no existing interface. -/
def NativeReturned {C : Contract} {Γ Δ : Ctx}
    (plan : InterfaceV1.Emission C Γ Δ) (L b frame : Nat)
    (caller : State C Γ) (base : Nat → Fin W) (machine : MachineV2)
    (start : Nat) (out : Solidity.Out C caller.H Δ) : Prop :=
  ∃ final addresses,
    runV2 (lift plan.code) machine = .ok final 0 ∧
    StateRepr L b frame plan.frag out.st addresses final.base ∧
    final.base.stack = machine.base.stack ∧
    BaseExtends caller.H base addresses ∧
    GrowsAllocator b frame (plan.heapCost caller) caller base machine.base out.st addresses final.base ∧
    final.base.mem plan.pointerCell = .val (wmod start) ∧
    Footprint.Words plan.localLimit start machine.base final.base ∧
    final.calls = machine.calls ∧ final.returndata = machine.returndata ∧
    final.reply = machine.reply

/-- Every frozen successful frame result lifts without dropping its witnesses. -/
theorem lift_returned {C : Contract} {Γ Δ : Ctx}
    (plan : InterfaceV1.Emission C Γ Δ) (L b frame : Nat)
    (caller : State C Γ) (base : Nat → Fin W) (machine : MachineV2)
    (start : Nat) (out : Solidity.Out C caller.H Δ)
    (returned : InterfaceV1.Returned plan L b frame caller base machine.base start out) :
    NativeReturned plan L b frame caller base machine start out := by
  obtain ⟨target,addresses,run,represented,stack,extension,grows,cursor,older⟩ := returned
  exact ⟨machine.withBase target,addresses,run_lift_ok run,
    represented,stack,extension,grows,cursor,older,rfl,rfl,rfl⟩

variable {C : Contract} {Γ ps Γf : Ctx} {b : Nat} {F : Frag Γ}
    {f : Name} {args : Args C Γ ps} {body : Prog C ps Γf}

/-- The actual selected compiler supplies Returned; callers do not assume it.
The alternative is the same typed source's bare revert, never a desired reply. -/
theorem compiled_outcomes
    (selected : Composition.Program b F (.cons (.call f args .none body) .nil))
    (lo pointer : Nat) (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag .refl)
    (e : P1LangV2.Input C Γ) (caller : MachineV2) (a v o : Fin W) (input : List UInt8)
    (entry : InterfaceV1.Entry (NoneProducer.plan selected lo pointer)
      e.L b e.frame F e.caller e.base (prepare caller e.machine a v o input).base e.start) :
    (∃ out : Solidity.Out C e.caller.H Γ,
      (Stmt.call f args .none body).run e.caller = .ok out ∧
      NativeReturned (NoneProducer.plan selected lo pointer) e.L b e.frame
        e.caller e.base (prepare caller e.machine a v o input) e.start out) ∨
    ((Stmt.call f args .none body).run e.caller = .error .revert ∧
      runV2 (lift (NoneProducer.plan selected lo pointer).code)
        (prepare caller e.machine a v o input) = .revert e.machine.calls []) := by
  let actual := CheckedExecutionCall.preparedInput e caller a v o input
  rcases P1V2CallAgreement.source_outcomes selected lo pointer actual entry with ⟨out,source⟩ | source
  · exact .inl ⟨out,source,lift_returned _ _ _ _ _ _ _ _ _
      (NoneProducer.returns selected lo pointer flags e.L e.frame e.caller e.base
        (prepare caller e.machine a v o input).base e.start entry out source)⟩
  · exact .inr ⟨source,P1V2FramedRevert.run_revert selected lo pointer actual entry source⟩

/-- The successful compiler-selected fixture really inhabits the full relation. -/
theorem selected_success (journal : List CallRec) (buffer : List UInt8) :
    let e := P1V2FramedRevertControls.input journal buffer
    ∃ out,
      NativeReturned (NoneProducer.plan P1V2CallAgreementControls.selected 8 8)
        e.L 0 e.frame e.caller e.base
        (prepare (CheckedExecutionCall.outer e) e.machine e.machine.base.self
          e.machine.base.callvalue CheckedExecutionCall.cell []) e.start out := by
  let e := P1V2FramedRevertControls.input journal buffer
  have entry := V3BareRevertProducer.coverage P1V2CallAgreementControls.selected 8 8
    1 16 V3BareRevertProducer.Checks.caller V3BareRevertProducer.Checks.P.base
    V3BareRevertProducer.Checks.machine 10 P1V2CallAgreementControls.physical
  have actual := compiled_outcomes P1V2CallAgreementControls.selected 8 8
    (NoneProducer.init_flags _ .refl) e (CheckedExecutionCall.outer e)
    e.machine.base.self e.machine.base.callvalue CheckedExecutionCall.cell []
    (CheckedExecutionCall.prepared_entry _ e entry)
  rcases actual with ⟨out,source,framed⟩ | ⟨source,_⟩
  · exact ⟨out,framed⟩
  · change Except.ok _ = Except.error _ at source
    cases source

end Solidity.H62.ReadonlyCalls.NativeFrameTransport
