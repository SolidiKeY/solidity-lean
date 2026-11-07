import Solidity.Backend.InternalFlow.RuntimeFrameP1V2FramedRevert

/-! Guard against certifying only successful captured calls by filtering the
approved domain. Every physically entered checked singleton has an actual
success or bare revert; the existing void-call return proof then yields exact
canonical V2 agreement in both cases. No new language/admission is defined.
This supported checked family does not establish general P1/profile adequacy. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.P1V2CallAgreement
open Evm Evm.Memory

/-- Actual compiler soundness classifies the source on the same physical input;
no desired source outcome, target execution or no-failure premise is assumed. -/
theorem source_outcomes {C : Contract} {Γ Δ : Ctx} {b : Nat} {F : Frag Γ}
    {statement : Stmt C Γ Δ}
    (selected : Composition.Program b F (.cons statement .nil)) (lo pointer : Nat)
    (e : P1LangV2.Input C Γ)
    (entry : InterfaceV1.Entry (V3BareRevertProducer.plan selected lo pointer)
      e.L b e.frame F e.caller e.base e.machine.base e.start) :
    (∃ out : Solidity.Out C e.caller.H Δ, statement.run e.caller = .ok out) ∨
      statement.run e.caller = .error .revert := by
  have room : b + selected.checked.need ≤ e.frame :=
    Nat.le_trans entry.workspace (Nat.le_trans entry.pointerAbove (Nat.le_of_lt entry.pointerBelow))
  have classified := selected.checked.sound entry.represented room entry.capacity
  cases actual : statement.run e.caller with
  | ok out => exact .inl ⟨out,rfl⟩
  | error halt =>
    have failed := CallAgreement.singleton_failure actual
    rcases classified with ⟨out,target,addresses,successful,rest⟩ | ⟨bare,code⟩
    · rw [failed] at successful
      cases successful
    · have same : halt = .revert := Except.error.inj (failed.symm.trans bare)
      exact .inr (by rw [← same])

/-- Both actual source classes agree with the canonical V2 target. Physical
return representation, stack, allocator, cursor and older-word obligations are
proved by NoneProducer.returns, rather than passed as a target-run premise. -/
theorem agree {C : Contract} {Γ ps Γf : Ctx} {b : Nat} {F : Frag Γ}
    {f : Name} {args : Args C Γ ps} {body : Prog C ps Γf}
    (selected : Composition.Program b F (.cons (.call f args .none body) .nil))
    (lo pointer : Nat)
    (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag .refl)
    (e : P1LangV2.Input C Γ)
    (entry : InterfaceV1.Entry (NoneProducer.plan selected lo pointer)
      e.L b e.frame F e.caller e.base e.machine.base e.start) :
    P1LangV2.targetSem (lift (NoneProducer.plan selected lo pointer).code) e =
      P1LangV2.sourcePrefix ((Stmt.call f args .none body).run e.caller) := by
  rcases source_outcomes selected lo pointer e entry with ⟨out,source⟩ | source
  · obtain ⟨target,addresses,executed,represented,stack,extended,growth,cursor,older⟩ :=
      NoneProducer.returns selected lo pointer flags e.L e.frame e.caller e.base
        e.machine.base e.start entry out source
    simp only [P1LangV2.targetSem, run_lift_ok executed, P1LangV2.targetPrefix,
      MachineV2.withBase, P1LangV2.eventsAfter_existing, source, P1LangV2.sourcePrefix]
  · exact P1V2FramedRevert.prefix_revert selected lo pointer e entry source

end Solidity.Backend.InternalFlow.RuntimeFrame.P1V2CallAgreement
