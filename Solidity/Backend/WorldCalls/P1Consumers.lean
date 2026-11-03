import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV3

/-! Consumers of exact frozen P1 V3 Pending producer requirements.
V1 representation/execution/restoration relations remain unchanged. No producer
instance is constructed. Approved/admitted domains and V3 coverage remain
explicit producer requirements; profile provenance is not inferred from equality.
Ordinary/fixed producers require both outcome witnesses; recursive witnesses
may use different indices. No all-caller/profile feasibility follows. -/
namespace Solidity.Backend.WorldCalls.P1Consumers
open Evm Evm.Memory
open InternalFlow.RuntimeFrame.InterfaceV1 (Entry Returned ReturnClaim BareRevertClaim recursiveSource RecursiveReturnCoherence PendingRestoration RestoredRepresentationClaim)
open InternalFlow.RuntimeFrame.InterfaceV3 (SuccessfulEntry RevertingEntry PendingCallProducer PendingFixedCallRecProducer PendingRecursiveReturns PendingBareRevertProducer)
variable {C : Contract} {Γ Δ ps rs Γf : Ctx} {b : Nat} {F : Frag Γ}
variable {approved admitted : InternalFlow.RuntimeFrame.InterfaceV3.Admission C Γ}
variable {approvedFamily admittedFamily : Nat → InternalFlow.RuntimeFrame.InterfaceV3.Admission C Γ}
variable {f : Name} {args : Args C Γ ps} {ret : CallRet Γ rs Δ}

theorem ordinary_return {body : Prog C (rs ++ ps) Γf}
    (p : PendingCallProducer b F approved admitted f args ret body) :
    ReturnClaim b F (.call f args ret body) p.plan := p.required_return

theorem ordinary_bare_revert {body : Prog C (rs ++ ps) Γf}
    (p : PendingCallProducer b F approved admitted f args ret body) :
    BareRevertClaim b F (.call f args ret body) p.plan := p.required_bare_revert

theorem fixed_bare_revert {body : Unit → Prog C (rs ++ ps) (rs ++ ps)}
    (p : PendingFixedCallRecProducer b F approved admitted f args ret body) (d : Nat) :
    BareRevertClaim b F (.callRec f d args ret body) p.plan := p.required_bare_revert d

theorem fixed_return {body : Unit → Prog C (rs ++ ps) (rs ++ ps)}
    (p : PendingFixedCallRecProducer b F approved admitted f args ret body) (d : Nat) :
    ReturnClaim b F (.callRec f d args ret body) p.plan := p.required_return d

theorem recursive_bare_revert {step : Nat → (Unit → Prog C (rs ++ ps) (rs ++ ps)) → Prog C (rs ++ ps) (rs ++ ps)}
    (p : PendingRecursiveReturns b F approvedFamily admittedFamily f args ret step) (n : Nat) :
    BareRevertClaim b F (recursiveSource f args ret step n) (p.plan.at n) := p.required_bare_revert n

theorem recursive_code {step : Nat → (Unit → Prog C (rs ++ ps) (rs ++ ps)) → Prog C (rs ++ ps) (rs ++ ps)}
    (p : PendingRecursiveReturns b F approvedFamily admittedFamily f args ret step) (n : Nat) : (p.plan.at n).code = p.plan.code := rfl

theorem recursive_return {step : Nat → (Unit → Prog C (rs ++ ps) (rs ++ ps)) → Prog C (rs ++ ps) (rs ++ ps)}
    (p : PendingRecursiveReturns b F approvedFamily admittedFamily f args ret step) (n : Nat) :
    ReturnClaim b F (recursiveSource f args ret step n) (p.plan.at n) := p.required_return n

theorem recursive_coherence {step : Nat → (Unit → Prog C (rs ++ ps) (rs ++ ps)) → Prog C (rs ++ ps) (rs ++ ps)}
    (p : PendingRecursiveReturns b F approvedFamily admittedFamily f args ret step) :
    RecursiveReturnCoherence f args ret step := p.required_source_coherence

theorem restoration (p : PendingRestoration) : RestoredRepresentationClaim := p.required

theorem ordinary_successful_entry {body : Prog C (rs ++ ps) Γf}
    (p : PendingCallProducer b F approved admitted f args ret body) :
    SuccessfulEntry b F admitted (.call f args ret body) p.plan := p.required_successful_entry

theorem fixed_successful_entry {body : Unit → Prog C (rs ++ ps) (rs ++ ps)}
    (p : PendingFixedCallRecProducer b F approved admitted f args ret body) (d : Nat) :
    SuccessfulEntry b F admitted (.callRec f d args ret body) p.plan := p.required_successful_entry d

theorem recursive_successful_entry {step : Nat → (Unit → Prog C (rs ++ ps) (rs ++ ps)) → Prog C (rs ++ ps) (rs ++ ps)}
    (p : PendingRecursiveReturns b F approvedFamily admittedFamily f args ret step) :
    ∃ n, SuccessfulEntry b F (admittedFamily n) (recursiveSource f args ret step n) (p.plan.at n) := p.required_successful_entry

theorem bare_reverting_entry {statement : Stmt C Γ Δ}
    (p : PendingBareRevertProducer b F approved admitted statement) : RevertingEntry b F admitted statement p.plan := p.required_reverting_entry

theorem bare_revert_claim {statement : Stmt C Γ Δ}
    (p : PendingBareRevertProducer b F approved admitted statement) : BareRevertClaim b F statement p.plan := p.required_bare_revert

/-- Given a V3 producer, its genuine successful entry invokes its full return
requirement for THAT SAME caller. No global producer existence is asserted. -/
theorem ordinary_return_witness {body : Prog C (rs ++ ps) Γf}
    (p : PendingCallProducer b F approved admitted f args ret body) :
    ∃ (L frame : Nat) (caller : State C Γ) (base : Nat → Fin W)
      (machine : Machine) (start : Nat) (out : Solidity.Out C caller.H Δ),
      Entry p.plan L b frame F caller base machine start ∧
      (Stmt.call f args ret body).run caller = .ok out ∧
      Returned p.plan L b frame caller base machine start out := by
  obtain ⟨L,frame,caller,base,machine,start,out,admission,entry,run⟩ := p.required_successful_entry
  exact ⟨L,frame,caller,base,machine,start,out,entry,run,
    p.required_return L frame caller base machine start entry out run⟩

/-- Exhaustion cannot supply a V3 successful-entry witness. -/
theorem rejects_exhausted {statement : Stmt C Γ Δ} {plan : InternalFlow.RuntimeFrame.InterfaceV1.Emission C Γ Δ}
    (failed : ∀ caller : State C Γ, statement.run caller = .error .exhausted) :
    ¬ SuccessfulEntry b F admitted statement plan := by
  intro witness
  obtain ⟨L,frame,caller,base,machine,start,out,admission,entry,run⟩ := witness
  rw [failed caller] at run
  cases run

end Solidity.Backend.WorldCalls.P1Consumers
