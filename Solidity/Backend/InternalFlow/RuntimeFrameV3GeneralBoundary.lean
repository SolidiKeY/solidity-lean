import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV3

/-! Boundary of a *general* P1 closure over the frozen V3 interface.

`no_call_producer`, `no_fixed_producer` and `no_recursive_producer` restate
formally the limitation the V3 interface already documents ("a success-only
source cannot inhabit this dual-outcome evidence class"): each dual-outcome V3
structure is empty for a source that never bare-reverts, whatever the plan,
domain or approved profile. They follow in one step from the
`required_reverting_entry` field. `trivial_never_reverts` gives a
uniform, index-independent recursive family (empty body, no arguments, void
return) with that property, so the unrestricted statement "every recursive
family has a V3 producer" is false (`no_unrestricted_closure`); the
meaningful instance is a nonempty domain such as the full one, since an empty
domain refutes it trivially. A general P1
closure must therefore be stated over a source class or with a success-only
companion interface; choosing either is a frozen-interface (H57) decision.

`of_unrolled` and `unrolled_returns` are a definitional repackaging, not a
new closure result: since `callRec` runs as the ordinary call of its body by
definition (`Stmt.run_callRec`), the V3 recursive structure is exactly the
ordinary-call obligations of each unrolled body with one code image. They
reduce a general recursive closure to per-body ordinary-call claims and add
no premise. The interfaces themselves are unchanged. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.V3GeneralBoundary
open Evm Evm.Memory

variable {C : Contract}

/-- `callRec` runs exactly as the ordinary call of its body; the quotation
index is not consulted. This is the existing `Stmt.run_callRec`. -/
theorem callRec_run {Γ Δ ps rs : Ctx} (f : Name) (d : Nat) (args : Args C Γ ps)
    (ret : CallRet Γ rs Δ) (body : Unit → Prog C (rs ++ ps) (rs ++ ps)) (σ : State C Γ) :
    (Stmt.callRec f d args ret body).run σ = (Stmt.call f args ret (body ())).run σ :=
  Stmt.run_callRec σ f d args ret body

/-- Transport of the frozen return claim along `callRec_run`. -/
theorem return_of_call {Γ Δ ps rs : Ctx} {b : Nat} {F : Frag Γ} (f : Name) (d : Nat)
    (args : Args C Γ ps) (ret : CallRet Γ rs Δ) (body : Unit → Prog C (rs ++ ps) (rs ++ ps))
    (plan : InterfaceV1.Emission C Γ Δ)
    (h : InterfaceV1.ReturnClaim b F (.call f args ret (body ())) plan) :
    InterfaceV1.ReturnClaim b F (.callRec f d args ret body) plan :=
  fun L frame caller base machine start entry out run =>
    h L frame caller base machine start entry out ((callRec_run f d args ret body caller).symm.trans run)

/-- Transport of the frozen bare-revert claim along `callRec_run`. -/
theorem bare_revert_of_call {Γ Δ ps rs : Ctx} {b : Nat} {F : Frag Γ} (f : Name) (d : Nat)
    (args : Args C Γ ps) (ret : CallRet Γ rs Δ) (body : Unit → Prog C (rs ++ ps) (rs ++ ps))
    (plan : InterfaceV1.Emission C Γ Δ)
    (h : InterfaceV1.BareRevertClaim b F (.call f args ret (body ())) plan) :
    InterfaceV1.BareRevertClaim b F (.callRec f d args ret body) plan :=
  fun L frame caller base machine start entry run =>
    h L frame caller base machine start entry ((callRec_run f d args ret body caller).symm.trans run)

/-- Witness transport: successful entries of the ordinary call are
successful entries of the `callRec` at any index, for the same plan. -/
theorem successful_of_call {Γ Δ ps rs : Ctx} {b : Nat} {F : Frag Γ} (f : Name) (d : Nat)
    (args : Args C Γ ps) (ret : CallRet Γ rs Δ) (body : Unit → Prog C (rs ++ ps) (rs ++ ps))
    (admitted : InterfaceV3.Admission C Γ) (plan : InterfaceV1.Emission C Γ Δ)
    (h : InterfaceV3.SuccessfulEntry b F admitted (.call f args ret (body ())) plan) :
    InterfaceV3.SuccessfulEntry b F admitted (.callRec f d args ret body) plan := by
  obtain ⟨L, frame, caller, base, machine, start, out, adm, entry, run⟩ := h
  exact ⟨L, frame, caller, base, machine, start, out, adm, entry,
    (callRec_run f d args ret body caller).trans run⟩

/-- Witness transport for reverting entries, as `successful_of_call`. -/
theorem reverting_of_call {Γ Δ ps rs : Ctx} {b : Nat} {F : Frag Γ} (f : Name) (d : Nat)
    (args : Args C Γ ps) (ret : CallRet Γ rs Δ) (body : Unit → Prog C (rs ++ ps) (rs ++ ps))
    (admitted : InterfaceV3.Admission C Γ) (plan : InterfaceV1.Emission C Γ Δ)
    (h : InterfaceV3.RevertingEntry b F admitted (.call f args ret (body ())) plan) :
    InterfaceV3.RevertingEntry b F admitted (.callRec f d args ret body) plan := by
  obtain ⟨L, frame, caller, base, machine, start, adm, entry, run⟩ := h
  exact ⟨L, frame, caller, base, machine, start, adm, entry,
    (callRec_run f d args ret body caller).trans run⟩

/-- Generic recursive `callRec` transport into the frozen V3 recursive
structure. Every obligation is the ordinary-call obligation of the actual
unrolled body at the same index, plan and domain; nothing is added. -/
def of_unrolled {Γ Δ ps rs : Ctx} {b : Nat} {F : Frag Γ}
    {f : Name} {args : Args C Γ ps} {ret : CallRet Γ rs Δ}
    {step : Nat → (Unit → Prog C (rs ++ ps) (rs ++ ps)) → Prog C (rs ++ ps) (rs ++ ps)}
    (approved admitted : Nat → InterfaceV3.Admission C Γ)
    (plan : InterfaceV1.RecursiveEmission C Γ Δ)
    (hprof : InterfaceV3.FamilyAdmissionAgreement approved admitted)
    (coverage : InterfaceV3.FamilyEntryCoverage b F admitted plan)
    (coherence : InterfaceV1.RecursiveReturnCoherence f args ret step)
    (success : ∃ n, InterfaceV3.SuccessfulEntry b F (admitted n)
      (.call f args ret (recUnroll Prog.recBase step n)) (plan.at n))
    (revert : ∃ n, InterfaceV3.RevertingEntry b F (admitted n)
      (.call f args ret (recUnroll Prog.recBase step n)) (plan.at n))
    (returns : ∀ n, InterfaceV1.ReturnClaim b F
      (.call f args ret (recUnroll Prog.recBase step n)) (plan.at n))
    (reverts : ∀ n, InterfaceV1.BareRevertClaim b F
      (.call f args ret (recUnroll Prog.recBase step n)) (plan.at n)) :
    InterfaceV3.PendingRecursiveReturns b F approved admitted f args ret step where
  plan := plan
  required_profile := hprof
  required_coverage := coverage
  required_successful_entry := by
    obtain ⟨n, h⟩ := success
    exact ⟨n, successful_of_call f n args ret (fun _ => recUnroll Prog.recBase step n) _ _ h⟩
  required_reverting_entry := by
    obtain ⟨n, h⟩ := revert
    exact ⟨n, reverting_of_call f n args ret (fun _ => recUnroll Prog.recBase step n) _ _ h⟩
  required_source_coherence := coherence
  required_return n :=
    return_of_call f n args ret (fun _ => recUnroll Prog.recBase step n) _ (returns n)
  required_bare_revert n :=
    bare_revert_of_call f n args ret (fun _ => recUnroll Prog.recBase step n) _ (reverts n)

/-- Converse of `of_unrolled`: every V3 recursive producer yields exactly the
ordinary-call claims `of_unrolled` consumes, at the same plan and indices, so
its hypotheses are no stronger than the frozen structure. -/
theorem unrolled_returns {Γ Δ ps rs : Ctx} {b : Nat} {F : Frag Γ}
    {f : Name} {args : Args C Γ ps} {ret : CallRet Γ rs Δ}
    {step : Nat → (Unit → Prog C (rs ++ ps) (rs ++ ps)) → Prog C (rs ++ ps) (rs ++ ps)}
    {approved admitted : Nat → InterfaceV3.Admission C Γ}
    (p : InterfaceV3.PendingRecursiveReturns b F approved admitted f args ret step) :
    (∀ n, InterfaceV1.ReturnClaim b F
      (.call f args ret (recUnroll Prog.recBase step n)) (p.plan.at n)) ∧
    (∀ n, InterfaceV1.BareRevertClaim b F
      (.call f args ret (recUnroll Prog.recBase step n)) (p.plan.at n)) ∧
    (∃ n, InterfaceV3.SuccessfulEntry b F (admitted n)
      (.call f args ret (recUnroll Prog.recBase step n)) (p.plan.at n)) ∧
    (∃ n, InterfaceV3.RevertingEntry b F (admitted n)
      (.call f args ret (recUnroll Prog.recBase step n)) (p.plan.at n)) := by
  refine ⟨fun n L frame caller base machine start entry out run => ?_,
    fun n L frame caller base machine start entry run => ?_, ?_, ?_⟩
  · exact p.required_return n L frame caller base machine start entry out
      ((callRec_run f n args ret _ caller).trans run)
  · exact p.required_bare_revert n L frame caller base machine start entry
      ((callRec_run f n args ret _ caller).trans run)
  · obtain ⟨n, L, frame, caller, base, machine, start, out, adm, entry, run⟩ :=
      p.required_successful_entry
    exact ⟨n, L, frame, caller, base, machine, start, out, adm, entry,
      (callRec_run f n args ret _ caller).symm.trans run⟩
  · obtain ⟨n, L, frame, caller, base, machine, start, adm, entry, run⟩ :=
      p.required_reverting_entry
    exact ⟨n, L, frame, caller, base, machine, start, adm, entry,
      (callRec_run f n args ret _ caller).symm.trans run⟩

/-! ## Emptiness for sources without a bare revert -/

/-- A statement that never bare-reverts from any typed caller. -/
def NeverReverts {Γ Δ : Ctx} (s : Stmt C Γ Δ) : Prop :=
  ∀ σ : State C Γ, s.run σ ≠ .error .revert

theorem no_reverting_entry {Γ Δ : Ctx} {b : Nat} {F : Frag Γ}
    {admitted : InterfaceV3.Admission C Γ} {s : Stmt C Γ Δ}
    {plan : InterfaceV1.Emission C Γ Δ} (never : NeverReverts s) :
    ¬ InterfaceV3.RevertingEntry b F admitted s plan := by
  intro h
  obtain ⟨_, _, caller, _, _, _, _, _, run⟩ := h
  exact never caller run

theorem no_call_producer {Γ Δ ps rs Γf : Ctx} {b : Nat} {F : Frag Γ}
    {approved admitted : InterfaceV3.Admission C Γ} {f : Name} {args : Args C Γ ps}
    {ret : CallRet Γ rs Δ} {body : Prog C (rs ++ ps) Γf}
    (never : NeverReverts (.call f args ret body)) :
    ¬ Nonempty (InterfaceV3.PendingCallProducer b F approved admitted f args ret body) :=
  fun ⟨p⟩ => no_reverting_entry never p.required_reverting_entry

theorem no_fixed_producer {Γ Δ ps rs : Ctx} {b : Nat} {F : Frag Γ}
    {approved admitted : InterfaceV3.Admission C Γ} {f : Name} {args : Args C Γ ps}
    {ret : CallRet Γ rs Δ} {body : Unit → Prog C (rs ++ ps) (rs ++ ps)}
    (d : Nat) (never : NeverReverts (.callRec f d args ret body)) :
    ¬ Nonempty (InterfaceV3.PendingFixedCallRecProducer b F approved admitted f args ret body) :=
  fun ⟨p⟩ => no_reverting_entry never (p.required_reverting_entry d)

theorem no_recursive_producer {Γ Δ ps rs : Ctx} {b : Nat} {F : Frag Γ}
    {approved admitted : Nat → InterfaceV3.Admission C Γ} {f : Name} {args : Args C Γ ps}
    {ret : CallRet Γ rs Δ}
    {step : Nat → (Unit → Prog C (rs ++ ps) (rs ++ ps)) → Prog C (rs ++ ps) (rs ++ ps)}
    (never : ∀ n, NeverReverts (InterfaceV1.recursiveSource f args ret step n)) :
    ¬ Nonempty (InterfaceV3.PendingRecursiveReturns b F approved admitted f args ret step) :=
  fun ⟨p⟩ => by
    obtain ⟨n, h⟩ := p.required_reverting_entry
    exact no_reverting_entry (never n) h

/-! ## A uniform family with no V3 producer -/

/-- Index-independent step with an empty body: no arguments, void return. -/
def trivialStep (_ : Nat) (_ : Unit → Prog C [] []) : Prog C [] [] := .nil

theorem trivial_never_reverts {Γ : Ctx} (f : Name) (n : Nat) :
    NeverReverts (InterfaceV1.recursiveSource (C := C) (Γ := Γ) f .nil .none trivialStep n) := by
  intro σ h
  cases n with
  | zero => exact nomatch h
  | succ n => exact nomatch h

/-- The unrestricted closure (a V3 recursive producer for every family, at
any fixed domain) is false: it already fails for the trivial uniform family,
for every contract, frame index, fragment and domain. For an empty domain this
is trivial; the full domain is the meaningful case (see the controls). -/
theorem no_unrestricted_closure (C : Contract) (b : Nat) (F : Frag ([] : Ctx))
    (approved admitted : Nat → InterfaceV3.Admission C []) (f : Name) :
    ¬ ∀ step : Nat → (Unit → Prog C [] []) → Prog C [] [],
      Nonempty (InterfaceV3.PendingRecursiveReturns b F approved admitted f .nil .none step) :=
  fun all => no_recursive_producer (trivial_never_reverts f) (all trivialStep)

end Solidity.Backend.InternalFlow.RuntimeFrame.V3GeneralBoundary

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.V3GeneralBoundary.no_unrestricted_closure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3GeneralBoundary.no_unrestricted_closure

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.V3GeneralBoundary.of_unrolled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3GeneralBoundary.of_unrolled

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.V3GeneralBoundary.unrolled_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3GeneralBoundary.unrolled_returns
