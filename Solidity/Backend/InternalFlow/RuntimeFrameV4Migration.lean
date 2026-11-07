import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV4
import Solidity.Backend.InternalFlow.RuntimeFrameV3GeneralBoundary

/-! Migration between the frozen V3 interface and its success-only companion
V4, and the boundary of V4.

- `ofV3`: every V3 producer is a V4 producer with the same plan (forget the
  reverting witness). V3 consumers keep working; a consumer that needs only
  successful-return transport can ask for V4 instead.
- `toV3`: a V4 producer plus an admitted reverting entry for its plan is a V3
  producer; nothing else is missing.
- `of_unrolled`: the recursive `callRec` reduction of `V3GeneralBoundary`
  for V4 (definitional, no premise added).
- Boundary: V4 is still empty for a family that succeeds from no caller
  (`no_success_producer`), e.g. the always-exhausting family
  (`exhaustingStep`), because it keeps the success witness on purpose; and it
  is empty for an incoherent family (`no_incoherent_producer`; no concrete
  incoherent instance is given here). So V4 closes the never-bare-revert gap of
  V3, not every recursive family. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.V4Migration
open Evm Evm.Memory V3GeneralBoundary

variable {C : Contract}

def call_ofV3 {Γ Δ ps rs Γf : Ctx} {b : Nat} {F : Frag Γ}
    {approved admitted : InterfaceV3.Admission C Γ} {f : Name} {args : Args C Γ ps}
    {ret : CallRet Γ rs Δ} {body : Prog C (rs ++ ps) Γf}
    (p : InterfaceV3.PendingCallProducer b F approved admitted f args ret body) :
    InterfaceV4.PendingCallProducer b F approved admitted f args ret body :=
  ⟨p.plan, p.required_profile, p.required_coverage, p.required_successful_entry,
    p.required_return, p.required_bare_revert⟩

def fixed_ofV3 {Γ Δ ps rs : Ctx} {b : Nat} {F : Frag Γ}
    {approved admitted : InterfaceV3.Admission C Γ} {f : Name} {args : Args C Γ ps}
    {ret : CallRet Γ rs Δ} {body : Unit → Prog C (rs ++ ps) (rs ++ ps)}
    (p : InterfaceV3.PendingFixedCallRecProducer b F approved admitted f args ret body) :
    InterfaceV4.PendingFixedCallRecProducer b F approved admitted f args ret body :=
  ⟨p.plan, p.required_profile, p.required_coverage, p.required_successful_entry,
    p.required_return, p.required_bare_revert⟩

def recursive_ofV3 {Γ Δ ps rs : Ctx} {b : Nat} {F : Frag Γ}
    {approved admitted : Nat → InterfaceV3.Admission C Γ} {f : Name} {args : Args C Γ ps}
    {ret : CallRet Γ rs Δ}
    {step : Nat → (Unit → Prog C (rs ++ ps) (rs ++ ps)) → Prog C (rs ++ ps) (rs ++ ps)}
    (p : InterfaceV3.PendingRecursiveReturns b F approved admitted f args ret step) :
    InterfaceV4.PendingRecursiveReturns b F approved admitted f args ret step :=
  ⟨p.plan, p.required_profile, p.required_coverage, p.required_successful_entry,
    p.required_source_coherence, p.required_return, p.required_bare_revert⟩

def call_toV3 {Γ Δ ps rs Γf : Ctx} {b : Nat} {F : Frag Γ}
    {approved admitted : InterfaceV3.Admission C Γ} {f : Name} {args : Args C Γ ps}
    {ret : CallRet Γ rs Δ} {body : Prog C (rs ++ ps) Γf}
    (p : InterfaceV4.PendingCallProducer b F approved admitted f args ret body)
    (reverting : InterfaceV3.RevertingEntry b F admitted (.call f args ret body) p.plan) :
    InterfaceV3.PendingCallProducer b F approved admitted f args ret body :=
  ⟨p.plan, p.required_profile, p.required_coverage, p.required_successful_entry,
    reverting, p.required_return, p.required_bare_revert⟩

def fixed_toV3 {Γ Δ ps rs : Ctx} {b : Nat} {F : Frag Γ}
    {approved admitted : InterfaceV3.Admission C Γ} {f : Name} {args : Args C Γ ps}
    {ret : CallRet Γ rs Δ} {body : Unit → Prog C (rs ++ ps) (rs ++ ps)}
    (p : InterfaceV4.PendingFixedCallRecProducer b F approved admitted f args ret body)
    (reverting : ∀ d, InterfaceV3.RevertingEntry b F admitted (.callRec f d args ret body) p.plan) :
    InterfaceV3.PendingFixedCallRecProducer b F approved admitted f args ret body :=
  ⟨p.plan, p.required_profile, p.required_coverage, p.required_successful_entry,
    reverting, p.required_return, p.required_bare_revert⟩

def recursive_toV3 {Γ Δ ps rs : Ctx} {b : Nat} {F : Frag Γ}
    {approved admitted : Nat → InterfaceV3.Admission C Γ} {f : Name} {args : Args C Γ ps}
    {ret : CallRet Γ rs Δ}
    {step : Nat → (Unit → Prog C (rs ++ ps) (rs ++ ps)) → Prog C (rs ++ ps) (rs ++ ps)}
    (p : InterfaceV4.PendingRecursiveReturns b F approved admitted f args ret step)
    (reverting : ∃ n, InterfaceV3.RevertingEntry b F (admitted n)
      (InterfaceV1.recursiveSource f args ret step n) (p.plan.at n)) :
    InterfaceV3.PendingRecursiveReturns b F approved admitted f args ret step :=
  ⟨p.plan, p.required_profile, p.required_coverage, p.required_successful_entry,
    reverting, p.required_source_coherence, p.required_return, p.required_bare_revert⟩

/-- `toV3 ∘ ofV3` is the identity, given the V3 producer's own reverting entry. -/
theorem recursive_round_trip {Γ Δ ps rs : Ctx} {b : Nat} {F : Frag Γ}
    {approved admitted : Nat → InterfaceV3.Admission C Γ} {f : Name} {args : Args C Γ ps}
    {ret : CallRet Γ rs Δ}
    {step : Nat → (Unit → Prog C (rs ++ ps) (rs ++ ps)) → Prog C (rs ++ ps) (rs ++ ps)}
    (p : InterfaceV3.PendingRecursiveReturns b F approved admitted f args ret step) :
    recursive_toV3 (recursive_ofV3 p) p.required_reverting_entry = p := rfl

/-- `ofV3 ∘ toV3` is the identity. -/
theorem recursive_round_trip' {Γ Δ ps rs : Ctx} {b : Nat} {F : Frag Γ}
    {approved admitted : Nat → InterfaceV3.Admission C Γ} {f : Name} {args : Args C Γ ps}
    {ret : CallRet Γ rs Δ}
    {step : Nat → (Unit → Prog C (rs ++ ps) (rs ++ ps)) → Prog C (rs ++ ps) (rs ++ ps)}
    (q : InterfaceV4.PendingRecursiveReturns b F approved admitted f args ret step)
    (r : ∃ n, InterfaceV3.RevertingEntry b F (admitted n)
      (InterfaceV1.recursiveSource f args ret step n) (q.plan.at n)) :
    recursive_ofV3 (recursive_toV3 q r) = q := rfl

/-- Recursive `callRec` reduction for V4 (definitional, as in V3). -/
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
    (returns : ∀ n, InterfaceV1.ReturnClaim b F
      (.call f args ret (recUnroll Prog.recBase step n)) (plan.at n))
    (reverts : ∀ n, InterfaceV1.BareRevertClaim b F
      (.call f args ret (recUnroll Prog.recBase step n)) (plan.at n)) :
    InterfaceV4.PendingRecursiveReturns b F approved admitted f args ret step where
  plan := plan
  required_profile := hprof
  required_coverage := coverage
  required_successful_entry := by
    obtain ⟨n, h⟩ := success
    exact ⟨n, successful_of_call f n args ret (fun _ => recUnroll Prog.recBase step n) _ _ h⟩
  required_source_coherence := coherence
  required_return n :=
    return_of_call f n args ret (fun _ => recUnroll Prog.recBase step n) _ (returns n)
  required_bare_revert n :=
    bare_revert_of_call f n args ret (fun _ => recUnroll Prog.recBase step n) _ (reverts n)

/-! ## Boundary of V4 -/

/-- A recursive family that succeeds from no caller at any index. -/
def NeverSucceeds {Γ Δ ps rs : Ctx} (f : Name) (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
    (step : Nat → (Unit → Prog C (rs ++ ps) (rs ++ ps)) → Prog C (rs ++ ps) (rs ++ ps)) : Prop :=
  ∀ n (σ : State C Γ) out, (InterfaceV1.recursiveSource f args ret step n).run σ ≠ .ok out

theorem no_success_producer {Γ Δ ps rs : Ctx} {b : Nat} {F : Frag Γ}
    {approved admitted : Nat → InterfaceV3.Admission C Γ} {f : Name} {args : Args C Γ ps}
    {ret : CallRet Γ rs Δ}
    {step : Nat → (Unit → Prog C (rs ++ ps) (rs ++ ps)) → Prog C (rs ++ ps) (rs ++ ps)}
    (never : NeverSucceeds f args ret step) :
    ¬ Nonempty (InterfaceV4.PendingRecursiveReturns b F approved admitted f args ret step) :=
  fun ⟨p⟩ => by
    obtain ⟨n, _, _, caller, _, _, _, out, _, _, run⟩ := p.required_successful_entry
    exact never n caller out run

/-- V4 retains source coherence. -/
theorem coherence {Γ Δ ps rs : Ctx} {b : Nat} {F : Frag Γ}
    {approved admitted : Nat → InterfaceV3.Admission C Γ} {f : Name} {args : Args C Γ ps}
    {ret : CallRet Γ rs Δ}
    {step : Nat → (Unit → Prog C (rs ++ ps) (rs ++ ps)) → Prog C (rs ++ ps) (rs ++ ps)}
    (p : InterfaceV4.PendingRecursiveReturns b F approved admitted f args ret step) :
    InterfaceV1.RecursiveReturnCoherence f args ret step :=
  p.required_source_coherence

theorem no_incoherent_producer {Γ Δ ps rs : Ctx} {b : Nat} {F : Frag Γ}
    {approved admitted : Nat → InterfaceV3.Admission C Γ} {f : Name} {args : Args C Γ ps}
    {ret : CallRet Γ rs Δ}
    {step : Nat → (Unit → Prog C (rs ++ ps) (rs ++ ps)) → Prog C (rs ++ ps) (rs ++ ps)}
    (incoherent : ¬ InterfaceV1.RecursiveReturnCoherence f args ret step) :
    ¬ Nonempty (InterfaceV4.PendingRecursiveReturns b F approved admitted f args ret step) :=
  fun ⟨p⟩ => incoherent p.required_source_coherence

/-- Every activation calls the next one: every unrolling is the base. -/
def exhaustingStep (_ : Nat) (k : Unit → Prog C [] []) : Prog C [] [] := k ()

theorem exhausting_unroll (n : Nat) :
    recUnroll (Prog.recBase (C := C) (Γ := [])) exhaustingStep n = Prog.recBase := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem exhausting_never_succeeds {Γ : Ctx} (f : Name) :
    NeverSucceeds (C := C) (Γ := Γ) f .nil .none exhaustingStep := by
  intro n σ out h
  change (Stmt.callRec f n .nil .none
    (fun _ => recUnroll Prog.recBase exhaustingStep n)).run σ = .ok out at h
  rw [exhausting_unroll n] at h
  exact nomatch h

/-- The always-exhausting family has no V4 producer, at any domain. -/
theorem exhausting_empty {Γ : Ctx} (b : Nat) (F : Frag Γ)
    (approved admitted : Nat → InterfaceV3.Admission C Γ) (f : Name) :
    ¬ Nonempty (InterfaceV4.PendingRecursiveReturns b F approved admitted f .nil .none
      exhaustingStep) :=
  no_success_producer (exhausting_never_succeeds f)

end Solidity.Backend.InternalFlow.RuntimeFrame.V4Migration

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.V4Migration.recursive_ofV3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V4Migration.recursive_ofV3
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.V4Migration.recursive_toV3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V4Migration.recursive_toV3
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.V4Migration.of_unrolled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V4Migration.of_unrolled
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.V4Migration.exhausting_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V4Migration.exhausting_empty
