import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV1

/-! Frozen P1 runtime-frame interface, version 2. The existing v1 execution,
representation and capacity relations are unchanged. These explicit pending
producer requirements tie an admitted entry to an actual source outcome.
They are minimum non-vacuity requirements, not profile-coverage theorems,
physical feasibility at all indices, or an unbounded recursive simulation. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.InterfaceV2
open Evm Evm.Memory

/-- The SAME caller has both a genuine represented entry and a successful
source execution. A failing or exhausted caller alone cannot witness this. -/
def SuccessfulEntry {C : Contract} {Γ Δ : Ctx} (b : Nat) (F : Frag Γ)
 (statement : Stmt C Γ Δ) (plan : InterfaceV1.Emission C Γ Δ) : Prop :=
 ∃ (L frame : Nat) (caller : State C Γ) (base : Nat → Fin W)
   (machine : Machine) (start : Nat) (out : Solidity.Out C caller.H Δ),
 InterfaceV1.Entry plan L b frame F caller base machine start ∧
 statement.run caller = .ok out

/-- A failure-specialized witness; this does not say that the source can
ONLY fail. Other halt classes are not identified with bare revert. -/
def RevertingEntry {C : Contract} {Γ Δ : Ctx} (b : Nat) (F : Frag Γ)
 (statement : Stmt C Γ Δ) (plan : InterfaceV1.Emission C Γ Δ) : Prop :=
 ∃ (L frame : Nat) (caller : State C Γ) (base : Nat → Fin W)
   (machine : Machine) (start : Nat),
 InterfaceV1.Entry plan L b frame F caller base machine start ∧
 statement.run caller = .error .revert

/-- Unproved ordinary-call producer duties with actual successful-entry
non-vacuity. Admission of all other callers remains a separate coverage duty. -/
structure PendingCallProducer {C : Contract} {Γ Δ ps rs Γf : Ctx}
 (b : Nat) (F : Frag Γ)
 (f : Name) (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
 (body : Prog C (rs ++ ps) Γf) where
 plan : InterfaceV1.Emission C Γ Δ
 required_successful_entry : SuccessfulEntry b F (.call f args ret body) plan
 required_return : InterfaceV1.ReturnClaim b F (.call f args ret body) plan
 required_bare_revert : InterfaceV1.BareRevertClaim b F (.call f args ret body) plan

/-- A fixed actual thunk at each quotation index. These requirements do not
establish unbounded recursion or physical feasibility of growing call stacks. -/
structure PendingFixedCallRecProducer {C : Contract} {Γ Δ ps rs : Ctx}
 (b : Nat) (F : Frag Γ)
 (f : Name) (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
 (body : Unit → Prog C (rs ++ ps) (rs ++ ps)) where
 plan : InterfaceV1.Emission C Γ Δ
 required_successful_entry : ∀ d, SuccessfulEntry b F (.callRec f d args ret body) plan
 required_return : ∀ d, InterfaceV1.ReturnClaim b F (.callRec f d args ret body) plan
 required_bare_revert : ∀ d, InterfaceV1.BareRevertClaim b F (.callRec f d args ret body) plan

/-- One code image, the actual intrinsic unrolling family, and at least one
successful represented family member. Index-zero exhaustion alone cannot
inhabit the witness. No claim is made that every index or caller has enough
physical room; successful-entry existence at one index is NOT such coverage. -/
structure PendingRecursiveReturns {C : Contract} {Γ Δ ps rs : Ctx}
 (b : Nat) (F : Frag Γ)
 (f : Name) (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
 (step : Nat → (Unit → Prog C (rs ++ ps) (rs ++ ps)) → Prog C (rs ++ ps) (rs ++ ps)) where
 plan : InterfaceV1.RecursiveEmission C Γ Δ
 required_successful_entry : ∃ n, SuccessfulEntry b F
   (InterfaceV1.recursiveSource f args ret step n) (plan.at n)
 required_source_coherence : InterfaceV1.RecursiveReturnCoherence f args ret step
 required_return : ∀ n, InterfaceV1.ReturnClaim b F
   (InterfaceV1.recursiveSource f args ret step n) (plan.at n)
 required_bare_revert : ∀ n, InterfaceV1.BareRevertClaim b F
   (InterfaceV1.recursiveSource f args ret step n) (plan.at n)

/-- Failure-specialized producer duties, with a genuine matching bare-revert
entry. Successful transport is not asserted by this structure. -/
structure PendingBareRevertProducer {C : Contract} {Γ Δ : Ctx}
 (b : Nat) (F : Frag Γ) (statement : Stmt C Γ Δ) where
 plan : InterfaceV1.Emission C Γ Δ
 required_reverting_entry : RevertingEntry b F statement plan
 required_bare_revert : InterfaceV1.BareRevertClaim b F statement plan

end Solidity.Backend.InternalFlow.RuntimeFrame.InterfaceV2
