import Solidity.Backend.InternalDispatch.FrozenV1
import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV2

/-! Older frozen P1 v2 consumer (FrozenV3 is the active one). V1 supplies ONLY unchanged execution relations
and version-independent typed selector/site metadata. All pending producers
below are the exact V2 types. No instance or universal admission is asserted. -/
namespace Solidity.Backend.InternalDispatch.FrozenV2
open FrozenV1
open Solidity.Backend.InternalFlow.RuntimeFrame.InterfaceV1
  (Entry Returned ReturnClaim BareRevertClaim recursiveSource RecursiveReturnCoherence)
open Solidity.Backend.InternalFlow.RuntimeFrame.InterfaceV2
  (SuccessfulEntry RevertingEntry PendingCallProducer PendingFixedCallRecProducer
   PendingRecursiveReturns PendingBareRevertProducer)
variable {E : Source.Env} {ps rs : List Source.STy} {qualifier : Option Source.Mutability}

/-- Ordinary calls use PendingCallProducer verbatim, including the exact successful-entry obligation
and ONLY bare-revert evidence. No full independent Source outcome is inferred. -/
theorem call_claims (t : Table E ps rs qualifier) {C : Contract} {Γ Δ : Ctx}
    (lowerType : Source.STy → LTy) (b : Nat) (F : Evm.Frag Γ)
    (sites : ∀ i, CallSite (t.candidate i) C Γ Δ lowerType)
    (producer : ∀ i, PendingCallProducer b F (t.candidate i).identity.name
      (sites i).args (sites i).ret (sites i).body)
    (value : Source.Val E.layout (.fn false ps rs qualifier)) (word : Fin Evm.W)
    (represented : t.Rep value word) :
    ∃ i, functionName value = some (t.candidate i).identity ∧
      select t (fun j => PendingCallProducer b F (t.candidate j).identity.name
        (sites j).args (sites j).ret (sites j).body) producer word = some ⟨i, producer i⟩ ∧
      SuccessfulEntry b F (.call (t.candidate i).identity.name
        (sites i).args (sites i).ret (sites i).body) (producer i).plan ∧
      ReturnClaim b F (.call (t.candidate i).identity.name
        (sites i).args (sites i).ret (sites i).body) (producer i).plan ∧
      BareRevertClaim b F (.call (t.candidate i).identity.name
        (sites i).args (sites i).ret (sites i).body) (producer i).plan := by
  obtain ⟨i, identity, chosen⟩ := selected t _ producer value word represented
  exact ⟨i, identity, chosen, (producer i).required_successful_entry,
    (producer i).required_return, (producer i).required_bare_revert⟩

/-- Fixed quotations keep their exact all-d obligations from the frozen type. -/
theorem fixed_claims (t : Table E ps rs qualifier) {C : Contract} {Γ Δ : Ctx}
    (lowerType : Source.STy → LTy) (b : Nat) (F : Evm.Frag Γ)
    (sites : ∀ i, FixedSite (t.candidate i) C Γ Δ lowerType)
    (producer : ∀ i, PendingFixedCallRecProducer b F (t.candidate i).identity.name
      (sites i).args (sites i).ret (sites i).body)
    (value : Source.Val E.layout (.fn false ps rs qualifier)) (word : Fin Evm.W)
    (represented : t.Rep value word) :
    ∃ i, functionName value = some (t.candidate i).identity ∧
      select t (fun j => PendingFixedCallRecProducer b F (t.candidate j).identity.name
        (sites j).args (sites j).ret (sites j).body) producer word = some ⟨i, producer i⟩ ∧
      (∀ d, SuccessfulEntry b F (.callRec (t.candidate i).identity.name d
        (sites i).args (sites i).ret (sites i).body) (producer i).plan) ∧
      (∀ d, ReturnClaim b F (.callRec (t.candidate i).identity.name d
        (sites i).args (sites i).ret (sites i).body) (producer i).plan) ∧
      (∀ d, BareRevertClaim b F (.callRec (t.candidate i).identity.name d
        (sites i).args (sites i).ret (sites i).body) (producer i).plan) := by
  obtain ⟨i, identity, chosen⟩ := selected t _ producer value word represented
  exact ⟨i, identity, chosen, (producer i).required_successful_entry,
    (producer i).required_return, (producer i).required_bare_revert⟩

/-- The full pending recursive family is retained: one code image, a successful
entry obligation, source coherence, and every finite-unroll return/bare-revert claim. -/
theorem recursive_claims (t : Table E ps rs qualifier) {C : Contract} {Γ Δ : Ctx}
    (lowerType : Source.STy → LTy) (b : Nat) (F : Evm.Frag Γ)
    (sites : ∀ i, RecursiveSite (t.candidate i) C Γ Δ lowerType)
    (producer : ∀ i, PendingRecursiveReturns b F (t.candidate i).identity.name
      (sites i).args (sites i).ret (sites i).step)
    (value : Source.Val E.layout (.fn false ps rs qualifier)) (word : Fin Evm.W)
    (represented : t.Rep value word) :
    ∃ i, functionName value = some (t.candidate i).identity ∧
      select t (fun j => PendingRecursiveReturns b F (t.candidate j).identity.name
        (sites j).args (sites j).ret (sites j).step) producer word = some ⟨i, producer i⟩ ∧
      (∃ n, SuccessfulEntry b F (recursiveSource (t.candidate i).identity.name
        (sites i).args (sites i).ret (sites i).step n) ((producer i).plan.at n)) ∧
      RecursiveReturnCoherence (t.candidate i).identity.name
        (sites i).args (sites i).ret (sites i).step ∧
      (∀ n, ReturnClaim b F (recursiveSource (t.candidate i).identity.name
        (sites i).args (sites i).ret (sites i).step n) ((producer i).plan.at n)) ∧
      (∀ n, BareRevertClaim b F (recursiveSource (t.candidate i).identity.name
        (sites i).args (sites i).ret (sites i).step n) ((producer i).plan.at n)) := by
  obtain ⟨i, identity, chosen⟩ := selected t _ producer value word represented
  exact ⟨i, identity, chosen, (producer i).required_successful_entry,
    (producer i).required_source_coherence, (producer i).required_return,
    (producer i).required_bare_revert⟩

/-- Explicit transport at a supplied represented entry. This transport uses
an explicit concrete Entry AND an actual intrinsic source return; it neither
constructs either witness and does not need to select the successful-entry witness. -/
theorem selected_call_return (t : Table E ps rs qualifier) {C : Contract} {Γ Δ : Ctx}
    (lowerType : Source.STy → LTy) (b : Nat) (F : Evm.Frag Γ)
    (sites : ∀ i, CallSite (t.candidate i) C Γ Δ lowerType)
    (producer : ∀ i, PendingCallProducer b F (t.candidate i).identity.name
      (sites i).args (sites i).ret (sites i).body)
    (word : Fin Evm.W) (i : Fin t.size) (chosen : t.decode word = some i)
    (L frame : Nat) (caller : State C Γ) (base : Nat → Fin Evm.W)
    (machine : Evm.Machine) (start : Nat)
    (entry : Entry (producer i).plan L b frame F caller base machine start)
    (out : Solidity.Out C caller.H Δ)
    (success : ((.call (t.candidate i).identity.name (sites i).args
      (sites i).ret (sites i).body : Stmt C Γ Δ).run caller) = .ok out) :
    select t (fun j => PendingCallProducer b F (t.candidate j).identity.name
      (sites j).args (sites j).ret (sites j).body) producer word = some ⟨i, producer i⟩ ∧
    Returned (producer i).plan L b frame caller base machine start out := by
  exact ⟨by simp only [select, chosen, Option.map_some],
    (producer i).required_return L frame caller base machine start entry out success⟩

/-- ONLY the failure-specialized V2 producer is used for reverting-run
transport. The three non-specialized bare fields remain explicit pending
claims until V3; they do not supply reverting admission or coverage. -/
theorem selected_call_bare_revert (t : Table E ps rs qualifier) {C : Contract} {Γ Δ : Ctx}
    (lowerType : Source.STy → LTy) (b : Nat) (F : Evm.Frag Γ)
    (sites : ∀ i, CallSite (t.candidate i) C Γ Δ lowerType)
    (producer : ∀ i, PendingBareRevertProducer b F (.call (t.candidate i).identity.name
      (sites i).args (sites i).ret (sites i).body))
    (word : Fin Evm.W) (i : Fin t.size) (chosen : t.decode word = some i)
    (L frame : Nat) (caller : State C Γ) (base : Nat → Fin Evm.W)
    (machine : Evm.Machine) (start : Nat)
    (entry : Entry (producer i).plan L b frame F caller base machine start)
    (failure : ((.call (t.candidate i).identity.name (sites i).args
      (sites i).ret (sites i).body : Stmt C Γ Δ).run caller) = .error .revert) :
    select t (fun j => PendingBareRevertProducer b F (.call (t.candidate j).identity.name
      (sites j).args (sites j).ret (sites j).body)) producer word = some ⟨i, producer i⟩ ∧
    Evm.run (producer i).plan.code machine = .revert := by
  exact ⟨by simp only [select, chosen, Option.map_some],
    (producer i).required_bare_revert L frame caller base machine start entry failure⟩

#print axioms selected_call_return
#print axioms selected_call_bare_revert

/-- Failure-specialized selection uses the exact V2 producer, with a real
reverting-entry obligation and no invented successful-return obligation. -/
theorem bare_claims (t : Table E ps rs qualifier) {C : Contract} {Γ Δ : Ctx}
    (lowerType : Source.STy → LTy) (b : Nat) (F : Evm.Frag Γ)
    (sites : ∀ i, CallSite (t.candidate i) C Γ Δ lowerType)
    (producer : ∀ i, PendingBareRevertProducer b F (.call (t.candidate i).identity.name
      (sites i).args (sites i).ret (sites i).body))
    (value : Source.Val E.layout (.fn false ps rs qualifier)) (word : Fin Evm.W)
    (represented : t.Rep value word) :
    ∃ i, functionName value = some (t.candidate i).identity ∧
      select t (fun j => PendingBareRevertProducer b F (.call (t.candidate j).identity.name
        (sites j).args (sites j).ret (sites j).body)) producer word = some ⟨i, producer i⟩ ∧
      RevertingEntry b F (.call (t.candidate i).identity.name
        (sites i).args (sites i).ret (sites i).body) (producer i).plan ∧
      BareRevertClaim b F (.call (t.candidate i).identity.name
        (sites i).args (sites i).ret (sites i).body) (producer i).plan := by
  obtain ⟨i, identity, chosen⟩ := selected t _ producer value word represented
  exact ⟨i, identity, chosen, (producer i).required_reverting_entry,
    (producer i).required_bare_revert⟩

/-- V2 ties the witnessed entry and return to the SAME caller. Conditional on
a supplied producer, this gives one genuine Returned witness, not admission of
all callers or a proof/instance of a physical runtime-frame producer. -/
theorem call_return_witness (t : Table E ps rs qualifier) {C : Contract} {Γ Δ : Ctx}
    (lowerType : Source.STy → LTy) (b : Nat) (F : Evm.Frag Γ)
    (sites : ∀ i, CallSite (t.candidate i) C Γ Δ lowerType)
    (producer : ∀ i, PendingCallProducer b F (t.candidate i).identity.name
      (sites i).args (sites i).ret (sites i).body) (i : Fin t.size) :
    ∃ (L frame : Nat) (caller : State C Γ) (base : Nat → Fin Evm.W)
      (machine : Evm.Machine) (start : Nat) (out : Solidity.Out C caller.H Δ),
      Entry (producer i).plan L b frame F caller base machine start ∧
      ((.call (t.candidate i).identity.name (sites i).args (sites i).ret
        (sites i).body : Stmt C Γ Δ).run caller) = .ok out ∧
      Returned (producer i).plan L b frame caller base machine start out := by
  obtain ⟨L, frame, caller, base, machine, start, out, entry, success⟩ :=
    (producer i).required_successful_entry
  exact ⟨L, frame, caller, base, machine, start, out, entry, success,
    (producer i).required_return L frame caller base machine start entry out success⟩

/-- A supplied V2 failure producer supplies one genuine matching source and
target bare revert. Other failure classes and successful coverage stay open. -/
theorem bare_revert_witness {C : Contract} {Γ Δ : Ctx} (b : Nat) (F : Evm.Frag Γ)
    (statement : Stmt C Γ Δ) (producer : PendingBareRevertProducer b F statement) :
    ∃ (L frame : Nat) (caller : State C Γ) (base : Nat → Fin Evm.W)
      (machine : Evm.Machine) (start : Nat),
      Entry producer.plan L b frame F caller base machine start ∧
      statement.run caller = .error .revert ∧ Evm.run producer.plan.code machine = .revert := by
  obtain ⟨L, frame, caller, base, machine, start, entry, failure⟩ := producer.required_reverting_entry
  exact ⟨L, frame, caller, base, machine, start, entry, failure,
    producer.required_bare_revert L frame caller base machine start entry failure⟩

#print axioms bare_claims
#print axioms call_return_witness
#print axioms bare_revert_witness

#print axioms call_claims
#print axioms fixed_claims
#print axioms recursive_claims
end Solidity.Backend.InternalDispatch.FrozenV2
