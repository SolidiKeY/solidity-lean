import Solidity.Backend.InternalDispatch.Chain
import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV1

/-! Consume the exact frozen P1 v1 producer structures. No producer is
constructed here. The generic independent Source ObservationModel remains
separate: it is not a physical P1 implementation or a source-lowering proof. -/
namespace Solidity.Backend.InternalDispatch
namespace FrozenV1
open Solidity.Backend.InternalFlow.RuntimeFrame.InterfaceV1

variable {E : Source.Env} {ps rs : List Source.STy} {qualifier : Option Source.Mutability}

/-- Typed intrinsic call site for a source candidate. Mapping source types to
intrinsic locals is explicit. Full argument/return list indices are retained;
semantic source-to-intrinsic lowering is a separate producer obligation. -/
structure CallSite (candidate : Candidate E ps rs qualifier) (C : Contract)
    (Γ Δ : Ctx) (lowerType : Source.STy → LTy) where
  bodyCtx : Ctx
  args : Args C Γ (ps.map lowerType)
  ret : CallRet Γ (rs.map lowerType) Δ
  body : Prog C (rs.map lowerType ++ ps.map lowerType) bodyCtx

structure FixedSite (candidate : Candidate E ps rs qualifier) (C : Contract)
    (Γ Δ : Ctx) (lowerType : Source.STy → LTy) where
  args : Args C Γ (ps.map lowerType)
  ret : CallRet Γ (rs.map lowerType) Δ
  body : Unit → Prog C (rs.map lowerType ++ ps.map lowerType) (rs.map lowerType ++ ps.map lowerType)

structure RecursiveSite (candidate : Candidate E ps rs qualifier) (C : Contract)
    (Γ Δ : Ctx) (lowerType : Source.STy → LTy) where
  args : Args C Γ (ps.map lowerType)
  ret : CallRet Γ (rs.map lowerType) Δ
  step : Nat → (Unit → Prog C (rs.map lowerType ++ ps.map lowerType)
    (rs.map lowerType ++ ps.map lowerType)) → Prog C
      (rs.map lowerType ++ ps.map lowerType) (rs.map lowerType ++ ps.map lowerType)

/-- Select an entire dependent producer, without erasing any of its obligations. -/
def select (t : Table E ps rs qualifier) (P : Fin t.size → Type)
    (producer : ∀ i, P i) (word : Fin Evm.W) : Option (Sigma P) :=
  (t.decode word).map (fun i => ⟨i, producer i⟩)

theorem selected (t : Table E ps rs qualifier) (P : Fin t.size → Type)
    (producer : ∀ i, P i) (value : Source.Val E.layout (.fn false ps rs qualifier))
    (word : Fin Evm.W) (represented : t.Rep value word) :
    ∃ i, functionName value = some (t.candidate i).identity ∧
      select t P producer word = some ⟨i, producer i⟩ := by
  obtain ⟨i, identity, rfl⟩ := represented
  exact ⟨i, identity, by simp only [select, t.decode_tag, Option.map_some]⟩

theorem zero_refused (t : Table E ps rs qualifier) (P : Fin t.size → Type)
    (producer : ∀ i, P i) : select t P producer (Evm.wmod 0) = none := by
  simp only [select, t.decode_zero, Option.map_none]

theorem foreign_refused (t : Table E ps rs qualifier) (P : Fin t.size → Type)
    (producer : ∀ i, P i) (word : Fin Evm.W) (foreign : t.size < word.val) :
    select t P producer word = none := by
  unfold select Table.decode
  split
  · rename_i h; omega
  · rfl

/-- Ordinary calls use PendingCallProducer verbatim, including realizability
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
      RealizableEntry b F (producer i).plan ∧
      ReturnClaim b F (.call (t.candidate i).identity.name
        (sites i).args (sites i).ret (sites i).body) (producer i).plan ∧
      BareRevertClaim b F (.call (t.candidate i).identity.name
        (sites i).args (sites i).ret (sites i).body) (producer i).plan := by
  obtain ⟨i, identity, chosen⟩ := selected t _ producer value word represented
  exact ⟨i, identity, chosen, (producer i).required_entry,
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
      RealizableEntry b F (producer i).plan ∧
      (∀ d, ReturnClaim b F (.callRec (t.candidate i).identity.name d
        (sites i).args (sites i).ret (sites i).body) (producer i).plan) ∧
      (∀ d, BareRevertClaim b F (.callRec (t.candidate i).identity.name d
        (sites i).args (sites i).ret (sites i).body) (producer i).plan) := by
  obtain ⟨i, identity, chosen⟩ := selected t _ producer value word represented
  exact ⟨i, identity, chosen, (producer i).required_entry,
    (producer i).required_return, (producer i).required_bare_revert⟩

/-- The full pending recursive family is retained: one code image, an actual
entry, source coherence, and every finite-unroll return/bare-revert claim. -/
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
      (∃ n, RealizableEntry b F ((producer i).plan.at n)) ∧
      RecursiveReturnCoherence (t.candidate i).identity.name
        (sites i).args (sites i).ret (sites i).step ∧
      (∀ n, ReturnClaim b F (recursiveSource (t.candidate i).identity.name
        (sites i).args (sites i).ret (sites i).step n) ((producer i).plan.at n)) ∧
      (∀ n, BareRevertClaim b F (recursiveSource (t.candidate i).identity.name
        (sites i).args (sites i).ret (sites i).step n) ((producer i).plan.at n)) := by
  obtain ⟨i, identity, chosen⟩ := selected t _ producer value word represented
  exact ⟨i, identity, chosen, (producer i).required_entry,
    (producer i).required_source_coherence, (producer i).required_return,
    (producer i).required_bare_revert⟩

#print axioms call_claims
#print axioms fixed_claims
#print axioms recursive_claims
end FrozenV1
end Solidity.Backend.InternalDispatch
