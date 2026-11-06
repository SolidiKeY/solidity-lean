import Solidity.Backend.InternalDispatch.FrozenV1
import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV3

/-! Ordinary dependent dispatch consumes the exact frozen V3 input domain.
Only actual approved inputs obtain Entry through universal coverage; neither
admission nor execution is obtained from the outcome witnesses. Source-to-
intrinsic call-site lowering and approved provenance remain separate producer
obligations. This adds no fixed/recursive or external-call coverage. -/
namespace Solidity.Backend.InternalDispatch.FrozenV3
open FrozenV1
open Solidity.Backend.InternalFlow.RuntimeFrame.InterfaceV1 (Entry Returned)
open Solidity.Backend.InternalFlow.RuntimeFrame.InterfaceV3
 (Admission PendingCallProducer EntryCoverage SuccessfulEntry RevertingEntry)
variable {E : Source.Env} {ps rs : List Source.STy} {qualifier : Option Source.Mutability}

abbrev CallFamily (t : Table E ps rs qualifier) {C : Contract} {Γ Δ : Ctx}
 (lowerType : Source.STy → LTy) (b : Nat) (F : Evm.Frag Γ)
 (sites : ∀ i, CallSite (t.candidate i) C Γ Δ lowerType)
 (approved admitted : Fin t.size → Admission C Γ) :=
 ∀ i, PendingCallProducer b F (approved i) (admitted i) (t.candidate i).identity.name
  (sites i).args (sites i).ret (sites i).body

variable (t : Table E ps rs qualifier) {C : Contract} {Γ Δ : Ctx}
 (lowerType : Source.STy → LTy) (b : Nat) (F : Evm.Frag Γ)
 (sites : ∀ i, CallSite (t.candidate i) C Γ Δ lowerType)
 (approved admitted : Fin t.size → Admission C Γ)
 (producer : CallFamily t lowerType b F sites approved admitted)

/-- Representation of the dependent function value selects the same candidate,
including both real outcome witnesses and universal exact-input coverage. -/
theorem call_claims
 (value : Source.Val E.layout (.fn false ps rs qualifier)) (word : Fin Evm.W)
 (represented : t.Rep value word) :
 ∃ i, functionName value=some (t.candidate i).identity ∧
  select t _ producer word=some ⟨i,producer i⟩ ∧
  EntryCoverage b F (admitted i) (producer i).plan ∧
  SuccessfulEntry b F (admitted i) (.call (t.candidate i).identity.name
   (sites i).args (sites i).ret (sites i).body) (producer i).plan ∧
  RevertingEntry b F (admitted i) (.call (t.candidate i).identity.name
   (sites i).args (sites i).ret (sites i).body) (producer i).plan := by
 obtain ⟨i,identity,chosen⟩ := selected t _ producer value word represented
 exact ⟨i,identity,chosen,(producer i).required_coverage,
  (producer i).required_successful_entry,(producer i).required_reverting_entry⟩

/-- A selected ordinary call runs from the very same approved input. There
is no caller/map/machine substitution and no separate Entry premise. -/
theorem selected_call_return
 (word : Fin Evm.W) (i : Fin t.size) (chosen : t.decode word=some i)
 (L frame : Nat) (caller : State C Γ) (base : Nat → Fin Evm.W)
 (machine : Evm.Machine) (start : Nat)
 (member : approved i L frame caller base machine start)
 (out : Solidity.Out C caller.H Δ)
 (source : (.call (t.candidate i).identity.name (sites i).args
  (sites i).ret (sites i).body : Stmt C Γ Δ).run caller=.ok out) :
 select t _ producer word=some ⟨i,producer i⟩ ∧
 Returned (producer i).plan L b frame caller base machine start out := by
 have entry : Entry (producer i).plan L b frame F caller base machine start :=
  (producer i).required_coverage L frame caller base machine start
   (((producer i).required_profile L frame caller base machine start).mp member)
 exact ⟨by simp only [select,chosen,Option.map_some],
  (producer i).required_return L frame caller base machine start entry out source⟩

/-- Exact actual bare failure from an approved input. This does not infer
payload/panic/world behavior or obtain a failing caller from the witness. -/
theorem selected_call_bare_revert
 (word : Fin Evm.W) (i : Fin t.size) (chosen : t.decode word=some i)
 (L frame : Nat) (caller : State C Γ) (base : Nat → Fin Evm.W)
 (machine : Evm.Machine) (start : Nat)
 (member : approved i L frame caller base machine start)
 (source : (.call (t.candidate i).identity.name (sites i).args
  (sites i).ret (sites i).body : Stmt C Γ Δ).run caller=.error .revert) :
 select t _ producer word=some ⟨i,producer i⟩ ∧
 Evm.run (producer i).plan.code machine=.revert := by
 have entry : Entry (producer i).plan L b frame F caller base machine start :=
  (producer i).required_coverage L frame caller base machine start
   (((producer i).required_profile L frame caller base machine start).mp member)
 exact ⟨by simp only [select,chosen,Option.map_some],
  (producer i).required_bare_revert L frame caller base machine start entry source⟩

/-- Uninitialized and foreign dispatch words still select no producer. -/
theorem zero_refused : select t _ producer (Evm.wmod 0)=none := by
 first | simp only [select,t.decode_zero,Option.map_none] | decide | omega | rfl

theorem foreign_refused (word : Fin Evm.W) (foreign : t.size<word.val) :
 select t _ producer word=none := FrozenV1.foreign_refused t _ producer word foreign

end Solidity.Backend.InternalDispatch.FrozenV3
