import Solidity.Backend.InternalFlow.RuntimeFrameCallAgreement
import Solidity.Backend.InternalFlow.RuntimeFrameCapturedReference
import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV2

/-! Construct actual v2 void-return call producers from checked finite call
certificates. Return and bare-revert duties are proved here; only genuine
checked input, fragment compatibility and successful-entry evidence are inputs.
This is not an unbounded recursive dispatcher or a world-frame theorem. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.NoneProducer
open Evm Evm.Memory
variable {C : Contract} {Γ ps Γf : Ctx} {b : Nat} {F : Frag Γ}
 {f : Name} {args : Args C Γ ps} {body : Prog C ps Γf}

def plan (selected : Composition.Program b F (.cons (.call f args .none body) .nil))
 (lo pointer : Nat) : InterfaceV1.Emission C Γ Γ :=
 ⟨Restore.saveCells pointer (Restore.contextCells b Γ) ++ selected.checked.code ++
   Restore.restoreCells pointer (Restore.contextCells b Γ),
  selected.checked.frag,selected.checked.need,lo,pointer,(fun _ => Γ.length+1),selected.checked.cost⟩

theorem arena_bounds {selected : Composition.Program b F (.cons (.call f args .none body) .nil)}
 {lo pointer L frame start : Nat} {caller : State C Γ} {base : Nat → Fin W} {machine : Machine}
 (entry : InterfaceV1.Entry (plan selected lo pointer) L b frame F caller base machine start) :
 start+Γ.length≤frame ∧ (pointer<start ∨ start+Γ.length≤pointer) ∧ start+Γ.length<W := by
 have reserve := entry.reserve
 have separate := entry.separate
 have fits := entry.noWrap
 change start+(Γ.length+1)≤frame at reserve
 change pointer<start ∨ start+(Γ.length+1)≤pointer at separate
 change start+(Γ.length+1)<W at fits
 constructor
 · omega
 constructor
 · rcases separate with left | right
   · exact .inl left
   · exact .inr (by omega)
 · omega

/-- The source caller-tail obligation is DERIVED from the actual call. -/
theorem returns (selected : Composition.Program b F (.cons (.call f args .none body) .nil))
 (lo pointer : Nat) (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag .refl) :
 InterfaceV1.ReturnClaim b F (.call f args .none body) (plan selected lo pointer) := by
 intro L frame caller base machine start entry out source
 obtain ⟨reserve,separate,fits⟩ := arena_bounds entry
 have environment := CallAgreement.none_tail f args body caller out source
 have programSource := CallAgreement.singleton_success source
 obtain ⟨saved,after,last,addresses,captureRun,bodyRun,restoreRun,whole,captured,recovered,
  bodyRepr,finalRepr,extended,growth,stack,cursor,locals⟩ :=
  CapturedProgram.endpoint selected entry.represented lo pointer start entry.callerBound entry.workspace
   entry.resultBound entry.pointerAbove entry.pointerBelow entry.payloadAbove reserve separate fits entry.cursor
   entry.capacity out programSource .refl environment flags
 obtain ⟨actualSaved,actualRun,actualCaptured,savedRepr,captureGrowth⟩ :=
  Context.capture_context machine lo pointer start entry.represented entry.callerBound entry.pointerAbove
   entry.pointerBelow entry.payloadAbove reserve separate fits entry.cursor
 have same : actualSaved=saved := (Evm.Out.ok.inj (actualRun.symm.trans captureRun)).1
 subst actualSaved
 have input : AllocationInput b frame (selected.checked.cost caller) caller base saved :=
  captureGrowth.nextInput (by simpa only [Nat.zero_add] using entry.capacity)
 have bodyWords := selected.safe savedRepr entry.workspace (by have h:=entry.pointerBelow;have h':=entry.pointerAbove;omega) input bodyRun
 have older := CapturedReference.older_words captured bodyWords recovered (by omega) entry.cursor
 exact ⟨last,addresses,whole,finalRepr,stack,extended,growth,cursor,older⟩

/-- Bare failure is exact and absorbs restoration, without a failed state. -/
theorem bare_revert (selected : Composition.Program b F (.cons (.call f args .none body) .nil))
 (lo pointer : Nat) :
 InterfaceV1.BareRevertClaim b F (.call f args .none body) (plan selected lo pointer) := by
 intro L frame caller base machine start entry source
 obtain ⟨reserve,separate,fits⟩ := arena_bounds entry
 obtain ⟨saved,captureRun,captured,failed,whole⟩ := CapturedProgram.bare_revert selected entry.represented
  lo pointer start entry.callerBound entry.workspace entry.pointerAbove entry.pointerBelow entry.payloadAbove
  reserve separate fits entry.cursor entry.capacity (CallAgreement.singleton_failure source)
  (Restore.restoreCells pointer (Restore.contextCells b Γ))
 exact whole

/-- An implemented producer value: correctness duties are derived, never
passed as premises. The witness is genuine input non-vacuity, not simulation. -/
def make (selected : Composition.Program b F (.cons (.call f args .none body) .nil))
 (lo pointer : Nat) (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag .refl)
 (successful : InterfaceV2.SuccessfulEntry b F (.call f args .none body) (plan selected lo pointer)) :
 InterfaceV2.PendingCallProducer b F f args .none body where
 plan := plan selected lo pointer
 required_successful_entry := successful
 required_return := returns selected lo pointer flags
 required_bare_revert := bare_revert selected lo pointer

/-- Failure-specialized producer, not an assertion of exclusively failing
source behavior or restored execution after a failure. -/
def make_failure (selected : Composition.Program b F (.cons (.call f args .none body) .nil))
 (lo pointer : Nat)
 (reverting : InterfaceV2.RevertingEntry b F (.call f args .none body) (plan selected lo pointer)) :
 InterfaceV2.PendingBareRevertProducer b F (.call f args .none body) where
 plan := plan selected lo pointer
 required_reverting_entry := reverting
 required_bare_revert := bare_revert selected lo pointer

/-- All quotation indices of ONE existing fixed thunk use the same checked
code. This follows the existing callRec equation, not unbounded recursion. -/
def make_fixed {C : Contract} {Γ ps : Ctx} {b : Nat} {F : Frag Γ}
 {f : Name} {args : Args C Γ ps} (thunk : Unit → Prog C ps ps)
 (selected : Composition.Program b F (.cons (.call f args .none (thunk ())) .nil))
 (lo pointer : Nat) (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag .refl)
 (successful : InterfaceV2.SuccessfulEntry b F (.call f args .none (thunk ())) (plan selected lo pointer)) :
 InterfaceV2.PendingFixedCallRecProducer b F f args .none thunk where
 plan := plan selected lo pointer
 required_successful_entry := by
  intro d
  obtain ⟨L,frame,caller,base,machine,start,out,entry,source⟩ := successful
  exact ⟨L,frame,caller,base,machine,start,out,entry,source⟩
 required_return := by
  intro d L frame caller base machine start entry out source
  exact returns selected lo pointer flags L frame caller base machine start entry out source
 required_bare_revert := by
  intro d L frame caller base machine start entry source
  exact bare_revert selected lo pointer L frame caller base machine start entry source

theorem init_flag {Γ : Ctx} {t : LTy} (index : Idx Γ t) : (Frag.init Γ).get index=.ok := by
 induction index with
 | here => rfl
 | there index ih => exact ih

/-- This uses the actual initial fragment classification, not a promotion
of a dead or fragile old alias into a live one. -/
theorem init_flags {Γ Δ : Ctx} (G : Frag Δ) (scope : Ext Γ Δ) :
 InterfaceV1.NoAliasPromotion (Frag.init Γ) G scope := by
 intro R index live
 rw [init_flag]
 decide

end Solidity.Backend.InternalFlow.RuntimeFrame.NoneProducer
