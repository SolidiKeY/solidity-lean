import Solidity.Backend.InternalFlow.RuntimeFrameCapturedProgram
import Solidity.Backend.InternalFlow.RuntimeFrameCallAgreement
import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV3

/-! Typed ordinary-call forms that retain the caller below fresh results.
This is a proof certificate for existing CallRet constructors, not a new AST,
value, evaluator or admission policy. RefArrayControls supplies actual allocating
reference witnesses; RefTupleCall and RefTupleControls certify mixed tuple
calls. StructDefaultCompile and StructDefaultControls add proved finite-default
framing/selection and a nested return case; StructRebindControls exercises actual
struct arguments and whole-return rebinding to the old graph. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducerRef
open Evm Evm.Memory

inductive Form (Γ : Ctx) : {rs Δ : Ctx} → CallRet Γ rs Δ → Ext Γ Δ → Prop where
 | memory (R : RefTy) (name : Var) (hd : (Ty.ref R).defaultOkS=true)
     (hm : (Ty.ref R).mapFree=true) :
     Form Γ (.mem R name hd hm) (.push .refl)
 | tuple {rs : Ctx} (binders : RetBinders rs) :
     Form Γ (.rets binders) (Ext.append Γ rs)

variable {C : Contract} {Γ Δ ps rs Γf : Ctx} {b : Nat} {F : Frag Γ}
 {f : Name} {args : Args C Γ ps} {ret : CallRet Γ rs Δ}
 {body : Prog C (rs ++ ps) Γf} {scope : Ext Γ Δ}

def plan (selected : Composition.Program b F (.cons (.call f args ret body) .nil))
 (lo pointer : Nat) : InterfaceV1.Emission C Γ Δ :=
 ⟨Restore.saveCells pointer (Restore.contextCells b Γ) ++ selected.checked.code ++
   Restore.restoreCells pointer (Restore.contextCells b Γ),
 selected.checked.frag,max selected.checked.need (max Γ.length Δ.length),lo,pointer,
 (fun _ => Γ.length+1),selected.checked.cost⟩

/-- Physical resource domain; agreement with approved remains an external
hypothesis. These fields are the exact Entry resource conditions. -/
def admitted (selected : Composition.Program b F (.cons (.call f args ret body) .nil))
 (lo pointer : Nat) : InterfaceV3.Admission C Γ := fun L frame caller base machine start =>
 StateRepr L b frame F caller base machine ∧
 b+max selected.checked.need (max Γ.length Δ.length)≤lo ∧
 lo≤pointer ∧ pointer<frame ∧ lo≤start ∧ start+(Γ.length+1)≤frame ∧
 (pointer<start ∨ start+(Γ.length+1)≤pointer) ∧ start+(Γ.length+1)<W ∧
 machine.mem pointer=.val (wmod start) ∧
 AllocationInput b frame (selected.checked.cost caller) caller base machine

/-- The syntactic form, not a desired source/target relation, yields the
exact old-caller tail of every actual successful call. -/
theorem source_tail (form : Form Γ ret scope) (caller : State C Γ)
 (out : Solidity.Out C caller.H Δ)
 (source : (.call f args ret body : Stmt C Γ Δ).run caller=.ok out) :
 TEnv.drop scope out.st.env=TEnv.wk out.ext Γ caller.env := by
 cases form with
 | memory R name hd hm =>
  exact CallAgreement.memory_tail f args R name hd hm body caller out source
 | @tuple rs binders =>
  obtain ⟨arguments,bodyOut,evaluated,executed,rfl⟩ :=
   CallAgreement.output_of_call f args (.rets binders) body caller out source
  change TEnv.drop (Ext.append Γ rs) (TEnv.append rs _ _) = _
  rw [TEnv.drop_append]

theorem coverage (selected : Composition.Program b F (.cons (.call f args ret body) .nil))
 (lo pointer : Nat) :
 InterfaceV3.EntryCoverage b F (admitted selected lo pointer) (plan selected lo pointer) := by
 intro L frame caller base machine start member
 obtain ⟨repr,workspace,pAbove,pBelow,payload,reserve,separate,nowrap,cursor,capacity⟩ := member
 have callerBound : b+Γ.length≤lo := by omega
 have resultBound : b+Δ.length≤lo := by omega
 exact ⟨repr,callerBound,resultBound,workspace,pAbove,pBelow,payload,reserve,
  Nat.le_refl _,separate,nowrap,cursor,capacity⟩

private theorem arena_bounds
 {selected : Composition.Program b F (.cons (.call f args ret body) .nil)}
 {lo pointer L frame start : Nat} {caller : State C Γ} {base : Nat → Fin W} {machine : Machine}
 (entry : InterfaceV1.Entry (plan selected lo pointer) L b frame F caller base machine start) :
 start+Γ.length≤frame ∧ (pointer<start ∨ start+Γ.length≤pointer) ∧ start+Γ.length<W := by
 have room := entry.reserve
 have apart := entry.separate
 have wrap := entry.noWrap
 change start+(Γ.length+1)≤frame at room
 change pointer<start ∨ start+(Γ.length+1)≤pointer at apart
 change start+(Γ.length+1)<W at wrap
 constructor
 · omega
 constructor <;> omega

/-- Real capture/checked execution/restoration retains all fresh results.
The source caller-tail is derived from Form; no simulation claim is assumed. -/
theorem returns (form : Form Γ ret scope)
 (selected : Composition.Program b F (.cons (.call f args ret body) .nil))
 (lo pointer : Nat) (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag scope) :
 InterfaceV1.ReturnClaim b F (.call f args ret body) (plan selected lo pointer) := by
 intro L frame caller base machine start entry out source
 obtain ⟨reserve,separate,fits⟩ := arena_bounds entry
 have workspace := entry.workspace
 change b+max selected.checked.need (max Γ.length Δ.length)≤lo at workspace
 have bodyBound : b+selected.checked.need≤lo := by omega
 have environment := source_tail form caller out source
 obtain ⟨saved,after,last,addresses,captureRun,bodyRun,restoreRun,whole,captured,recovered,
  bodyRepr,finalRepr,extension,growth,stack,cursor,locals⟩ :=
  CapturedProgram.endpoint selected entry.represented lo pointer start entry.callerBound
   bodyBound entry.resultBound entry.pointerAbove entry.pointerBelow entry.payloadAbove
   reserve separate fits entry.cursor entry.capacity out (CallAgreement.singleton_success source)
   scope environment flags
 obtain ⟨actualSaved,actualRun,actualCaptured,savedRepr,captureGrowth⟩ :=
  Context.capture_context machine lo pointer start entry.represented entry.callerBound
   entry.pointerAbove entry.pointerBelow entry.payloadAbove reserve separate fits entry.cursor
 have same : actualSaved=saved := (Evm.Out.ok.inj (actualRun.symm.trans captureRun)).1
 subst actualSaved
 have input : AllocationInput b frame (selected.checked.cost caller) caller base saved :=
  captureGrowth.nextInput (by simpa only [Nat.zero_add] using entry.capacity)
 have boundary : lo≤frame := by
  have below : pointer<frame := entry.pointerBelow
  have above : lo≤pointer := entry.pointerAbove
  omega
 have words := selected.safe savedRepr bodyBound boundary input bodyRun
 have older : Footprint.Words lo start machine last := by
  intro address lower upper
  by_cases header : address=pointer
  · subst address
    exact recovered.cursor.trans entry.cursor.symm
  · exact (recovered.exterior address lower header).trans
     ((words address lower (by omega)).trans (captured.exterior address header (.inl upper)))
 exact ⟨last,addresses,whole,finalRepr,stack,extension,growth,cursor,older⟩

theorem bare_revert (selected : Composition.Program b F (.cons (.call f args ret body) .nil))
 (lo pointer : Nat) :
 InterfaceV1.BareRevertClaim b F (.call f args ret body) (plan selected lo pointer) := by
 intro L frame caller base machine start entry source
 obtain ⟨reserve,separate,fits⟩ := arena_bounds entry
 have workspace := entry.workspace
 change b+max selected.checked.need (max Γ.length Δ.length)≤lo at workspace
 have bodyBound : b+selected.checked.need≤lo := by omega
 obtain ⟨saved,captureRun,captured,failed,whole⟩ := CapturedProgram.bare_revert selected
  entry.represented lo pointer start entry.callerBound bodyBound entry.pointerAbove
  entry.pointerBelow entry.payloadAbove reserve separate fits entry.cursor entry.capacity
  (CallAgreement.singleton_failure source) (Restore.restoreCells pointer (Restore.contextCells b Γ))
 exact whole

/-- Frozen V3 implementation for a checked memory/tuple call form. Both
real outcomes and independently supplied profile agreement remain explicit. -/
def make (form : Form Γ ret scope)
 (selected : Composition.Program b F (.cons (.call f args ret body) .nil))
 (lo pointer : Nat) (approved : InterfaceV3.Admission C Γ)
 (hprof : InterfaceV3.AdmissionAgreement approved (admitted selected lo pointer))
 (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag scope)
 (successful : InterfaceV3.SuccessfulEntry b F (admitted selected lo pointer)
  (.call f args ret body) (plan selected lo pointer))
 (reverting : InterfaceV3.RevertingEntry b F (admitted selected lo pointer)
  (.call f args ret body) (plan selected lo pointer)) :
 InterfaceV3.PendingCallProducer b F approved (admitted selected lo pointer) f args ret body where
 plan := plan selected lo pointer
 required_profile := hprof
 required_coverage := coverage selected lo pointer
 required_successful_entry := successful
 required_reverting_entry := reverting
 required_return := returns form selected lo pointer flags
 required_bare_revert := bare_revert selected lo pointer

/-- Exact-plan packaging target; make supplies the underlying producer. -/
abbrev ProducerGoal (selected : Composition.Program b F (.cons (.call f args ret body) .nil))
 (lo pointer : Nat) (approved : InterfaceV3.Admission C Γ) :=
 {producer : InterfaceV3.PendingCallProducer b F approved (admitted selected lo pointer) f args ret body //
  producer.plan=plan selected lo pointer}

end Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducerRef
