import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV3
import Solidity.Backend.InternalFlow.RuntimeFrameCapturedProgram
import Solidity.Backend.InternalFlow.RuntimeFrameCallAgreement

/-! P1-CALL checkpoint: primitive value-returning ordinary calls.
The reached result is saved in a private local cell before caller restoration,
and exported into its caller destination AFTER restoration. The make constructor
supplies the frozen V3 producer from explicit profile agreement and real dual
outcome witnesses. Genuine witnesses are in its Controls module. No approved source domain is defined.
Literal revert and other scratch-selector refusals are unchanged. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducer
open Evm Evm.Memory
variable {C : Contract} {Γ ps Γf : Ctx} {b : Nat} {F : Frag Γ}
 {f : Name} {args : Args C Γ ps} {p : PrimTy} {r : Var}
 {destination : Idx Γ (.val p)} {body : Prog C (.val p :: ps) Γf}

/-- Reserve a private result cell above every caller cell. Its value is written
only after the checked call has completed, so it need not survive the body. -/
def need (selected : Composition.Program b F
    (.cons (.call f args (.val p r (some destination)) body) .nil)) : Nat :=
 max selected.checked.need Γ.length + 1

def code (selected : Composition.Program b F
    (.cons (.call f args (.val p r (some destination)) body) .nil))
    (lo pointer : Nat) : List Instr :=
 Restore.saveCells pointer (Restore.contextCells b Γ) ++ selected.checked.code ++
 [.mload (cellOf b destination), .mstore (lo-1)] ++
 Restore.restoreCells pointer (Restore.contextCells b Γ) ++
 [.mload (lo-1), .mstore (cellOf b destination)]

def plan (selected : Composition.Program b F
    (.cons (.call f args (.val p r (some destination)) body) .nil))
    (lo pointer : Nat) : InterfaceV1.Emission C Γ Γ :=
 ⟨code selected lo pointer, selected.checked.frag, need selected, lo, pointer,
   (fun _ => Γ.length+1), selected.checked.cost⟩

/-- Physical, typed initial inputs. The definition never mentions Entry,
source outcomes, an approved-profile predicate, or a caller whitelist. -/
def admitted (selected : Composition.Program b F
    (.cons (.call f args (.val p r (some destination)) body) .nil))
    (lo pointer : Nat) : InterfaceV3.Admission C Γ :=
 fun L frame caller base machine start =>
 StateRepr L b frame F caller base machine ∧
 b + (max selected.checked.need Γ.length + 1) ≤ lo ∧
 lo ≤ pointer ∧ pointer < frame ∧ lo ≤ start ∧
 start + (Γ.length+1) ≤ frame ∧
 (pointer < start ∨ start+(Γ.length+1) ≤ pointer) ∧
 start + (Γ.length+1) < W ∧
 machine.mem pointer = .val (wmod start) ∧
 AllocationInput b frame (selected.checked.cost caller) caller base machine

/-- Every typed physical input has Entry for that SAME caller, map,
machine, frame and cursor. No outcome or caller filtering is introduced. -/
theorem coverage (selected : Composition.Program b F
 (.cons (.call f args (.val p r (some destination)) body) .nil))
 (lo pointer : Nat) :
 InterfaceV3.EntryCoverage b F (admitted selected lo pointer) (plan selected lo pointer) := by
 intro L frame caller base machine start member
 obtain ⟨represented,workspace,pointerAbove,pointerBelow,payloadAbove,reserve,
  separate,noWrap,cursor,capacity⟩ := member
 have callerBound : b+Γ.length≤lo := by omega
 exact ⟨represented,callerBound,callerBound,workspace,pointerAbove,pointerBelow,
  payloadAbove,reserve,Nat.le_refl _,separate,noWrap,cursor,capacity⟩

/-- Actual value-call semantics preserves every other caller local, including
reference identities, through the actual reached heap extension. -/
theorem source_other (caller : State C Γ) (out : Solidity.Out C caller.H Γ)
 (source : (.call f args (.val p r (some destination)) body : Stmt C Γ Γ).run caller=.ok out)
 {t : LTy} (index : Idx Γ t) (different : destination.toNat ≠ index.toNat) :
 TEnv.get index out.st.env = LTy.TDenote.wk out.ext t (TEnv.get index caller.env) := by
 obtain ⟨arguments,bodyOut,evaluated,executed,same⟩ :=
  CallAgreement.output_of_call f args (.val p r (some destination)) body caller out source
 subst out
 change TEnv.get index (TEnv.set destination _ (TEnv.wk _ Γ caller.env)) = _
 rw [TEnv.get_set_ne destination index _ _ different,TEnv.get_wk]

/-- Pointwise caller agreement is sufficient away from the actual returned
primitive destination. No old heap contents or alias promotion is inferred. -/
theorem other_word {L frame : Nat} {G : Frag Γ}
 {caller : State C Γ} {out : Solidity.Out C caller.H Γ}
 {base addresses : Nat → Fin W} {before after : Machine}
 (initial : StateRepr L b frame F caller base before)
 (reached : StateRepr L b frame G out.st addresses after)
 (source : (.call f args (.val p r (some destination)) body : Stmt C Γ Γ).run caller=.ok out)
 (extension : BaseExtends caller.H base addresses)
 (flags : InterfaceV1.NoAliasPromotion F G .refl)
 {t : LTy} (index : Idx Γ t) (different : destination.toNat ≠ index.toNat)
 (needed : Restored.Observed G index) :
 before.mem (cellOf b index) = after.mem (cellOf b index) := by
 have transported := source_other caller out source index different
 have read : Look.ofTEnv out.st.env index = Look.ofTEnv caller.env index := by
  simp only [Look.ofTEnv,transported,see_wk]
 cases t with
 | val q =>
  have a := initial.core.vals index
  have z := reached.core.vals index
  rw [read] at z
  exact Restored.value_unique a z
 | mem R =>
  obtain ⟨old,oldValue,oldWord⟩ := initial.pointers index
  obtain ⟨current,currentValue,currentWord⟩ := reached.pointers index
  have value : TEnv.get index out.st.env = some (old.wk out.ext) := by
   rw [transported,oldValue]
   rfl
  have same : current = old.wk out.ext := Option.some.inj (currentValue.symm.trans value)
  subst current
  simp only [HRef.wk] at currentWord
  rw [extension old] at currentWord
  exact oldWord.trans currentWord.symm
 | alias R =>
  obtain ⟨old,oldSlot,oldValue,oldWord,oldPath⟩ := Restored.alias_slot initial index (flags index needed)
  obtain ⟨current,currentSlot,currentValue,currentWord,currentPath⟩ := Restored.alias_slot reached index needed
  have same : old = current := Option.some.inj (oldValue.symm.trans (read.symm.trans currentValue))
  subst current
  have slot := Restored.path_unique oldPath currentPath
  rw [← slot] at currentWord
  exact oldWord.trans currentWord.symm
 | old => exact needed.elim
 | oldNet => exact needed.elim
 | kint => exact needed.elim

/-- A real checked bare failure absorbs result capture, restoration and
export. It does not assert a final machine or fabricate a reverting caller. -/
theorem bare_revert (selected : Composition.Program b F
    (.cons (.call f args (.val p r (some destination)) body) .nil))
    (lo pointer : Nat) :
 InterfaceV1.BareRevertClaim b F (.call f args (.val p r (some destination)) body)
    (plan selected lo pointer) := by
 intro L frame caller base machine start entry source
 have workspace := entry.workspace
 change b + (max selected.checked.need Γ.length + 1) ≤ lo at workspace
 have localBound : b + Γ.length ≤ lo := by omega
 have bodyBound : b + selected.checked.need ≤ lo := by omega
 have reserve := entry.reserve
 change start + (Γ.length+1) ≤ frame at reserve
 have separate := entry.separate
 change pointer < start ∨ start + (Γ.length+1) ≤ pointer at separate
 have fits := entry.noWrap
 change start + (Γ.length+1) < W at fits
 have room : start + Γ.length ≤ frame := by omega
 have disjoint : pointer < start ∨ start + Γ.length ≤ pointer := by omega
 have nowrap : start + Γ.length < W := by omega
 obtain ⟨saved,captureRun,captured,failed,whole⟩ :=
  CapturedProgram.bare_revert selected entry.represented lo pointer start
   localBound bodyBound entry.pointerAbove entry.pointerBelow entry.payloadAbove
   room disjoint nowrap entry.cursor entry.capacity
   (CallAgreement.singleton_failure source)
   ([.mload (cellOf b destination), .mstore (lo-1)] ++
    Restore.restoreCells pointer (Restore.contextCells b Γ) ++
    [.mload (lo-1), .mstore (cellOf b destination)])
 simpa only [plan,code,List.append_assoc] using whole

/-- Successful ordinary primitive calls restore every caller word before
exporting the reached primitive result. Physical capture, checked execution,
restoration and the final write are all derived from their real evaluators. -/
theorem returns (selected : Composition.Program b F
    (.cons (.call f args (.val p r (some destination)) body) .nil))
    (lo pointer : Nat) (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag .refl) :
 InterfaceV1.ReturnClaim b F (.call f args (.val p r (some destination)) body)
    (plan selected lo pointer) := by
 intro L frame caller base machine start entry out source
 have workspace := entry.workspace
 change b + (max selected.checked.need Γ.length + 1) ≤ lo at workspace
 have callerBound : b+Γ.length≤lo := by omega
 have bodyBound : b+selected.checked.need≤lo := by omega
 have scratchAbove : b+Γ.length≤lo-1 := by omega
 have scratchBelow : lo-1<lo := by omega
 have pointerAbove : lo≤pointer := entry.pointerAbove
 have pointerBelow : pointer<frame := entry.pointerBelow
 have payloadAbove : lo≤start := entry.payloadAbove
 have reserve := entry.reserve
 change start+(Γ.length+1)≤frame at reserve
 have separate := entry.separate
 change pointer<start ∨ start+(Γ.length+1)≤pointer at separate
 have fits := entry.noWrap
 change start+(Γ.length+1)<W at fits
 have room : start+Γ.length≤frame := by omega
 have disjoint : pointer<start ∨ start+Γ.length≤pointer := by omega
 have nowrap : start+Γ.length<W := by omega
 obtain ⟨saved,captureRun,captured,savedRepr,captureGrowth⟩ :=
  Context.capture_context machine lo pointer start entry.represented callerBound
   pointerAbove pointerBelow payloadAbove room disjoint nowrap entry.cursor
 have input : AllocationInput b frame (selected.checked.cost caller) caller base saved :=
  captureGrowth.nextInput (by simpa only [Nat.zero_add] using entry.capacity)
 obtain ⟨after,addresses,bodyRun,reached,bodyStack,extension,bodyGrowth,words⟩ :=
  Composition.endpoint selected savedRepr bodyBound (by omega) input out
   (CallAgreement.singleton_success source)
 let privateAfter := writeMachine after (lo-1) (after.mem (cellOf b destination))
 have saveResult : Evm.run [.mload (cellOf b destination),.mstore (lo-1)] after =
   .ok privateAfter 0 := rfl
 have count : (Restore.contextCells b Γ).length=Γ.length := by
  simp only [Restore.contextCells,List.length_map,List.length_range]
 have pointerKept : privateAfter.mem pointer=.val (wmod (start+Γ.length)) := by
  change upd after.mem (lo-1) _ pointer = _
  rw [upd_other _ _ (by omega)]
  exact (words pointer pointerAbove pointerBelow).trans (by simpa only [count] using captured.cursor)
 have payloadKept : ∀ i (_hi : i<Γ.length),privateAfter.mem (start+i)=machine.mem (b+i) := by
  intro i hi
  change upd after.mem (lo-1) _ (start+i) = _
  rw [upd_other _ _ (by omega)]
  have bound : i<(Restore.contextCells b Γ).length := by simpa only [count] using hi
  have actual := captured.payload i bound
  simp only [Restore.contextCells,List.getElem_map,List.getElem_range] at actual
  exact (words (start+i) (by omega) (by omega)).trans actual
 obtain ⟨restored,restoreRun,recovered,bindings⟩ :=
  Context.restore_context b Γ machine privateAfter lo pointer start callerBound
   pointerAbove payloadAbove disjoint nowrap pointerKept payloadKept
 have privateNotCaptured : lo-1 ∉ Restore.contextCells b Γ := by
  intro member
  have upper := (Restored.member_bounds b Γ _ member).2
  omega
 have returnedWord : restored.mem (lo-1)=after.mem (cellOf b destination) := by
  have actual := recovered.locals (lo-1) scratchBelow
  rw [if_neg privateNotCaptured] at actual
  exact actual.trans (upd_same _ _ _)
 let final := writeMachine restored (cellOf b destination) (after.mem (cellOf b destination))
 have exportResult : Evm.run [.mload (lo-1),.mstore (cellOf b destination)] restored =
   .ok final 0 := by
  change Evm.Out.ok (writeMachine restored (cellOf b destination) (restored.mem (lo-1))) 0 = _
  rw [returnedWord]
 have destBelow : cellOf b destination<lo := Nat.lt_of_lt_of_le (lvl_lt b destination) callerBound
 have localAgreement : ∀ {t : LTy} (index : Idx Γ t), Restored.Observed selected.checked.frag index →
   final.mem (cellOf b index)=after.mem (cellOf b index) := by
  intro t index needed
  by_cases same : cellOf b index=cellOf b destination
  · change upd restored.mem (cellOf b destination) _ (cellOf b index) = _
    rw [same,upd_same]
  · change upd restored.mem (cellOf b destination) _ (cellOf b index) = _
    rw [upd_other _ _ same,bindings index]
    have different : destination.toNat≠index.toNat := by
     intro equality
     exact same ((lvl_eq_iff b index destination).mpr equality.symm)
    exact other_word entry.represented reached source extension flags index different needed
 have heapAgreement : ∀ x, frame≤x → final.mem x=after.mem x := by
  intro x above
  change upd restored.mem (cellOf b destination) _ x = _
  rw [upd_other _ _ (by omega),recovered.exterior x (by omega) (by omega)]
  exact upd_other _ _ (by omega)
 have represented := Restored.memory_transport reached final.mem localAgreement heapAgreement
 have changed := represented.stack final.stack
 have fields : {after with mem:=final.mem,stack:=final.stack}=final := by
  have actual := congrArg (fun m : Machine => {m with mem:=final.mem,stack:=final.stack}) recovered.fields
  exact actual.symm
 rw [fields] at changed
 have whole : Evm.run (code selected lo pointer) machine=.ok final 0 := by
  simp only [code,List.append_assoc]
  rw [Evm.run_append_ok captureRun,Evm.run_append_ok bodyRun,
   Evm.run_append_ok saveResult,Evm.run_append_ok restoreRun]
  exact exportResult
 have cursor : final.mem pointer=.val (wmod start) := by
  change upd restored.mem (cellOf b destination) _ pointer = _
  rw [upd_other _ _ (by omega)]
  exact recovered.cursor
 have older : Footprint.Words lo start machine final := by
  intro x lower upper
  change upd restored.mem (cellOf b destination) _ x = _
  rw [upd_other _ _ (by omega)]
  by_cases header : x=pointer
  · subst x
    exact recovered.cursor.trans entry.cursor.symm
  · rw [recovered.exterior x lower header]
    change upd after.mem (lo-1) _ x = _
    rw [upd_other _ _ (by omega)]
    exact (words x lower (by omega)).trans (captured.exterior x header (.inl upper))
 have growth : GrowsAllocator b frame (selected.checked.cost caller) caller base machine out.st addresses final := by
  intro oldCursor positive allocation space
  have total : GrowsAllocator b frame (selected.checked.cost caller) caller base machine out.st addresses after := by
   simpa only [Nat.zero_add] using captureGrowth.comp bodyGrowth
  have allocated := total oldCursor positive allocation space
  have scratchAllocation := allocated.localWrite (lo-1) (by omega) (by omega) (after.mem (cellOf b destination))
  have bounds : ∀ x∈Restore.contextCells b Γ,0<x ∧ x<frame := by
   intro x member
   have bound := Restored.member_bounds b Γ x member
   constructor <;> omega
  have restoredAllocation := recovered.allocator out.st.heap addresses frame _ bounds
   (by omega) pointerBelow scratchAllocation
  exact restoredAllocation.localWrite (cellOf b destination)
   (Nat.lt_of_lt_of_le positive (le_lvl b destination)) (by omega)
   (after.mem (cellOf b destination))
 exact ⟨final,addresses,whole,changed,recovered.stack.trans (bodyStack.trans captured.stack),
  extension,growth,cursor,older⟩

/-- Construct the frozen V3 producer using proved exact-input coverage and
actual checked execution. Approved-profile provenance remains external through
hprof; both outcome witnesses and the static alias condition stay explicit. -/
def make (selected : Composition.Program b F
 (.cons (.call f args (.val p r (some destination)) body) .nil))
 (lo pointer : Nat) (approved : InterfaceV3.Admission C Γ)
 (hprof : InterfaceV3.AdmissionAgreement approved (admitted selected lo pointer))
 (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag .refl)
 (successful : InterfaceV3.SuccessfulEntry b F (admitted selected lo pointer)
  (.call f args (.val p r (some destination)) body) (plan selected lo pointer))
 (reverting : InterfaceV3.RevertingEntry b F (admitted selected lo pointer)
  (.call f args (.val p r (some destination)) body) (plan selected lo pointer)) :
 InterfaceV3.PendingCallProducer b F approved (admitted selected lo pointer)
  f args (.val p r (some destination)) body where
 plan := plan selected lo pointer
 required_profile := hprof
 required_coverage := coverage selected lo pointer
 required_successful_entry := successful
 required_reverting_entry := reverting
 required_return := returns selected lo pointer flags
 required_bare_revert := bare_revert selected lo pointer

/-- Exact-plan packaging target for a producer with approved-domain agreement.
The make constructor supplies the underlying producer; provenance of approved
is not inferred from this type. -/
abbrev ProducerGoal (selected : Composition.Program b F
    (.cons (.call f args (.val p r (some destination)) body) .nil))
    (lo pointer : Nat) (approved : InterfaceV3.Admission C Γ) :=
 InterfaceV3.AdmissionAgreement approved (admitted selected lo pointer) →
 {producer : InterfaceV3.PendingCallProducer b F approved (admitted selected lo pointer)
   f args (.val p r (some destination)) body // producer.plan = plan selected lo pointer}

end Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducer
