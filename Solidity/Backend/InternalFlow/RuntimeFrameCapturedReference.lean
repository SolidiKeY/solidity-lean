import Solidity.Backend.InternalFlow.RuntimeFrameCapturedProgram
import Solidity.Backend.InternalFlow.RuntimeFrameReference

/-! Actual capture/body/restore followed by a typed reference export. The
returned identity comes from the reached representation, not an allocator
frontier. Changed heap contents remain changed; no world rollback is inferred. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.CapturedReference
open Evm Evm.Memory

/-- A restored header plus actual capture/body footprint preserves the older
runtime prefix, including the header if it lies inside that prefix. -/
theorem older_words {before saved after last : Machine} {cells : List Nat}
 {lo frame pointer start : Nat}
 (captured : Context.Captured before saved cells lo pointer start)
 (body : Footprint.Words lo frame saved after)
 (recovered : Context.Recovered before after last cells lo pointer start)
 (room : start ≤ frame) (cursor : before.mem pointer=.val (wmod start)) :
 Footprint.Words lo start before last := by
 intro x lower upper
 by_cases header : x=pointer
 · subst x
   exact recovered.cursor.trans cursor.symm
 · exact (recovered.exterior x lower header).trans
    ((body x lower (by omega)).trans (captured.exterior x header (.inl upper)))

/-- The result is exported AFTER the actual restore. Every target phase,
reached representation, allocation input and older-word fact is derived from
checked execution. Source caller-tail and fragment obligations remain visible. -/
theorem after_reference {C : Contract} {Γ Δ : Ctx} {R : RefTy}
 {L b frame : Nat} {F : Frag Γ} {P : Prog C Γ Δ}
 {σ : State C Γ} {base : Nat → Fin W} {before : Machine}
 (selected : Composition.Program b F P) (repr : StateRepr L b frame F σ base before)
 (lo pointer start : Nat) (localBound : b+Γ.length≤lo)
 (bodyBound : b+selected.checked.need≤lo) (resultBound : b+Δ.length≤lo)
 (pointerAbove : lo≤pointer) (pointerBelow : pointer<frame) (payloadAbove : lo≤start)
 (payloadBelow : start+Γ.length≤frame) (separate : pointer<start ∨ start+Γ.length≤pointer)
 (fits : start+Γ.length<W) (current : before.mem pointer=.val (wmod start))
 (capacity : AllocationInput b frame (selected.checked.cost σ) σ base before)
 (out : Solidity.Out C σ.H Δ) (source : P.run σ=.ok out)
 (scope : Ext Γ Δ) (environment : TEnv.drop scope out.st.env = TEnv.wk out.ext Γ σ.env)
 (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag scope)
 (destination : Idx Γ (.mem R)) (result : Idx Δ (.mem R)) :
 ∃ (saved after restored last : Machine) (addresses : Nat → Fin W) (reference : HRef out.st.H R),
 Evm.run (Restore.saveCells pointer (Restore.contextCells b Γ)) before=.ok saved 0 ∧
 Evm.run selected.checked.code saved=.ok after 0 ∧
 Evm.run (Restore.restoreCells pointer (Restore.contextCells b Γ)) after=.ok restored 0 ∧
 Evm.run ((Restore.saveCells pointer (Restore.contextCells b Γ) ++ selected.checked.code ++
   Restore.restoreCells pointer (Restore.contextCells b Γ)) ++ Reference.code b scope destination result)
   before=.ok last 0 ∧
 Context.Captured before saved (Restore.contextCells b Γ) lo pointer start ∧
 Context.Recovered before after restored (Restore.contextCells b Γ) lo pointer start ∧
 TEnv.get result out.st.env=some reference ∧
 restored.mem (cellOf b result)=.val (addresses reference.id) ∧
 last=writeMachine restored (cellOf b destination) (.val (addresses reference.id)) ∧
 StateRepr L b frame (selected.checked.frag.restrict Γ)
   ((out.st.setLocal (destination.ext scope) (TEnv.get result out.st.env)).drop scope) addresses last ∧
 last.stack=before.stack ∧ BaseExtends σ.H base addresses ∧
 GrowsAllocator b frame (selected.checked.cost σ) σ base before
   ((out.st.setLocal (destination.ext scope) (TEnv.get result out.st.env)).drop scope) addresses last ∧
 last.mem pointer=.val (wmod start) ∧ Footprint.Words lo start before last ∧
 (∀ {t : LTy} (index : Idx Γ t),cellOf b index≠cellOf b destination →
   last.mem (cellOf b index)=before.mem (cellOf b index)) := by
 obtain ⟨saved,after,restored,addresses,captureRun,bodyRun,restoreRun,whole,captured,
  recovered,bodyRepr,restoredRepr,extended,growth,stack,cursor,locals⟩ :=
  CapturedProgram.endpoint selected repr lo pointer start localBound bodyBound resultBound
   pointerAbove pointerBelow payloadAbove payloadBelow separate fits current capacity out source scope environment flags
 obtain ⟨actualSaved,actualRun,actualCaptured,savedRepr,captureGrowth⟩ :=
  Context.capture_context before lo pointer start repr localBound pointerAbove pointerBelow
   payloadAbove payloadBelow separate fits current
 have same : actualSaved=saved := (Evm.Out.ok.inj (actualRun.symm.trans captureRun)).1
 subst actualSaved
 have input : AllocationInput b frame (selected.checked.cost σ) σ base saved :=
  captureGrowth.nextInput (by simpa only [Nat.zero_add] using capacity)
 have bodyWords := selected.safe savedRepr bodyBound (by omega) input bodyRun
 have older := older_words captured bodyWords recovered (by omega) current
 obtain ⟨reference,value,word,exportRun,finalRepr⟩ := Reference.export_reference restoredRepr scope destination result
 have exportedGrowth := Reference.allocator restoredRepr scope destination result
 rw [word] at exportedGrowth
 have below : cellOf b destination<lo := Nat.lt_of_lt_of_le (lvl_lt b destination) localBound
 refine ⟨saved,after,restored,writeMachine restored (cellOf b destination) (.val (addresses reference.id)),
  addresses,reference,captureRun,bodyRun,restoreRun,?_,captured,recovered,value,word,rfl,finalRepr,stack,extended,?_,?_,?_,?_⟩
 · rw [Evm.run_append_ok whole]
   exact exportRun
 · simpa only [Nat.add_zero] using growth.comp exportedGrowth
 · change upd restored.mem (cellOf b destination) _ pointer = _
   rw [upd_other _ _ (by omega : pointer≠cellOf b destination)]
   exact cursor
 · intro x lower upper
   exact (Footprint.write_below (hi := frame) restored (cellOf b destination) (.val (addresses reference.id)) below
    x lower (by omega)).trans (older x lower upper)
 · intro t index different
   exact (upd_other _ _ different).trans (locals index)

/-- A real following caller program consumes the exported representation and
its reached allocator input. Its own derived scratch footprint preserves the
restored runtime cursor and older arena; logical caller writes remain allowed. -/
theorem then_program {C : Contract} {Γ Δ Ω : Ctx} {R : RefTy}
 {L b frame : Nat} {F : Frag Γ} {P : Prog C Γ Δ}
 {σ : State C Γ} {base : Nat → Fin W} {before : Machine}
 (selected : Composition.Program b F P) (repr : StateRepr L b frame F σ base before)
 (lo pointer start : Nat) (localBound : b+Γ.length≤lo)
 (bodyBound : b+selected.checked.need≤lo) (resultBound : b+Δ.length≤lo)
 (pointerAbove : lo≤pointer) (pointerBelow : pointer<frame) (payloadAbove : lo≤start)
 (payloadBelow : start+Γ.length≤frame) (separate : pointer<start ∨ start+Γ.length≤pointer)
 (fits : start+Γ.length<W) (current : before.mem pointer=.val (wmod start))
 (out : Solidity.Out C σ.H Δ) (source : P.run σ=.ok out)
 (scope : Ext Γ Δ) (environment : TEnv.drop scope out.st.env = TEnv.wk out.ext Γ σ.env)
 (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag scope)
 (destination : Idx Γ (.mem R)) (result : Idx Δ (.mem R))
 {tail : Prog C Γ Ω} (next : Composition.Program b (selected.checked.frag.restrict Γ) tail)
 (nextLo : Nat) (nextLower : nextLo≤lo) (nextBound : b+next.checked.need≤nextLo)
 (capacity : AllocationInput b frame (selected.checked.cost σ + next.checked.cost
   ((out.st.setLocal (destination.ext scope) (TEnv.get result out.st.env)).drop scope)) σ base before)
 (final : Solidity.Out C out.st.H Ω)
 (nextSource : tail.run ((out.st.setLocal (destination.ext scope) (TEnv.get result out.st.env)).drop scope)=.ok final) :
 ∃ (saved exported last : Machine) (firstBase addresses : Nat → Fin W) (reference : HRef out.st.H R),
 Evm.run (((Restore.saveCells pointer (Restore.contextCells b Γ) ++ selected.checked.code ++
   Restore.restoreCells pointer (Restore.contextCells b Γ)) ++ Reference.code b scope destination result) ++
   next.checked.code) before=.ok last 0 ∧
 StateRepr L b frame next.checked.frag final.st addresses last ∧
 last.stack=before.stack ∧ BaseExtends σ.H base addresses ∧
 GrowsAllocator b frame (selected.checked.cost σ + next.checked.cost
   ((out.st.setLocal (destination.ext scope) (TEnv.get result out.st.env)).drop scope))
   σ base before final.st addresses last ∧
 last.mem pointer=.val (wmod start) ∧ Footprint.Words lo start before last ∧
 Context.Captured before saved (Restore.contextCells b Γ) lo pointer start ∧
 BaseExtends σ.H base firstBase ∧ TEnv.get result out.st.env=some reference ∧
 (cellOf b result≠cellOf b destination → exported.mem (cellOf b result)=.val (firstBase reference.id)) ∧
 Footprint.Words nextLo frame exported last := by
 obtain ⟨saved,after,restored,exported,firstBase,reference,captureRun,bodyRun,restoreRun,
  whole,captured,recovered,value,resultWord,written,exportedRepr,stack,extended,growth,cursor,older,locals⟩ :=
  after_reference selected repr lo pointer start localBound bodyBound resultBound pointerAbove pointerBelow
   payloadAbove payloadBelow separate fits current (capacity.of_le (Nat.le_add_right _ _))
   out source scope environment flags destination result
 have input := growth.nextInput capacity
 rcases next.checked.sound exportedRepr (by omega) input with
  ⟨actual,last,addresses,actualSource,nextRun,finalRepr,nextStack,nextExtended,nextGrowth⟩ | ⟨failed,nextRun⟩
 · have same := Except.ok.inj (actualSource.symm.trans nextSource)
   subst actual
   have footprint := next.safe exportedRepr nextBound (by omega) input nextRun
   refine ⟨saved,exported,last,firstBase,addresses,reference,?_,finalRepr,nextStack.trans stack,
    extended.trans out.ext nextExtended,growth.comp nextGrowth,?_,?_,captured,extended,value,?_,footprint⟩
   · rw [Evm.run_append_ok whole]
     exact nextRun
   · exact (footprint pointer (by omega) pointerBelow).trans cursor
   · intro x lower upper
     exact (footprint x (by omega) (by omega)).trans (older x lower upper)
   · intro different
     rw [written]
     change upd restored.mem (cellOf b destination) _ (cellOf b result)=_
     rw [upd_other _ _ different]
     exact resultWord
 · rw [nextSource] at failed
   contradiction

end Solidity.Backend.InternalFlow.RuntimeFrame.CapturedReference
