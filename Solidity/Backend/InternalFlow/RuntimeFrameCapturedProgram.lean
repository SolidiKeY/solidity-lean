import Solidity.Backend.InternalFlow.RuntimeFrameRestoredRepresentation

/-! Compose actual capture, a checked framed body, and actual restoration into
full reached representation. The source caller-tail and alias-flag agreement
remain explicit; no world history or unbounded return dispatch is inferred. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.CapturedProgram
open Evm Evm.Memory

/-- Target runs, payload, reached representation and allocator growth are
outputs of existing checked execution. Only actual SOURCE caller agreement
and fragment compatibility are extra premises of restored representation. -/
theorem endpoint {C : Contract} {Γ Δ : Ctx} {L b frame : Nat} {F : Frag Γ}
 {P : Prog C Γ Δ} {σ : State C Γ} {base : Nat → Fin W} {before : Machine}
 (selected : Composition.Program b F P) (repr : StateRepr L b frame F σ base before)
 (lo pointer start : Nat) (localBound : b+Γ.length≤lo)
 (bodyBound : b+selected.checked.need≤lo) (resultBound : b+Δ.length≤lo)
 (pointerAbove : lo≤pointer) (pointerBelow : pointer<frame) (payloadAbove : lo≤start)
 (payloadBelow : start+Γ.length≤frame) (separate : pointer<start ∨ start+Γ.length≤pointer)
 (fits : start+Γ.length<W) (current : before.mem pointer=.val (wmod start))
 (capacity : AllocationInput b frame (selected.checked.cost σ) σ base before)
 (out : Solidity.Out C σ.H Δ) (source : P.run σ=.ok out)
 (scope : Ext Γ Δ)
 (environment : TEnv.drop scope out.st.env = TEnv.wk out.ext Γ σ.env)
 (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag scope) :
 ∃ saved after last addresses,
 Evm.run (Restore.saveCells pointer (Restore.contextCells b Γ)) before=.ok saved 0 ∧
 Evm.run selected.checked.code saved=.ok after 0 ∧
 Evm.run (Restore.restoreCells pointer (Restore.contextCells b Γ)) after=.ok last 0 ∧
 Evm.run (Restore.saveCells pointer (Restore.contextCells b Γ) ++ selected.checked.code ++
   Restore.restoreCells pointer (Restore.contextCells b Γ)) before=.ok last 0 ∧
 Context.Captured before saved (Restore.contextCells b Γ) lo pointer start ∧
 Context.Recovered before after last (Restore.contextCells b Γ) lo pointer start ∧
 StateRepr L b frame selected.checked.frag out.st addresses after ∧
 StateRepr L b frame selected.checked.frag out.st addresses last ∧
 BaseExtends σ.H base addresses ∧
 GrowsAllocator b frame (selected.checked.cost σ) σ base before out.st addresses last ∧
 last.stack=before.stack ∧ last.mem pointer=.val (wmod start) ∧
 (∀ {t : LTy} (index : Idx Γ t),last.mem (cellOf b index)=before.mem (cellOf b index)) := by
 obtain ⟨saved,after,last,addresses,captureRun,bodyRun,restoreRun,whole,captured,
  bodyRepr,recovered,extension,growth,stack,locals⟩ :=
  Context.program selected repr lo pointer start localBound bodyBound pointerAbove pointerBelow
   payloadAbove payloadBelow separate fits current capacity out source
 have finalRepr := Restored.restored_representation (caller := σ) (afterSource := out.st)
  scope out.ext repr bodyRepr environment extension flags resultBound pointerAbove pointerBelow
  (by omega) recovered
 exact ⟨saved,after,last,addresses,captureRun,bodyRun,restoreRun,whole,captured,recovered,
  bodyRepr,finalRepr,extension,growth,stack,recovered.cursor,locals⟩
/-- A checked bare body failure after real capture absorbs restore and any
following code. No final State, unwind execution or rollback is inferred. -/
theorem bare_revert {C : Contract} {Γ Δ : Ctx} {L b frame : Nat} {F : Frag Γ}
 {P : Prog C Γ Δ} {σ : State C Γ} {base : Nat → Fin W} {before : Machine}
 (selected : Composition.Program b F P) (repr : StateRepr L b frame F σ base before)
 (lo pointer start : Nat) (localBound : b+Γ.length≤lo)
 (bodyBound : b+selected.checked.need≤lo)
 (pointerAbove : lo≤pointer) (pointerBelow : pointer<frame) (payloadAbove : lo≤start)
 (payloadBelow : start+Γ.length≤frame) (separate : pointer<start ∨ start+Γ.length≤pointer)
 (fits : start+Γ.length<W) (current : before.mem pointer=.val (wmod start))
 (capacity : AllocationInput b frame (selected.checked.cost σ) σ base before)
 (source : P.run σ=.error .revert) (suffix : List Instr) :
 ∃ saved,
 Evm.run (Restore.saveCells pointer (Restore.contextCells b Γ)) before=.ok saved 0 ∧
 Context.Captured before saved (Restore.contextCells b Γ) lo pointer start ∧
 Evm.run selected.checked.code saved=.revert ∧
 Evm.run (Restore.saveCells pointer (Restore.contextCells b Γ) ++
   selected.checked.code ++ suffix) before=.revert := by
 obtain ⟨saved,captureRun,captured,savedRepr,captureGrowth⟩ :=
  Context.capture_context before lo pointer start repr localBound pointerAbove pointerBelow
   payloadAbove payloadBelow separate fits current
 have input : AllocationInput b frame (selected.checked.cost σ) σ base saved :=
  captureGrowth.nextInput (by simpa only [Nat.zero_add] using capacity)
 have failed : Evm.run selected.checked.code saved=.revert := by
  rcases selected.checked.sound savedRepr (by omega) input with
   ⟨out,target,addresses,actual,code,represented,stack,extension,growth⟩ | ⟨actual,code⟩
  · rw [source] at actual
    contradiction
  · exact code
 refine ⟨saved,captureRun,captured,failed,?_⟩
 rw [List.append_assoc,Evm.run_append_ok captureRun]
 exact Evm.run_append_revert failed

end Solidity.Backend.InternalFlow.RuntimeFrame.CapturedProgram
