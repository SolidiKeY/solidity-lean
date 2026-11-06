import Solidity.Backend.Passes.ReferenceCallArgumentFailure
import Solidity.Backend.InternalFlow.RuntimeFrameContext

/-! Actual private save and first-argument failure before any return allocation.
The successful runtime branch uses the very same emitted checked program. -/
namespace Solidity.Backend.Passes.ReferenceCallArgumentFailure
open Evm Evm.Memory Evm.Compiler
open Solidity.Backend.InternalFlow.RuntimeFrame
open V3CallProducerRef.Tuple.Controls (C A Γ F rs binders body)

def saveCode := Restore.saveCells 16 (Restore.contextCells 1 Γ)
private def successMachine : Evm.Out → Option Machine
  | .ok m 0 => some m | _ => none
@[irreducible] def saved : Machine := (successMachine (run saveCode machine)).get (by decide +kernel)
theorem save_run : run saveCode machine = .ok saved 0 := by
  have h : some saved = successMachine (run saveCode machine) := by unfold saved;exact Option.some_get _
  generalize run saveCode machine = result at h ⊢
  cases result with
  | ok m skip => cases skip with
    | zero => exact congrArg (fun m => Evm.Out.ok m 0) (Option.some.inj h).symm
    | succ n => cases h
  | revert => cases h
  | fault => cases h

theorem saved_evidence :
    Context.Captured machine saved (Restore.contextCells 1 Γ) 16 16 20 ∧
    StateRepr 1 1 64 F caller base saved ∧
    GrowsAllocator 1 64 0 caller base machine caller base saved := by
  obtain ⟨actual,run,captured,repr,growth⟩ := Context.capture_context machine 16 16 20
    (V3CallProducerRef.ArrayControls.initial (wmod 2)).1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) rfl
  have same : actual = saved := (Evm.Out.ok.inj (run.symm.trans save_run)).1
  subst actual
  exact ⟨captured,repr,growth⟩

theorem early_revert (suffix : List Instr) (tail : List Word) :
    run ((saveCode ++ first.code) ++ suffix) (appendTail machine tail) = .revert := by
  have prefixRun : run saveCode (appendTail machine tail) = .ok (appendTail saved tail) 0 := by
    simpa only [save_run,appendOut] using run_tail saveCode machine tail
      (by rw [save_run];intro impossible;cases impossible)
  have failed : run first.code (appendTail saved tail) = .revert :=
    (value_revert_iff first saved_evidence.2.1 (saved.stack ++ tail)).mpr argument_revert
  rw [List.append_assoc,run_append_ok prefixRun]
  exact run_append_revert failed

def prefixCells : List Nat := [0,1,2,3,4,5,16,20,21,22,63,128,129,130]
theorem prefix_observations (tail : List Word) :
    (prefixCells.map (appendTail saved tail).mem,(appendTail saved tail).stack) =
      ([w[130],w[128],w[2],w[0],w[0],w[0],w[22],w[128],w[2],w[0],w[99],w[1],w[0],w[0]],
        w[77] :: tail) := by
  apply Prod.ext
  · change prefixCells.map saved.mem =
      [w[130],w[128],w[2],w[0],w[0],w[0],w[22],w[128],w[2],w[0],w[99],w[1],w[0],w[0]]
    unfold prefixCells saved
    decide +kernel
  · have same : saved.stack = machine.stack := saved_evidence.1.stack
    change saved.stack ++ tail = _
    rw [same]
    rfl

def goodVector : Option (List Nat) := do
  let returned ← goodOutput.st.env.2.1
  let old ← goodOutput.st.env.2.2.2.1
  pure [goodOutput.st.env.1.val.toNat,returned.id,goodOutput.st.env.2.2.1.val.toNat,
    old.id,goodOutput.st.H.length,goodOutput.st.heap.len returned .dyn]
theorem positive_source_observations : goodVector = some [7,0,0,0,2,1] := by
  unfold goodVector goodOutput
  decide +kernel

theorem not_always_revert : ∃ target,
    run (V3CallProducerRef.plan selected 16 16).code goodMachine = .ok target 0 := by
  obtain ⟨target,_,run,_⟩ := successful_return
  exact ⟨target,run⟩

end Solidity.Backend.Passes.ReferenceCallArgumentFailure
