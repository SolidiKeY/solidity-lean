import Solidity.Evm.MemoryCompile

/-! Capture an actual initialized memory reference, then rebind its old local.
The old identity remains in the fresh local and physical cell for every saved
tail. No Source/world/function-reference lowering is asserted. -/
namespace Solidity.Backend.Passes.ReferenceCaptureStability
open Evm Evm.Memory
variable {C : Contract} {Γ : Ctx} {R : RefTy} {b L frame : Nat}
  {F : Frag Γ} {state : State C Γ} {base : Nat → Fin W} {machine : Machine}

theorem capture_rebind_readback
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+(Γ.length+1) ≤ frame)
    (dst src : Idx Γ (.mem R)) (mapFree : (Ty.ref R).mapFree = true) (name : Var) :
    ∃ captured rebound : HRef state.H R,
      TEnv.get dst state.env = some captured ∧ TEnv.get src state.env = some rebound ∧
      (Stmt.declMem R name (some (.alias (.var dst mapFree))) rfl mapFree).run state =
        .ok ⟨state.push (t := .mem R) (some captured),List.prefix_refl _⟩ ∧
      (Stmt.rebindMem (.there dst) (.alias (.var (.there src) mapFree))).run
        (state.push (t := .mem R) (some captured)) =
        .ok ⟨(state.push (t := .mem R) (some captured)).setLocal (.there dst) (some rebound),
          List.prefix_refl _⟩ ∧ ∀ tail,
      let cm := writeMachine {machine with stack := tail}
        (cell (b+Γ.length)) (.val (base captured.id))
      let em := writeMachine cm (cellOf b (.there (u := .mem R) dst)) (.val (base rebound.id))
      StateRepr L b frame (F.push (.mem R) .ok)
        ((state.push (t := .mem R) (some captured)).setLocal (.there dst) (some rebound)) base em ∧
      run (declareAliasCode b dst) {machine with stack := tail} = .ok cm 0 ∧
      run (aliasLocalCode b (.there (u := .mem R) dst) (.there (u := .mem R) src)) cm = .ok em 0 ∧
      run ((declareAliasCode b dst ++
        aliasLocalCode b (.there (u := .mem R) dst) (.there (u := .mem R) src)) ++
        [.mload (cell (b+Γ.length))]) {machine with stack := tail} =
        .ok (em.push (.val (base captured.id))) 0 := by
  obtain ⟨captured,hCaptured,capturedWord⟩ := represented.pointers dst
  obtain ⟨rebound,hRebound,reboundWord⟩ := represented.pointers src
  refine ⟨captured,rebound,hCaptured,hRebound,?_,?_,?_⟩
  · change TRun.declMem R (some (.alias (.var dst mapFree))) mapFree state = _
    simp only [TRun.declMem,MRhs.evalT,MPath.mvalT,hCaptured,bind,Except.bind,pure,Except.pure]
  · have oldSource : TEnv.get (.there (u := .mem R) src)
        (state.push (t := .mem R) (some captured)).env = some rebound := hRebound
    change TRun.rebindMem (.there dst) (.alias (.var (.there src) mapFree))
      (state.push (t := .mem R) (some captured)) = _
    simp only [TRun.rebindMem,MRhs.evalT,MPath.mvalT,oldSource,bind,Except.bind,pure,Except.pure]
  · intro tail
    let cm := writeMachine {machine with stack := tail}
      (cell (b+Γ.length)) (.val (base captured.id))
    let em := writeMachine cm (cellOf b (.there (u := .mem R) dst)) (.val (base rebound.id))
    have capturedRep := (represented.stack tail).consMem captured capacity
    have reached := capturedRep.setMem (.there dst) rebound
    have secondWord : cm.mem (cellOf b (.there (u := .mem R) src)) = .val (base rebound.id) := by
      change upd machine.mem (b+Γ.length) (.val (base captured.id)) (lvl b (.there src)) = _
      rw [lvl_there,upd_other _ _ (Nat.ne_of_lt (lvl_lt b src))]
      exact reboundWord
    have captureRun : run (declareAliasCode b dst) {machine with stack := tail} = .ok cm 0 := by
      simp only [declareAliasCode,run,exec_cons_zero,Instr.step,Machine.next,
        Out.ok_bind,capturedWord,exec_nil,writeMachine,cm]
    have rebindRun : run (aliasLocalCode b (.there (u := .mem R) dst)
        (.there (u := .mem R) src)) cm = .ok em 0 := by
      simp only [aliasLocalCode,run,exec_cons_zero,Instr.step,Machine.next,
        Out.ok_bind,secondWord,exec_nil,writeMachine,em]
    refine ⟨reached,captureRun,rebindRun,?_⟩
    rw [List.append_assoc,run_append_ok captureRun,run_append_ok rebindRun]
    have separate : cellOf b (.there (u := .mem R) dst) ≠ cell (b+Γ.length) := by
      simpa only [cellOf,lvl_there,cell] using Nat.ne_of_lt (lvl_lt b dst)
    have read : em.mem (cell (b+Γ.length)) = .val (base captured.id) :=
      (upd_other _ _ separate.symm).trans (upd_same _ _ _)
    change Evm.Out.ok (em.push (em.mem (cell (b+Γ.length)))) 0 = _
    rw [read]

end Solidity.Backend.Passes.ReferenceCaptureStability
/-- info: 'Solidity.Backend.Passes.ReferenceCaptureStability.capture_rebind_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReferenceCaptureStability.capture_rebind_readback
