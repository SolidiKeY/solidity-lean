import Solidity.Backend.Passes.ReferenceCallReadback

/-! Exact reached ordinary-revert transport after a real memory/tuple call.
The returned map precedes every saved tail; no post-failure state is supplied. -/
namespace Solidity.Backend.Passes.ReferenceCallReadback
open Evm Evm.Memory Evm.Compiler
open Solidity.Backend.InternalFlow.RuntimeFrame
variable {C : Contract} {Γ Δ ps rs Γf : Ctx} {b L frame : Nat} {F : Frag Γ}
  {f : Name} {args : Args C Γ ps} {ret : CallRet Γ rs Δ}
  {body : Prog C (rs ++ ps) Γf} {scope : Ext Γ Δ}

theorem source_capture_revert {caller : State C Γ} (out : Solidity.Out C caller.H Δ)
    (sourceCall : (Stmt.call f args ret body).run caller = .ok out)
    {p : PrimTy} (name : Var) (e : Val C Δ p)
    (failed : e.evalT out.st = .error .revert) :
    (Prog.cons (.call f args ret body) (.cons (.declLocal p name (some e)) .nil)).run caller =
      .error .revert := by
  have declaration : (Stmt.declLocal p name (some e)).run out.st = .error .revert := by
    change TRun.declLocal p (some e) out.st = _
    simp only [TRun.declLocal,failed,bind,Except.bind]
  rw [Prog.run_cons_ok sourceCall,Prog.run_cons_error declaration]
  rfl

theorem capture_revert_iff (form : V3CallProducerRef.Form Γ ret scope)
    (selected : Composition.Program b F (.cons (.call f args ret body) .nil))
    (lo pointer : Nat) (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag scope)
    {caller : State C Γ} {base : Nat → Fin W} {machine : Machine} {start : Nat}
    (entry : InterfaceV1.Entry (V3CallProducerRef.plan selected lo pointer) L b frame F caller base machine start)
    (out : Solidity.Out C caller.H Δ) (sourceCall : (Stmt.call f args ret body).run caller = .ok out)
    {p : PrimTy} (name : Var) (e : Val C Δ p) (cc : CompiledVal b selected.checked.frag e)
    (room : b+(Δ.length+1) ≤ lo) :
    ∃ (returned : Machine) (addresses : Nat → Fin W),
      run (V3CallProducerRef.plan selected lo pointer).code machine = .ok returned 0 ∧
      StateRepr L b frame selected.checked.frag out.st addresses returned ∧
      returned.stack = machine.stack ∧ BaseExtends caller.H base addresses ∧
      GrowsAllocator b frame (selected.checked.cost caller) caller base machine out.st addresses returned ∧
      returned.mem pointer = .val (wmod start) ∧ Footprint.Words lo start machine returned ∧
      ∀ tail,
        (CapturedValueStability.captureStage name e cc).Input L frame addresses out.st (appendTail returned tail) ∧
        run (V3CallProducerRef.plan selected lo pointer).code (appendTail machine tail) =
          .ok (appendTail returned tail) 0 ∧
        (run ((V3CallProducerRef.plan selected lo pointer).code ++
          (CapturedValueStability.captureStage name e cc).code) (appendTail machine tail) = .revert ↔
          e.evalT out.st = .error .revert) := by
  have capacity : b+(Δ.length+1) ≤ frame := by
    have lower : lo ≤ pointer := entry.pointerAbove
    have upper : pointer < frame := entry.pointerBelow
    omega
  obtain ⟨returned,addresses,hcall,represented,stack,extension,growth,cursor,words⟩ :=
    V3CallProducerRef.returns form selected lo pointer flags L frame caller base machine start entry out sourceCall
  have input : (CapturedValueStability.captureStage name e cc).Input L frame addresses out.st returned := by
    refine ⟨represented,?_,Or.inl rfl⟩
    change b+max (max Δ.length (max (Δ.length+1) 0)) (Δ.length+1) ≤ frame
    omega
  refine ⟨returned,addresses,hcall,represented,stack,extension,growth,cursor,words,?_⟩
  intro tail
  have transported : run (V3CallProducerRef.plan selected lo pointer).code (appendTail machine tail) =
      .ok (appendTail returned tail) 0 := by
    simpa only [hcall,appendOut] using run_tail (V3CallProducerRef.plan selected lo pointer).code
      machine tail (by rw [hcall]; intro impossible; cases impossible)
  refine ⟨⟨represented.stack (returned.stack ++ tail),input.2.1,Or.inl rfl⟩,transported,?_⟩
  rw [run_append_ok transported]
  exact capture_stage_revert_iff name e cc input tail

end Solidity.Backend.Passes.ReferenceCallReadback
