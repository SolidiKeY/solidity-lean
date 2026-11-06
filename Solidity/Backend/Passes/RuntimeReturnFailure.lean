import Solidity.Backend.Passes.RuntimeReturnCapture

/-! A real primitive-returning runtime-frame call succeeds, but its reached
capture expression reverts. The successful machine/map precede every tail;
the receiving typed Input and actual failing value/capture runs are derived.
There is no post-failure state, map or public ABI/resource observation. -/
namespace Solidity.Backend.Passes.RuntimeReturnFailure
open Evm Evm.Memory
open Solidity.Backend.InternalFlow.RuntimeFrame

theorem capture_revert
    {C : Solidity.Contract} {Γ ps Γf : Solidity.Ctx} {b L frame : Nat} {F : Solidity.Evm.Frag Γ}
    {f : Solidity.Name} {args : Solidity.Args C Γ ps} {p q : Solidity.PrimTy} {r : Solidity.Var}
    {destination : Solidity.Idx Γ (.val p)} {body : Solidity.Prog C (.val p :: ps) Γf}
    (selected : Solidity.Backend.InternalFlow.RuntimeFrame.Composition.Program b F
      (.cons (.call f args (.val p r (some destination)) body) .nil))
    (lo pointer : Nat) (flags : Solidity.Backend.InternalFlow.RuntimeFrame.InterfaceV1.NoAliasPromotion F selected.checked.frag .refl)
    {caller : Solidity.State C Γ} {base : Nat → Fin Solidity.Evm.W} {machine : Solidity.Evm.Machine} {start : Nat}
    (member : Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducer.admitted selected lo pointer L frame caller base machine start)
    (out : Solidity.Out C caller.H Γ)
    (sourceCall : (Solidity.Stmt.call f args (.val p r (some destination)) body).run caller = .ok out)
    (name : Solidity.Var) (operand : Solidity.Val C Γ q)
    (given : Solidity.Evm.Memory.CompiledVal b selected.checked.frag operand)
    (evaluated : operand.evalT out.st = .error .revert)
    (room : b+(Γ.length+1) ≤ lo) :

    (Solidity.Prog.cons (.call f args (.val p r (some destination)) body)
      (.cons (.declLocal q name (some operand)) .nil)).run caller = .error .revert ∧
    ∃ (mid : Solidity.Evm.Machine) (addresses : Nat → Fin Solidity.Evm.W),
      Solidity.Evm.run (Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducer.plan selected lo pointer).code machine = .ok mid 0 ∧
      Solidity.Evm.Memory.StateRepr L b frame selected.checked.frag out.st addresses mid ∧
      mid.stack = machine.stack ∧
      Solidity.Evm.Memory.BaseExtends caller.H base addresses ∧
      Solidity.Evm.Memory.GrowsAllocator b frame
        ((Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducer.plan selected lo pointer).heapCost caller)
        caller base machine out.st addresses mid ∧
      mid.mem pointer = .val (Solidity.Evm.wmod start) ∧
      Solidity.Backend.InternalFlow.RuntimeFrame.Footprint.Words lo start machine mid ∧
      ∀ tail,
        (Solidity.Backend.Passes.CapturedValueStability.captureStage name operand given).Input
          L frame addresses out.st (Solidity.Backend.Passes.appendTail mid tail) ∧
        Solidity.Evm.run (Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducer.plan selected lo pointer).code
          (Solidity.Backend.Passes.appendTail machine tail) =
            .ok (Solidity.Backend.Passes.appendTail mid tail) 0 ∧
        Solidity.Evm.run given.code (Solidity.Backend.Passes.appendTail mid tail) = .revert ∧
        Solidity.Evm.run (Solidity.Backend.Passes.CapturedValueStability.captureStage name operand given).code
          (Solidity.Backend.Passes.appendTail mid tail) = .revert ∧
        Solidity.Evm.run ((Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducer.plan selected lo pointer).code ++
          (Solidity.Backend.Passes.CapturedValueStability.captureStage name operand given).code)
          (Solidity.Backend.Passes.appendTail machine tail) = .revert := by
  have entry := V3CallProducer.coverage selected lo pointer L frame caller base machine start member
  obtain ⟨mid,addresses,callRun,represented,stack,extension,growth,cursor,older⟩ :=
    V3CallProducer.returns selected lo pointer flags L frame caller base machine start
      entry out sourceCall
  have capacity : b+(Γ.length+1) ≤ frame := by
    have lower : lo ≤ pointer := entry.pointerAbove
    have upper : pointer < frame := entry.pointerBelow
    omega
  have suffixInput : (CapturedValueStability.captureStage name operand given).Input
      L frame addresses out.st mid := by
    refine ⟨represented,?_,Or.inl rfl⟩
    change b + max (max Γ.length (max (Γ.length+1) 0)) (Γ.length+1) ≤ frame
    omega
  have declaration : (Stmt.declLocal q name (some operand)).run out.st =
      .error .revert := by
    change TRun.declLocal q (some operand) out.st = _
    simp only [TRun.declLocal,evaluated,bind,Except.bind]
  constructor
  · rw [Prog.run_cons_ok sourceCall,Prog.run_cons_error declaration]
    rfl
  · refine ⟨mid,addresses,callRun,represented,stack,extension,growth,cursor,older,?_⟩
    intro tail
    have prefixTail := run_tail (V3CallProducer.plan selected lo pointer).code machine tail
      (by rw [callRun]; intro impossible; cases impossible)
    have prefixRun : run (V3CallProducer.plan selected lo pointer).code (appendTail machine tail) =
        .ok (appendTail mid tail) 0 := by
      simpa only [callRun,appendOut] using prefixTail
    have reachedInput := compilation_input_stack
      (CapturedValueStability.captureStage name operand given) suffixInput (mid.stack ++ tail)
    have failed : run given.code (appendTail mid tail) = .revert :=
      (value_revert_iff given represented (mid.stack ++ tail)).mpr evaluated
    have captureFailed :
        run (CapturedValueStability.captureStage name operand given).code (appendTail mid tail) = .revert := by
      change run ((given.code ++ [.mstore (cell (b+Γ.length))]) ++ []) _ = _
      exact run_append_revert (run_append_revert failed)
    refine ⟨reachedInput,prefixRun,failed,captureFailed,?_⟩
    rw [run_append_ok prefixRun]
    exact captureFailed

end Solidity.Backend.Passes.RuntimeReturnFailure

/-- info: 'Solidity.Backend.Passes.RuntimeReturnFailure.capture_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.RuntimeReturnFailure.capture_revert
