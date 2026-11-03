import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducer
import Solidity.Backend.Passes.CapturedValueStability

/-! Consume the actual P1 primitive-return emitter with a typed value capture.
The physical admission predicate and alias guard remain explicit. This is an
internal word-machine result, not an approved source-profile or ABI theorem.
The actual intermediate machine and selected map precede all appended tails. -/
namespace Solidity.Backend.Passes.RuntimeReturnCapture
open Evm Evm.Memory
open Solidity.Backend.InternalFlow.RuntimeFrame

theorem capture
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
    (value : q.Denote) (evaluated : operand.evalT out.st = .ok value)
    (room : b+(Γ.length+1) ≤ lo) :
    (Solidity.Prog.cons (.call f args (.val p r (some destination)) body)
      (.cons (.declLocal q name (some operand)) .nil)).run caller =
        .ok ⟨out.st.push (t := .val q) value,out.ext⟩ ∧
    ∃ (mid : Solidity.Evm.Machine) (addresses : Nat → Fin Solidity.Evm.W) (word : Solidity.Evm.Word) (final : Solidity.Evm.Machine),
      Solidity.Evm.ReprV q value word ∧
      Solidity.Evm.run (Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducer.plan selected lo pointer).code machine = .ok mid 0 ∧
      Solidity.Evm.Memory.StateRepr L b frame selected.checked.frag out.st addresses mid ∧
      mid.stack = machine.stack ∧
      Solidity.Evm.Memory.BaseExtends caller.H base addresses ∧
      Solidity.Evm.Memory.GrowsAllocator b frame ((Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducer.plan selected lo pointer).heapCost caller)
        caller base machine out.st addresses mid ∧
      mid.mem pointer = .val (Solidity.Evm.wmod start) ∧
      Solidity.Backend.InternalFlow.RuntimeFrame.Footprint.Words lo start machine mid ∧
      (Solidity.Backend.Passes.CapturedValueStability.captureStage name operand given).Input
        L frame addresses out.st mid ∧
      Solidity.Backend.Passes.MappedOutput (Solidity.Backend.Passes.CapturedValueStability.captureStage name operand given) L frame
        addresses out.st mid (out.st.push (t := .val q) value) final addresses ∧
      Solidity.Evm.run (Solidity.Backend.Passes.CapturedValueStability.captureStage name operand given).code mid = .ok final 0 ∧
      Solidity.Evm.run ((Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducer.plan selected lo pointer).code ++
        (Solidity.Backend.Passes.CapturedValueStability.captureStage name operand given).code) machine = .ok final 0 ∧
      final.stack = machine.stack ∧
      final.mem pointer = .val (Solidity.Evm.wmod start) ∧
      Solidity.Backend.InternalFlow.RuntimeFrame.Footprint.Words lo start machine final ∧
      Solidity.Evm.Memory.GrowsAllocator b frame ((Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducer.plan selected lo pointer).heapCost caller)
        caller base machine (out.st.push (t := .val q) value) addresses final ∧
      ∀ tail, Solidity.Evm.run ((Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducer.plan selected lo pointer).code ++
        (Solidity.Backend.Passes.CapturedValueStability.captureStage name operand given).code) (Solidity.Backend.Passes.appendTail machine tail) =
        .ok (Solidity.Backend.Passes.appendTail final tail) 0 := by
  obtain ⟨mid,addresses,callRun,represented,stack,extension,growth,cursor,older⟩ :=
    V3CallProducer.returns selected lo pointer flags L frame caller base machine start
      (V3CallProducer.coverage selected lo pointer L frame caller base machine start member)
      out sourceCall
  have entry := V3CallProducer.coverage selected lo pointer L frame caller base machine start member
  have capacity : b+(Γ.length+1) ≤ frame := by
    have lower : lo ≤ pointer := entry.pointerAbove
    have upper : pointer < frame := entry.pointerBelow
    omega
  have declaration : (Stmt.declLocal q name (some operand)).run out.st =
      .ok ⟨out.st.push (t := .val q) value,List.prefix_refl _⟩ := by
    change TRun.declLocal q (some operand) out.st = _
    simp only [TRun.declLocal,evaluated,bind,Except.bind,pure,Except.pure]
  constructor
  · rw [Prog.run_cons_ok sourceCall,Prog.run_cons_ok declaration]
    rfl
  · obtain ⟨word,repr,valueRun⟩ := value_success_tail given represented evaluated mid.stack
    have actualValue : run given.code mid = .ok (mid.push word) 0 := by
      simpa only using valueRun
    let final := writeMachine mid (cell (b+Γ.length)) word
    have captureRun : run (CapturedValueStability.captureStage name operand given).code mid =
        .ok final 0 := by
      change run ((given.code ++ [.mstore (cell (b+Γ.length))]) ++ []) mid = _
      rw [List.append_nil,run_append_ok actualValue]
      rfl
    have joined : run ((V3CallProducer.plan selected lo pointer).code ++
        (CapturedValueStability.captureStage name operand given).code) machine = .ok final 0 := by
      rw [run_append_ok callRun]
      exact captureRun
    have freshBelow : cell (b+Γ.length) < lo := by
      change b+Γ.length < lo
      omega
    have freshFrame : cell (b+Γ.length) < frame := by
      change b+Γ.length < frame
      omega
    have preservedCursor : final.mem pointer = .val (wmod start) := by
      change upd mid.mem (cell (b+Γ.length)) word pointer = _
      rw [upd_other _ _ (by have h : lo ≤ pointer := entry.pointerAbove; omega)]
      exact cursor
    have suffixInput : (CapturedValueStability.captureStage name operand given).Input
        L frame addresses out.st mid := by
      refine ⟨represented,?_,Or.inl rfl⟩
      change b + max (max Γ.length (max (Γ.length+1) 0)) (Γ.length+1) ≤ frame
      omega
    have mapped : MappedOutput (CapturedValueStability.captureStage name operand given)
        L frame addresses out.st mid (out.st.push (t := .val q) value) final addresses := by
      refine ⟨represented.consVal value word repr capacity,BaseExtends.refl addresses,?_⟩
      intro free positive allocator space
      exact allocator.localWrite (b+Γ.length) (by omega) freshFrame word
    have total : GrowsAllocator b frame ((V3CallProducer.plan selected lo pointer).heapCost caller)
        caller base machine (out.st.push (t := .val q) value) addresses final := by
      intro free positive allocator space
      exact (growth free positive allocator space).localWrite (b+Γ.length) (by omega) freshFrame word
    refine ⟨mid,addresses,word,final,repr,callRun,represented,stack,extension,growth,cursor,
      older,suffixInput,mapped,captureRun,joined,stack,preservedCursor,
      Footprint.words_trans older (Footprint.write_below mid _ word freshBelow),total,?_⟩
    intro tail
    have actual := run_tail ((V3CallProducer.plan selected lo pointer).code ++
      (CapturedValueStability.captureStage name operand given).code) machine tail
      (by rw [joined]; intro impossible; cases impossible)
    simpa only [joined,appendOut] using actual

end Solidity.Backend.Passes.RuntimeReturnCapture

/-- info: 'Solidity.Backend.Passes.RuntimeReturnCapture.capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.RuntimeReturnCapture.capture
