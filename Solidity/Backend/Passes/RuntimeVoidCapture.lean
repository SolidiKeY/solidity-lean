import Solidity.Backend.InternalFlow.RuntimeFrameNoneProducer
import Solidity.Backend.Passes.CapturedValueStability
import Solidity.Backend.Passes.MappedTail

/-! A checked void call may mutate the reached heap without returning a
primitive. Capture reads that actual reached heap under its selected map.
Original Entry, alias, allocation and frame premises remain explicit; no
approved source-profile or public session adequacy is inferred. -/
namespace Solidity.Backend.Passes.RuntimeVoidCapture
open Evm Evm.Memory
open Solidity.Backend.InternalFlow.RuntimeFrame

theorem capture
    {C : Solidity.Contract} {Γ ps Γf : Solidity.Ctx} {b L frame : Nat} {F : Solidity.Evm.Frag Γ}
    {f : Solidity.Name} {args : Solidity.Args C Γ ps} {q : Solidity.PrimTy} {body : Solidity.Prog C ps Γf}
    (selected : Solidity.Backend.InternalFlow.RuntimeFrame.Composition.Program b F
      (.cons (.call f args .none body) .nil))
    (lo pointer : Nat) (flags : Solidity.Backend.InternalFlow.RuntimeFrame.InterfaceV1.NoAliasPromotion F selected.checked.frag .refl)
    {caller : Solidity.State C Γ} {base : Nat → Fin Solidity.Evm.W} {machine : Solidity.Evm.Machine} {start : Nat}
    (entry : Solidity.Backend.InternalFlow.RuntimeFrame.InterfaceV1.Entry
      (Solidity.Backend.InternalFlow.RuntimeFrame.NoneProducer.plan selected lo pointer) L b frame F caller base machine start)
    (out : Solidity.Out C caller.H Γ)
    (sourceCall : (Solidity.Stmt.call f args .none body).run caller = .ok out)
    (name : Solidity.Var) (operand : Solidity.Val C Γ q)
    (given : Solidity.Evm.Memory.CompiledVal b selected.checked.frag operand)
    (value : q.Denote) (evaluated : operand.evalT out.st = .ok value)
    (room : b+(Γ.length+1) ≤ lo) :
    (Solidity.Prog.cons (.call f args .none body)
      (.cons (.declLocal q name (some operand)) .nil)).run caller =
        .ok ⟨out.st.push (t := .val q) value,out.ext⟩ ∧
    ∃ (mid : Solidity.Evm.Machine) (addresses : Nat → Fin Solidity.Evm.W) (word : Solidity.Evm.Word) (final : Solidity.Evm.Machine),
      Solidity.Evm.ReprV q value word ∧
      Solidity.Evm.run (Solidity.Backend.InternalFlow.RuntimeFrame.NoneProducer.plan selected lo pointer).code machine = .ok mid 0 ∧
      Solidity.Evm.Memory.StateRepr L b frame selected.checked.frag out.st addresses mid ∧
      mid.stack = machine.stack ∧
      Solidity.Evm.Memory.BaseExtends caller.H base addresses ∧
      Solidity.Evm.Memory.GrowsAllocator b frame ((Solidity.Backend.InternalFlow.RuntimeFrame.NoneProducer.plan selected lo pointer).heapCost caller)
        caller base machine out.st addresses mid ∧
      mid.mem pointer = .val (Solidity.Evm.wmod start) ∧
      Solidity.Backend.InternalFlow.RuntimeFrame.Footprint.Words lo start machine mid ∧
      (Solidity.Backend.Passes.CapturedValueStability.captureStage name operand given).Input
        L frame addresses out.st mid ∧
      Solidity.Backend.Passes.MappedOutput (Solidity.Backend.Passes.CapturedValueStability.captureStage name operand given) L frame
        addresses out.st mid (out.st.push (t := .val q) value) final addresses ∧
      Solidity.Evm.run (Solidity.Backend.Passes.CapturedValueStability.captureStage name operand given).code mid = .ok final 0 ∧
      Solidity.Evm.run ((Solidity.Backend.InternalFlow.RuntimeFrame.NoneProducer.plan selected lo pointer).code ++
        (Solidity.Backend.Passes.CapturedValueStability.captureStage name operand given).code) machine = .ok final 0 ∧
      final.stack = machine.stack ∧
      final.mem pointer = .val (Solidity.Evm.wmod start) ∧
      Solidity.Backend.InternalFlow.RuntimeFrame.Footprint.Words lo start machine final ∧
      Solidity.Evm.Memory.GrowsAllocator b frame ((Solidity.Backend.InternalFlow.RuntimeFrame.NoneProducer.plan selected lo pointer).heapCost caller)
        caller base machine (out.st.push (t := .val q) value) addresses final ∧
      ∀ tail,
        Solidity.Evm.run (Solidity.Backend.InternalFlow.RuntimeFrame.NoneProducer.plan selected lo pointer).code (Solidity.Backend.Passes.appendTail machine tail) = .ok (Solidity.Backend.Passes.appendTail mid tail) 0 ∧
        (Solidity.Backend.Passes.CapturedValueStability.captureStage name operand given).Input L frame addresses out.st (Solidity.Backend.Passes.appendTail mid tail) ∧
        Solidity.Backend.Passes.MappedOutput (Solidity.Backend.Passes.CapturedValueStability.captureStage name operand given) L frame addresses out.st
          (Solidity.Backend.Passes.appendTail mid tail) (out.st.push (t := .val q) value) (Solidity.Backend.Passes.appendTail final tail) addresses ∧
        Solidity.Evm.run (Solidity.Backend.Passes.CapturedValueStability.captureStage name operand given).code (Solidity.Backend.Passes.appendTail mid tail) = .ok (Solidity.Backend.Passes.appendTail final tail) 0 ∧
        Solidity.Evm.run ((Solidity.Backend.InternalFlow.RuntimeFrame.NoneProducer.plan selected lo pointer).code ++ (Solidity.Backend.Passes.CapturedValueStability.captureStage name operand given).code) (Solidity.Backend.Passes.appendTail machine tail) =
          .ok (Solidity.Backend.Passes.appendTail final tail) 0 := by
  obtain ⟨mid,addresses,callRun,represented,stack,extension,growth,cursor,older⟩ :=
    NoneProducer.returns selected lo pointer flags L frame caller base machine start
      entry out sourceCall
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
    have joined : run ((NoneProducer.plan selected lo pointer).code ++
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
    have total : GrowsAllocator b frame ((NoneProducer.plan selected lo pointer).heapCost caller)
        caller base machine (out.st.push (t := .val q) value) addresses final := by
      intro free positive allocator space
      exact (growth free positive allocator space).localWrite (b+Γ.length) (by omega) freshFrame word
    refine ⟨mid,addresses,word,final,repr,callRun,represented,stack,extension,growth,cursor,
      older,suffixInput,mapped,captureRun,joined,stack,preservedCursor,
      Footprint.words_trans older (Footprint.write_below mid _ word freshBelow),total,?_⟩
    intro tail
    have transport (code : List Instr) (before after : Machine)
        (actual : run code before = .ok after 0) :
        run code (appendTail before tail) = .ok (appendTail after tail) 0 := by
      have stable := run_tail code before tail
        (by rw [actual]; intro impossible; cases impossible)
      simpa only [actual,appendOut] using stable
    exact ⟨transport _ _ _ callRun,
      compilation_input_stack _ suffixInput (mid.stack ++ tail),
      mapped_output_stack _ mapped (mid.stack ++ tail) (final.stack ++ tail),
      transport _ _ _ captureRun,transport _ _ _ joined⟩

end Solidity.Backend.Passes.RuntimeVoidCapture
