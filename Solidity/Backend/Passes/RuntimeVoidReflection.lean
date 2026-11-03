import Solidity.Backend.InternalFlow.RuntimeFrameNoneProducer
import Solidity.Evm.MemoryLoopScopeSound
import Solidity.Backend.Passes.TailLoop

/-! Exact internal terminal reflection for the actual checked void-call
emission. Context capture is a real successful prefix, including transported
heap ownership, frame and allocator input. This is not public ABI/session or
unbounded-call adequacy; the selected finite certificate is essential. -/
namespace Solidity.Backend.Passes.RuntimeVoidReflection
open Evm Evm.Memory
open Solidity.Backend.InternalFlow.RuntimeFrame

theorem terminal_exact
    {C : Contract} {Γ ps Γf : Ctx} {b L frame : Nat} {F : Frag Γ}
    {f : Name} {args : Args C Γ ps} {body : Prog C ps Γf}
    (selected : Composition.Program b F (.cons (.call f args .none body) .nil))
    (lo pointer : Nat) (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag .refl)
    {caller : State C Γ} {base : Nat → Fin W} {machine : Machine} {start : Nat}
    (entry : InterfaceV1.Entry (NoneProducer.plan selected lo pointer)
      L b frame F caller base machine start) :
    ∃ saved,
      run (Restore.saveCells pointer (Restore.contextCells b Γ)) machine = .ok saved 0 ∧
      Context.Captured machine saved (Restore.contextCells b Γ) lo pointer start ∧
      StateRepr L b frame F caller base saved ∧
      b + selected.checked.need ≤ frame ∧
      AllocationInput b frame (selected.checked.cost caller) caller base saved ∧
      ((∃ out, (.call f args .none body : Stmt C Γ Γ).run caller = .ok out ∧
          InterfaceV1.Returned (NoneProducer.plan selected lo pointer)
            L b frame caller base machine start out) ∨
        ((.call f args .none body : Stmt C Γ Γ).run caller = .error .revert ∧
          run selected.checked.code saved = .revert ∧
          run (NoneProducer.plan selected lo pointer).code machine = .revert)) := by
  obtain ⟨reserve,separate,fits⟩ := NoneProducer.arena_bounds entry
  obtain ⟨saved,captureRun,captured,represented,growth⟩ :=
    Context.capture_context machine lo pointer start entry.represented entry.callerBound
      entry.pointerAbove entry.pointerBelow entry.payloadAbove reserve separate fits entry.cursor
  have capacity : AllocationInput b frame (selected.checked.cost caller) caller base saved :=
    growth.nextInput (by simpa only [Nat.zero_add] using entry.capacity)
  have room : b + selected.checked.need ≤ frame := by
    have workspace := entry.workspace
    have above := entry.pointerAbove
    have below := entry.pointerBelow
    change b + selected.checked.need ≤ lo at workspace
    change lo ≤ pointer at above
    change pointer < frame at below
    omega
  refine ⟨saved,captureRun,captured,represented,room,capacity,?_⟩
  rcases selected.checked.sound represented room capacity with
    ⟨out,target,addresses,source,bodyRun,bodyRepr,stack,extension,bodyGrowth⟩ | ⟨source,bodyRun⟩
  · have callSource : (.call f args .none body : Stmt C Γ Γ).run caller = .ok out := by
      simpa only [LoopScopes.run_singleton] using source
    exact .inl ⟨out,callSource,
      NoneProducer.returns selected lo pointer flags L frame caller base machine start entry out callSource⟩
  · have callSource : (.call f args .none body : Stmt C Γ Γ).run caller = .error .revert := by
      simpa only [LoopScopes.run_singleton] using source
    refine .inr ⟨callSource,bodyRun,?_⟩
    change run (Restore.saveCells pointer (Restore.contextCells b Γ) ++
      selected.checked.code ++ Restore.restoreCells pointer (Restore.contextCells b Γ)) machine = _
    rw [List.append_assoc,run_append_ok captureRun]
    exact run_append_revert bodyRun

theorem revert_iff
    {C : Contract} {Γ ps Γf : Ctx} {b L frame : Nat} {F : Frag Γ}
    {f : Name} {args : Args C Γ ps} {body : Prog C ps Γf}
    (selected : Composition.Program b F (.cons (.call f args .none body) .nil))
    (lo pointer : Nat) (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag .refl)
    {caller : State C Γ} {base : Nat → Fin W} {machine : Machine} {start : Nat}
    (entry : InterfaceV1.Entry (NoneProducer.plan selected lo pointer)
      L b frame F caller base machine start) :
    run (NoneProducer.plan selected lo pointer).code machine = .revert ↔
      (.call f args .none body : Stmt C Γ Γ).run caller = .error .revert := by
  obtain ⟨saved,captureRun,captured,represented,room,capacity,alternatives⟩ :=
    terminal_exact selected lo pointer flags entry
  rcases alternatives with ⟨out,source,target,addresses,whole,rest⟩ | ⟨source,bodyRun,whole⟩
  · constructor
    · intro bad
      rw [bad] at whole
      cases whole
    · intro bad
      rw [bad] at source
      cases source
  · exact ⟨fun _ => source,fun _ => whole⟩

theorem no_fault
    {C : Contract} {Γ ps Γf : Ctx} {b L frame : Nat} {F : Frag Γ}
    {f : Name} {args : Args C Γ ps} {body : Prog C ps Γf}
    (selected : Composition.Program b F (.cons (.call f args .none body) .nil))
    (lo pointer : Nat) (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag .refl)
    {caller : State C Γ} {base : Nat → Fin W} {machine : Machine} {start : Nat}
    (entry : InterfaceV1.Entry (NoneProducer.plan selected lo pointer)
      L b frame F caller base machine start) :
    run (NoneProducer.plan selected lo pointer).code machine ≠ .fault := by
  obtain ⟨saved,captureRun,captured,represented,room,capacity,alternatives⟩ :=
    terminal_exact selected lo pointer flags entry
  rcases alternatives with ⟨out,source,target,addresses,whole,rest⟩ | ⟨source,bodyRun,whole⟩
  · intro bad
    rw [bad] at whole
    cases whole
  · intro bad
    rw [whole] at bad
    cases bad

theorem reflect_success
    {C : Contract} {Γ ps Γf : Ctx} {b L frame : Nat} {F : Frag Γ}
    {f : Name} {args : Args C Γ ps} {body : Prog C ps Γf}
    (selected : Composition.Program b F (.cons (.call f args .none body) .nil))
    (lo pointer : Nat) (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag .refl)
    {caller : State C Γ} {base : Nat → Fin W} {machine : Machine} {start : Nat}
    (entry : InterfaceV1.Entry (NoneProducer.plan selected lo pointer)
      L b frame F caller base machine start)
    {final : Machine} (executed : run (NoneProducer.plan selected lo pointer).code machine = .ok final 0) :
    ∃ out addresses,
      (.call f args .none body : Stmt C Γ Γ).run caller = .ok out ∧
      StateRepr L b frame selected.checked.frag out.st addresses final ∧
      final.stack = machine.stack ∧ BaseExtends caller.H base addresses ∧
      GrowsAllocator b frame (selected.checked.cost caller) caller base machine out.st addresses final ∧
      final.mem pointer = .val (wmod start) ∧ Footprint.Words lo start machine final := by
  obtain ⟨saved,captureRun,captured,represented,room,capacity,alternatives⟩ :=
    terminal_exact selected lo pointer flags entry
  rcases alternatives with ⟨out,source,target,addresses,whole,represented,stack,extension,growth,cursor,older⟩ |
      ⟨source,bodyRun,whole⟩
  · have same : target = final := (Evm.Out.ok.inj (whole.symm.trans executed)).1
    subst target
    exact ⟨out,addresses,source,represented,stack,extension,growth,cursor,older⟩
  · rw [whole] at executed
    cases executed

theorem revert_iff_tail
    {C : Contract} {Γ ps Γf : Ctx} {b L frame : Nat} {F : Frag Γ}
    {f : Name} {args : Args C Γ ps} {body : Prog C ps Γf}
    (selected : Composition.Program b F (.cons (.call f args .none body) .nil))
    (lo pointer : Nat) (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag .refl)
    {caller : State C Γ} {base : Nat → Fin W} {machine : Machine} {start : Nat}
    (entry : InterfaceV1.Entry (NoneProducer.plan selected lo pointer)
      L b frame F caller base machine start)
    (tail : List Word) :
    run (NoneProducer.plan selected lo pointer).code (appendTail machine tail) = .revert ↔
      (.call f args .none body : Stmt C Γ Γ).run caller = .error .revert := by
  have stable := run_tail (NoneProducer.plan selected lo pointer).code machine tail
    (no_fault selected lo pointer flags entry)
  rw [stable]
  have observation : appendOut tail (run (NoneProducer.plan selected lo pointer).code machine) = .revert ↔
      run (NoneProducer.plan selected lo pointer).code machine = .revert := by
    cases run (NoneProducer.plan selected lo pointer).code machine <;>
      simp only [appendOut,reduceCtorEq]
  exact observation.trans (revert_iff selected lo pointer flags entry)

end Solidity.Backend.Passes.RuntimeVoidReflection
