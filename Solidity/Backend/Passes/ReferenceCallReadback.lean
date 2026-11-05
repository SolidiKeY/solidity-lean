import Solidity.Backend.Passes.CapturedReadback
import Solidity.Backend.Passes.RuntimeCaptureReflection
import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducerRef

/-! Consumer of the published memory/tuple return producer. The actual returned
map and full representation supply the capture/update Input. No caller/body
preservation is assumed, and no frontend, world or public ABI claim follows. -/
namespace Solidity.Backend.Passes.ReferenceCallReadback
open Evm Evm.Memory Evm.Compiler
open Solidity.Backend.InternalFlow.RuntimeFrame
variable {C : Contract} {Γ Δ ps rs Γf : Ctx} {b L frame : Nat} {F : Frag Γ}
  {f : Name} {args : Args C Γ ps} {ret : CallRet Γ rs Δ}
  {body : Prog C (rs ++ ps) Γf} {scope : Ext Γ Δ}

theorem execution (form : V3CallProducerRef.Form Γ ret scope)
    (selected : Composition.Program b F (.cons (.call f args ret body) .nil))
    (lo pointer : Nat) (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag scope)
    {caller : State C Γ} {base : Nat → Fin W} {machine : Machine} {start : Nat}
    (entry : InterfaceV1.Entry (V3CallProducerRef.plan selected lo pointer) L b frame F caller base machine start)
    (out : Solidity.Out C caller.H Δ) (sourceCall : (Stmt.call f args ret body).run caller = .ok out)
    {p q : PrimTy} (name : Var) (e : Val C Δ p) (cc : CompiledVal b selected.checked.frag e)
    (dst : Idx Δ (.val q)) (update : Val C (.val p :: Δ) q)
    (uc : CompiledVal b (selected.checked.frag.push (.val p) .ok) update)
    (v : p.Denote) (u : q.Denote) (hv : e.evalT out.st = .ok v)
    (hu : update.evalT (out.st.push (t := .val p) v) = .ok u)
    (room : b+(Δ.length+1) ≤ lo) :
    (Prog.cons (.call f args ret body) (CapturedValueStability.program name e dst update)).run caller =
      .ok ⟨(out.st.push (t := .val p) v).setLocal (.there dst) u,out.ext⟩ ∧
    ∃ (returned : Machine) (addresses : Nat → Fin W) (captured updated : Word),
      run (V3CallProducerRef.plan selected lo pointer).code machine = .ok returned 0 ∧
      StateRepr L b frame selected.checked.frag out.st addresses returned ∧
      returned.stack = machine.stack ∧ BaseExtends caller.H base addresses ∧
      GrowsAllocator b frame (selected.checked.cost caller) caller base machine out.st addresses returned ∧
      returned.mem pointer = .val (wmod start) ∧ Footprint.Words lo start machine returned ∧
      ReprV p v captured ∧ ReprV q u updated ∧ ∀ tail,
        let initial := appendTail returned tail
        let cm := writeMachine initial (cell (b+Δ.length)) captured
        let em := writeMachine cm (cellOf b (.there (u := .val p) dst)) updated
        (CapturedValueStability.compiled name e cc dst update uc).Input L frame addresses out.st initial ∧
        run (V3CallProducerRef.plan selected lo pointer).code (appendTail machine tail) = .ok initial 0 ∧
        MappedOutput (CapturedValueStability.compiled name e cc dst update uc) L frame addresses out.st initial
          ((out.st.push (t := .val p) v).setLocal (.there dst) u) em addresses ∧
        GrowsAllocator b frame (selected.checked.cost caller) caller base (appendTail machine tail)
          ((out.st.push (t := .val p) v).setLocal (.there dst) u) addresses em ∧
        em.mem pointer = .val (wmod start) ∧ Footprint.Words lo start (appendTail machine tail) em ∧
        run ((V3CallProducerRef.plan selected lo pointer).code ++
          (CapturedValueStability.compiled name e cc dst update uc).code ++ [.mload (cell (b+Δ.length))])
          (appendTail machine tail) = .ok (em.push captured) 0 := by
  first
  | (solve | simp only)
  | (solve | decide)
  | (solve | omega)
  | (solve | rfl)
  |
    have roomFrame : b+(Δ.length+1) ≤ frame := by
      have above := entry.pointerAbove
      have below := entry.pointerBelow
      change lo ≤ pointer at above
      change pointer < frame at below
      omega
    obtain ⟨returned,addresses,hcall,represented,stack,extension,growth,cursor,words⟩ :=
      V3CallProducerRef.returns form selected lo pointer flags L frame caller base machine start entry out sourceCall
    obtain ⟨cw,uw,hcw,huw,runs⟩ := CapturedValueStability.execution name e cc dst update uc
      represented roomFrame v u hv hu
    refine ⟨?_,returned,addresses,cw,uw,hcall,represented,stack,extension,growth,cursor,words,hcw,huw,?_⟩
    · rw [Prog.run_cons_ok sourceCall,CapturedValueStability.source name e dst update out.st v u hv hu]
      rfl
    · intro tail
      have suffix := runs (returned.stack ++ tail)
      have prefixRun : run (V3CallProducerRef.plan selected lo pointer).code (appendTail machine tail) =
          .ok (appendTail returned tail) 0 := by
        simpa only [hcall,appendOut] using run_tail (V3CallProducerRef.plan selected lo pointer).code
          machine tail (by rw [hcall]; intro impossible; cases impossible)
      have grown : GrowsAllocator b frame (selected.checked.cost caller) caller base
          (appendTail machine tail) out.st addresses (appendTail returned tail) := by
        intro cursor hb allocator space
        exact (growth cursor hb (allocator.mem_eq rfl) space).mem_eq rfl
      have afterGrowth := suffix.2.2.2.1.2.2
      change GrowsAllocator b frame 0 out.st addresses (appendTail returned tail)
        ((out.st.push (t := .val p) v).setLocal (.there dst) u) addresses _ at afterGrowth
      have freshBelow : cell (b+Δ.length) < lo := by change b+Δ.length < lo; omega
      have oldBelow : cellOf b (.there (u := .val p) dst) < lo := by
        simpa only [cellOf,lvl_there] using
          Nat.lt_of_lt_of_le (lvl_lt b dst) (by omega : b+Δ.length ≤ lo)
      have untouched (address : Nat) (lower : lo ≤ address) :
          (writeMachine (writeMachine (appendTail returned tail) (cell (b+Δ.length)) cw)
            (cellOf b (.there (u := .val p) dst)) uw).mem address = returned.mem address := by
        change upd (upd returned.mem (cell (b+Δ.length)) cw)
          (cellOf b (.there (u := .val p) dst)) uw address = returned.mem address
        exact (upd_other _ _ (by omega : address ≠ cellOf b (.there (u := .val p) dst))).trans
          (upd_other _ _ (by omega : address ≠ cell (b+Δ.length)))
      refine ⟨suffix.1,prefixRun,suffix.2.2.2.1,?_,?_,?_,?_⟩
      · simpa only [Nat.add_zero] using grown.comp afterGrowth
      · have above : lo ≤ pointer := entry.pointerAbove
        exact (untouched pointer above).trans cursor
      · intro address lower upper
        exact (untouched address lower).trans (words address lower upper)
      · rw [List.append_assoc,run_append_ok prefixRun]
        simpa only [appendTail] using
          (run_append_ok (c₂ := [.mload (cell (b+Δ.length))]) suffix.2.2.2.2.1).trans suffix.2.2.2.2.2

theorem call_revert (selected : Composition.Program b F (.cons (.call f args ret body) .nil))
    (lo pointer : Nat) {caller : State C Γ} {base : Nat → Fin W} {machine : Machine} {start : Nat}
    (entry : InterfaceV1.Entry (V3CallProducerRef.plan selected lo pointer) L b frame F caller base machine start)
    (failed : (Stmt.call f args ret body).run caller = .error .revert)
    (suffix : List Instr) (tail : List Word) :
    run ((V3CallProducerRef.plan selected lo pointer).code ++ suffix) (appendTail machine tail) = .revert := by
  have actual := V3CallProducerRef.bare_revert selected lo pointer L frame caller base machine start entry failed
  have transported : run (V3CallProducerRef.plan selected lo pointer).code (appendTail machine tail) = .revert := by
    simpa only [actual,appendOut] using run_tail (V3CallProducerRef.plan selected lo pointer).code
      machine tail (by rw [actual]; intro impossible; cases impossible)
  exact run_append_revert transported

end Solidity.Backend.Passes.ReferenceCallReadback
