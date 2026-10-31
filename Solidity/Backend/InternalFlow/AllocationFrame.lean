import Solidity.Backend.InternalFlow.FrameLaws
import Solidity.Calculus.RunFrameMem

/-!
# Allocation-only memory-call content framing

This consumes the published withinM predicate and Prog/CallRet frame laws.
It does not broaden admission to writes through old objects or prove target
frames, recursive compilation or whole-world correctness.
-/
namespace Solidity.Backend.InternalFlow

/-- Actual memory-result call return with the exact composed heap extension,
allocation-only frame, full caller tail and result export. Body preservation
is derived from Prog.run_frameM, never assumed as an execution premise.
The readsIn hypothesis is retained in the actual call's withinM certificate. -/
theorem memory_call_allocation_frame {C : Contract} {Γ ps Γf : Ctx}
    (μ : Mutability) (R : RefTy) (function : Name) (name : Var)
    (hd : (Ty.ref R).defaultOkS = true) (hm : (Ty.ref R).mapFree = true)
    (args : Args C Γ ps) (reads : args.readsIn μ = true)
    (body : Prog C ([.mem R] ++ ps) Γf) (within : Prog.withinM μ body = true)
    (caller : State C Γ) (arguments : TEnv C caller.H ps)
    (ha : args.evalT caller = .ok arguments)
    (out : Out C ((CallRet.mem (Γ := Γ) R name hd hm).enterT
      (caller.withEnv arguments)).st.H Γf)
    (hb : body.runR ((CallRet.mem (Γ := Γ) R name hd hm).enterT
      (caller.withEnv arguments)).st = .ok out) :
    let ret : CallRet Γ [.mem R] (.mem R :: Γ) := .mem R name hd hm
    let entry := ret.enterT (caller.withEnv arguments)
    let extension := entry.ext.trans out.ext
    let final : Out C caller.H (.mem R :: Γ) :=
      ⟨out.st.withEnv (ret.leaveT (TEnv.wk extension Γ caller.env)
        (TEnv.take [.mem R] (TEnv.drop body.ext out.st.env))), extension⟩
    TRun.call args ret body.ext body.runR caller = .ok final ∧
      (Stmt.call function args ret body).withinM μ = true ∧
      TGFrameM μ caller final.st final.ext ∧
      Heap.Keeps final.ext caller.heap final.st.heap ∧
      TEnv.drop (.push .refl) final.st.env = TEnv.wk extension Γ caller.env ∧
      final.st.env.1 = (TEnv.take [.mem R] (TEnv.drop body.ext out.st.env)).1 := by
  have entered : TGFrameM μ caller
      ((CallRet.mem (Γ := Γ) R name hd hm).enterT (caller.withEnv arguments)).st
      ((CallRet.mem (Γ := Γ) R name hd hm).enterT (caller.withEnv arguments)).ext :=
    (TGFrameM.env caller arguments (List.prefix_refl _)).trans
      (CallRet.enterT_frameM (μ := μ) (.mem R name hd hm) (caller.withEnv arguments)) _
  have bodyFrame : TGFrameM μ
      ((CallRet.mem (Γ := Γ) R name hd hm).enterT (caller.withEnv arguments)).st out.st out.ext :=
    (Prog.run_frameM body within 0 hb).1
  have composed : TGFrameM μ caller out.st
      (((CallRet.mem (Γ := Γ) R name hd hm).enterT (caller.withEnv arguments)).ext.trans out.ext) :=
    entered.trans bodyFrame _
  refine ⟨call_return args (.mem R name hd hm) body.ext body.runR caller arguments ha out hb,
    ?_, composed.withEnv _, composed.keeps, rfl, rfl⟩
  simp only [Stmt.withinM, Stmt.within, CallRet.noMem, Bool.and_false,
    Bool.false_and, Bool.false_or, reads, within, Bool.true_and]

/-- info: 'Solidity.Backend.InternalFlow.memory_call_allocation_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms memory_call_allocation_frame

end Solidity.Backend.InternalFlow
