import Solidity.Backend.InternalFlow.RuntimeFrameTarget

/-! Exact typed argument, entry/body extension and result export at the real
checked target endpoint. Heap contents may mutate; old identity-to-address
preservation is not Heap.Keeps. All CallRet types remain intrinsic. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame
open Evm Evm.Memory
variable {C : Contract} {Γ Δ ps rs Γf : Ctx}

def exported (ret : CallRet Γ rs Δ) (scope : Ext (rs ++ ps) Γf)
    (caller : State C Γ) (arguments : TEnv C caller.H ps)
    (out : Solidity.Out C (ret.enterT (caller.withEnv arguments)).st.H Γf) :
    Solidity.Out C caller.H Δ :=
  ⟨out.st.withEnv (ret.leaveT
    (TEnv.wk ((ret.enterT (caller.withEnv arguments)).ext.trans out.ext) Γ caller.env)
    (TEnv.take rs (TEnv.drop scope out.st.env))),
   (ret.enterT (caller.withEnv arguments)).ext.trans out.ext⟩

theorem call_return (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
    (scope : Ext (rs ++ ps) Γf) (body : TStep C (rs ++ ps) Γf)
    (caller : State C Γ) (arguments : TEnv C caller.H ps)
    (evaluated : args.evalT caller = .ok arguments)
    (out : Solidity.Out C (ret.enterT (caller.withEnv arguments)).st.H Γf)
    (executed : body (ret.enterT (caller.withEnv arguments)).st = .ok out) :
    TRun.call args ret scope body caller = .ok (exported ret scope caller arguments out) := by
  simp only [TRun.call,evaluated,ok_bind,executed]
  rfl

/-- A small proof boundary pins a real source output to its checked target
without normalizing a concrete compiler certificate during elaboration. -/
theorem statement_endpoint {b L frame : Nat} {F : Frag Γ} {s : Stmt C Γ Δ}
    (checked : Calls.Statement b F s) {caller : State C Γ}
    {base : Nat → Fin W} {machine : Machine}
    (repr : StateRepr L b frame F caller base machine)
    (room : b + checked.need ≤ frame)
    (capacity : AllocationInput b frame (checked.cost caller) caller base machine)
    (out : Solidity.Out C caller.H Δ) (actual : s.run caller = .ok out) :
    ∃ target addresses, Evm.run checked.code machine = .ok target 0 ∧
      StateRepr L b frame checked.frag out.st addresses target ∧ target.stack = machine.stack ∧
      BaseExtends caller.H base addresses ∧
      GrowsAllocator b frame (checked.cost caller) caller base machine out.st addresses target := by
  rcases checked.sound repr room capacity with ⟨o,m,addresses,hs,ht,hr,hk,he,hg⟩ | ⟨hs,ht⟩
  · have same := Except.ok.inj (hs.symm.trans actual)
    subst o
    exact ⟨m,addresses,ht,hr,hk,he,hg⟩
  · rw [actual] at hs
    contradiction

/-- Exact actual source frame plus independently checked emitted code. The
caller tail is the entry/body transported original tail under ret.leaveT;
private parameter/body locals never replace it. -/
theorem target_return {b L frame : Nat} {F : Frag Γ}
    (f : Name) (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
    (body : Prog C (rs ++ ps) Γf) (checked : Calls.Statement b F (.call f args ret body))
    (caller : State C Γ) (arguments : TEnv C caller.H ps)
    (evaluated : args.evalT caller = .ok arguments)
    (out : Solidity.Out C (ret.enterT (caller.withEnv arguments)).st.H Γf)
    (executed : body.runR (ret.enterT (caller.withEnv arguments)).st = .ok out)
    {base : Nat → Fin W} {machine : Machine}
    (repr : StateRepr L b frame F caller base machine)
    (room : b + checked.need ≤ frame)
    (capacity : AllocationInput b frame (checked.cost caller) caller base machine) :
    ∃ target addresses,
      Evm.run checked.code machine = .ok target 0 ∧
      StateRepr L b frame checked.frag (exported ret body.ext caller arguments out).st addresses target ∧
      target.stack = machine.stack ∧ BaseExtends caller.H base addresses ∧
      GrowsAllocator b frame (checked.cost caller) caller base machine
        (exported ret body.ext caller arguments out).st addresses target := by
  have source : (.call f args ret body : Stmt C Γ Δ).run caller =
      .ok (exported ret body.ext caller arguments out) :=
    call_return args ret body.ext body.runR caller arguments evaluated out executed
  rcases checked.sound repr room capacity with ⟨o,m,addresses,hs,ht,hr,hk,he,hg⟩ | ⟨hs,ht⟩
  · have same := Except.ok.inj (hs.symm.trans source)
    subst o
    exact ⟨m,addresses,ht,hr,hk,he,hg⟩
  · rw [source] at hs
    contradiction
/-- The actual recursive-call CONSTRUCTOR receives the same exact checked
frame endpoint. This does not turn a finite supplied thunk into an unbounded
source/target recursion theorem. -/
theorem target_recursive_return {b L frame : Nat} {F : Frag Γ}
    (f : Name) (d : Nat) (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
    (body : Unit → Prog C (rs ++ ps) (rs ++ ps))
    (checked : Calls.Statement b F (.callRec f d args ret body))
    (caller : State C Γ) (arguments : TEnv C caller.H ps)
    (evaluated : args.evalT caller = .ok arguments)
    (out : Solidity.Out C (ret.enterT (caller.withEnv arguments)).st.H (rs ++ ps))
    (executed : (body ()).runR (ret.enterT (caller.withEnv arguments)).st = .ok out)
    {base : Nat → Fin W} {machine : Machine}
    (repr : StateRepr L b frame F caller base machine)
    (room : b + checked.need ≤ frame)
    (capacity : AllocationInput b frame (checked.cost caller) caller base machine) :
    ∃ target addresses,
      Evm.run checked.code machine = .ok target 0 ∧
      StateRepr L b frame checked.frag (exported ret (body ()).ext caller arguments out).st addresses target ∧
      target.stack = machine.stack ∧ BaseExtends caller.H base addresses ∧
      GrowsAllocator b frame (checked.cost caller) caller base machine
        (exported ret (body ()).ext caller arguments out).st addresses target := by
  have source : (.callRec f d args ret body : Stmt C Γ Δ).run caller =
      .ok (exported ret (body ()).ext caller arguments out) :=
    call_return args ret (body ()).ext (body ()).runR caller arguments evaluated out executed
  rcases checked.sound repr room capacity with ⟨o,m,addresses,hs,ht,hr,hk,he,hg⟩ | ⟨hs,ht⟩
  · have same := Except.ok.inj (hs.symm.trans source)
    subst o
    exact ⟨m,addresses,ht,hr,hk,he,hg⟩
  · rw [source] at hs
    contradiction
end Solidity.Backend.InternalFlow.RuntimeFrame
