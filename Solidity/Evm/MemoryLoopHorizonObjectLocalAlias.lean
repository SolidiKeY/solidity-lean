import Solidity.Evm.MemoryLoopHorizonObjectAllocatingTarget
import Solidity.Evm.MemoryObjectEmpty

/-! Actual initialized memory locals survive the allocating loop.
Each declaration weakens older local references through its real heap extension;
scope exit drops only the temporary binding. Genuine prefixes retain that typed
binding, and complete reached pointer representations preserve each local's
stored pointer word. The original input representation and finite capacity
remain explicit; no uninitialized-local or general write/call claim is made. -/
namespace Solidity.Evm.Memory.HorizonObjectAllocating
variable {C : Contract} {Γ : Ctx}

theorem body_local_ref {state : State C Γ}
    {out : Solidity.Out C state.H (.mem (.array (.prim .uint))::Γ)}
    (step : body.run state = .ok out) {R : RefTy} (i : Idx Γ (.mem R))
    (r : HRef state.H R) (binding : TEnv.get i state.env = some r) :
    TEnv.get (i.ext (body : Prog C Γ _).ext) out.st.env = some (r.wk out.ext) := by
  change TRun.declMem (.array (.prim .uint)) none rfl state = .ok out at step
  rw [Objects.defaultEmpty_decl] at step
  cases step
  change TEnv.get i (TEnv.wk _ Γ state.env) = _
  rw [TEnv.get_wk,binding]
  rfl

theorem prefix_local_ref {state : State C Γ} {out : Solidity.Out C state.H Γ} {cost count : Nat}
    (hp : Construction.CountedLoopPrefix (.simple (.bool true)) body state out cost count)
    {R : RefTy} (i : Idx Γ (.mem R)) (r : HRef state.H R)
    (binding : TEnv.get i state.env = some r) :
    TEnv.get i out.st.env = some (r.wk out.ext) := by
  induction hp with
  | start => exact binding
  | next hp condition step ih =>
    change TEnv.get i (TEnv.drop (body : Prog C Γ _).ext _) = _
    rw [← TEnv.get_ext_drop]
    exact body_local_ref step i (r.wk _) ih

theorem target_local_aliases {L b frame : Nat}
    (compiled : Construction.CompiledLoop b (Frag.init Γ) (.simple (.bool true) : Val C Γ .bool) body)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine} (n : Nat)
    (repr : Objects.StateRepr L b frame (Frag.init Γ) state base machine)
    (capacity : b + frameNeedProg (body : Prog C Γ _) ≤ frame)
    (demand : Objects.AllocationInput b frame n state base machine) :
    ∃ (out : Solidity.Out C state.H Γ) (nextBase : Nat → Fin W) (reached : Machine),
      loopIterN (fun m => exec compiled.conditionCode 0 m) (fun m => exec compiled.bodyCode 0 m)
        n machine = .inl reached ∧
      Construction.CountedLoopPrefix (.simple (.bool true)) body state out n n ∧
      (∀ {R : RefTy} (i : Idx Γ (.mem R)) (r : HRef state.H R),
        TEnv.get i state.env = some r →
        TEnv.get i out.st.env = some (r.wk out.ext) ∧
        nextBase (r.wk out.ext).id = base r.id ∧
        reached.mem (cellOf b i) = machine.mem (cellOf b i)) := by
  obtain ⟨out,nextBase,reached,target,source,hp,current,stack,bases,grows⟩ :=
    target_pending compiled n repr capacity demand
  refine ⟨out,nextBase,reached,target,hp,?_⟩
  intro R i r binding
  have finalBinding := prefix_local_ref hp i r binding
  obtain ⟨old,oldBinding,oldWord⟩ := repr.pointers i
  have oldSame : r = old := Option.some.inj (binding.symm.trans oldBinding)
  subst old
  obtain ⟨new,newBinding,newWord⟩ := current.pointers i
  have newSame : r.wk out.ext = new := Option.some.inj (finalBinding.symm.trans newBinding)
  subst new
  refine ⟨finalBinding,bases r,?_⟩
  change reached.mem (cellOf b i) = .val (nextBase r.id) at newWord
  rw [bases r] at newWord
  exact newWord.trans oldWord.symm

end Solidity.Evm.Memory.HorizonObjectAllocating
