import Solidity.Evm.MemoryLoopHorizonObjectAllocatingTarget

/-! Checked typed read selection after actual allocating-loop execution.
The existing complete-object value compiler accepts a local-array primitive
read when its core index is accepted. Its returned owner certificate executes
that same emitted read code from the reached complete representation, retaining
success/revert correspondence. Dynamic/fixed layouts and all existing finite
capacity premises remain unchanged. This is typed value selection, not original
source-parser authenticity or whole compiler/source adequacy. -/
namespace Solidity.Evm.Memory.HorizonObjectAllocating
variable {C : Contract} {Γ : Ctx}

theorem checked_local_reads_after_loop {L b frame : Nat}
    (compiled : Construction.CompiledLoop b (Frag.init Γ) (.simple (.bool true) : Val C Γ .bool) body)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine} (n : Nat)
    (repr : Objects.StateRepr L b frame (Frag.init Γ) state base machine)
    (capacity : b + frameNeedProg (body : Prog C Γ _) ≤ frame)
    (demand : Objects.AllocationInput b frame n state base machine)
    {A : RefTy} {p : PrimTy} (layout : ArrTy A (.prim p)) (mapFree : (Ty.ref A).mapFree = true) (src : Idx Γ (.mem A))
    (index : Val C Γ .uint) (acceptedIndex : valIn (Frag.init Γ) index = true) :
    ∃ (read : Objects.CompiledVal b (Frag.init Γ) (.readMem (.index layout (.var src mapFree) index)))
      (out : Solidity.Out C state.H Γ) (nextBase : Nat → Fin W) (reached : Machine),
      Objects.compileVal b (Frag.init Γ) (.readMem (.index layout (.var src mapFree) index)) = some read ∧
      loopIterN (fun m => exec compiled.conditionCode 0 m) (fun m => exec compiled.bodyCode 0 m)
        n machine = .inl reached ∧
      Construction.CountedLoopPrefix (.simple (.bool true)) body state out n n ∧
      Objects.StateRepr L b frame (Frag.init Γ) out.st nextBase reached ∧
      ValOutT p ((Val.readMem (.index layout (.var src mapFree) index)).evalT out.st)
        (run read.code reached) reached := by
  let read : Objects.CompiledVal b (Frag.init Γ) (.readMem (.index layout (.var src mapFree) index)) :=
    ⟨[.mload (cellOf b src)] ++ Evm.compileVal b index ++ Objects.readCode layout,
      .read layout (.var src mapFree) _ (.local src mapFree) index acceptedIndex⟩
  have selected : Objects.compileVal b (Frag.init Γ)
      (.readMem (.index layout (.var src mapFree) index)) = some read := by
    change (if h : valIn (Frag.init Γ) index = true then some _ else none) = some read
    rw [dif_pos acceptedIndex]
  obtain ⟨out,nextBase,reached,target,source,hp,current,stack,bases,grows⟩ :=
    target_pending compiled n repr capacity demand
  exact ⟨read,out,nextBase,reached,selected,target,hp,current,read.cert.correct current⟩

end Solidity.Evm.Memory.HorizonObjectAllocating
