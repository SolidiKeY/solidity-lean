import Solidity.Evm.MemoryLoopHorizonObjectAllocatingTarget

/-! Checked typed nested read selection after allocating-loop execution.
The existing pointer selector accepts the parent-to-child path, then the value
selector accepts the child primitive read. Their actual returned certificate
executes the same emitted code from the reached complete representation, with
success/revert agreement. Map-free source typing and both accepted core indices
are explicit, alongside original finite capacity. No parser authenticity or
whole compiler/source adequacy is claimed. -/
namespace Solidity.Evm.Memory.HorizonObjectAllocating
variable {C : Contract} {Γ : Ctx}

theorem checked_nested_reads_after_loop {L b frame : Nat}
    (compiled : Construction.CompiledLoop b (Frag.init Γ) (.simple (.bool true) : Val C Γ .bool) body)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine} (n : Nat)
    (repr : Objects.StateRepr L b frame (Frag.init Γ) state base machine)
    (capacity : b + frameNeedProg (body : Prog C Γ _) ≤ frame)
    (demand : Objects.AllocationInput b frame n state base machine)
    {A R : RefTy} {p : PrimTy} (parentLayout : ArrTy A (.ref R)) (childLayout : ArrTy R (.prim p))
    (mapFree : (Ty.ref A).mapFree = true) (src : Idx Γ (.mem A))
    (parentIndex childIndex : Val C Γ .uint)
    (acceptedParent : valIn (Frag.init Γ) parentIndex = true)
    (acceptedChild : valIn (Frag.init Γ) childIndex = true) :
    ∃ (read : Objects.CompiledVal b (Frag.init Γ)
        (.readMem (.index childLayout (.loc (.index parentLayout (.var src mapFree) parentIndex)) childIndex)))
      (out : Solidity.Out C state.H Γ) (nextBase : Nat → Fin W) (reached : Machine),
      Objects.compileVal b (Frag.init Γ)
        (.readMem (.index childLayout (.loc (.index parentLayout (.var src mapFree) parentIndex)) childIndex)) = some read ∧
      loopIterN (fun m => exec compiled.conditionCode 0 m) (fun m => exec compiled.bodyCode 0 m)
        n machine = .inl reached ∧
      Construction.CountedLoopPrefix (.simple (.bool true)) body state out n n ∧
      Objects.StateRepr L b frame (Frag.init Γ) out.st nextBase reached ∧
      ValOutT p ((Val.readMem
        (.index childLayout (.loc (.index parentLayout (.var src mapFree) parentIndex)) childIndex)).evalT out.st)
        (run read.code reached) reached := by
  let path : MPath C Γ (.ref R) := .loc (.index parentLayout (.var src mapFree) parentIndex)
  let pointer : Objects.CompiledPtr b (Frag.init Γ) path :=
    ⟨[.mload (cellOf b src)] ++ Evm.compileVal b parentIndex ++ Objects.readCode parentLayout,
      .index parentLayout (.var src mapFree) _ (.local src mapFree) parentIndex acceptedParent⟩
  have pointerSelected : Objects.compilePtr b (Frag.init Γ) path = some pointer := by
    change (if h : valIn (Frag.init Γ) parentIndex = true then some _ else none) = some pointer
    rw [dif_pos acceptedParent]
  let read : Objects.CompiledVal b (Frag.init Γ) (.readMem (.index childLayout path childIndex)) :=
    ⟨pointer.code ++ Evm.compileVal b childIndex ++ Objects.readCode childLayout,
      .read childLayout path pointer.code pointer.cert childIndex acceptedChild⟩
  have selected : Objects.compileVal b (Frag.init Γ)
      (.readMem (.index childLayout path childIndex)) = some read := by
    change (Objects.compilePtr b (Frag.init Γ) path >>= fun ptr =>
      if hi : valIn (Frag.init Γ) childIndex = true then
        some ⟨ptr.code ++ Evm.compileVal b childIndex ++ Objects.readCode childLayout,
          .read childLayout path ptr.code ptr.cert childIndex hi⟩ else none) = some read
    rw [pointerSelected]
    change (if h : valIn (Frag.init Γ) childIndex = true then some _ else none) = some read
    rw [dif_pos acceptedChild]
  obtain ⟨out,nextBase,reached,target,source,hp,current,stack,bases,grows⟩ :=
    target_pending compiled n repr capacity demand
  exact ⟨read,out,nextBase,reached,selected,target,hp,current,read.cert.correct current⟩

end Solidity.Evm.Memory.HorizonObjectAllocating
