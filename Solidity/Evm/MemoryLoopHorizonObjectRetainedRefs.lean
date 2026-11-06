import Solidity.Evm.MemoryLoopHorizonObjectNewInventory
import Solidity.Evm.MemoryLoopHorizonAppend

/-! Typed identities and pointer values retained across actual allocating
loop resumption. Arrays created in the first phase are weakened through the
actual second-phase heap extension. Their lengths remain zero, their encoded
pointers retain the intermediate base values, and their final headers are zero.
Both successful prefixes and the summed-horizon target execution are exported;
remaining demand derives from the original budget, without a capacity reset. -/
namespace Solidity.Evm.Memory.HorizonObjectAllocating
variable {C : Contract} {Γ : Ctx}

theorem target_retained_new_refs {L b frame : Nat}
    (compiled : Construction.CompiledLoop b (Frag.init Γ) (.simple (.bool true) : Val C Γ .bool) body)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine} (elapsed remaining : Nat)
    (repr : Objects.StateRepr L b frame (Frag.init Γ) state base machine)
    (capacity : b + frameNeedProg (body : Prog C Γ _) ≤ frame)
    (demand : Objects.AllocationInput b frame (elapsed + remaining) state base machine) :
    ∃ (out : Solidity.Out C state.H Γ) (tail : Solidity.Out C out.st.H Γ)
      (midBase nextBase : Nat → Fin W) (mid reached : Machine),
      loopIterN (fun m => exec compiled.conditionCode 0 m) (fun m => exec compiled.bodyCode 0 m)
        elapsed machine = .inl mid ∧
      loopIterN (fun m => exec compiled.conditionCode 0 m) (fun m => exec compiled.bodyCode 0 m)
        remaining mid = .inl reached ∧
      loopIterN (fun m => exec compiled.conditionCode 0 m) (fun m => exec compiled.bodyCode 0 m)
        (elapsed + remaining) machine = .inl reached ∧
      Construction.CountedLoopPrefix (.simple (.bool true)) body state out elapsed elapsed ∧
      Construction.CountedLoopPrefix (.simple (.bool true)) body out.st tail remaining remaining ∧
      BaseExtends out.st.H midBase nextBase ∧
      (∀ i, i < elapsed → ∃ r : HRef out.st.H (.array (.prim .uint)),
        r.id = state.H.length + i ∧
        tail.st.heap.len (r.wk tail.ext) .dyn = 0 ∧
        nextBase (r.wk tail.ext).id = midBase r.id ∧
        reached.mem (nextBase (r.wk tail.ext).id).val = w[0]) := by
  obtain ⟨out,midBase,mid,firstRun,source,hp,current,stack,bases,grows⟩ :=
    target_pending compiled elapsed repr capacity (demand.of_le (by omega))
  have tailInput : Objects.AllocationInput b frame remaining out.st midBase mid :=
    grows.nextInput demand
  obtain ⟨tail,nextBase,reached,tailRun,tailSource,tailPrefix,finalRepr,tailStack,tailBases,tailGrows⟩ :=
    target_pending compiled remaining current capacity tailInput
  have fullRun := (loopIterN_add_of_pending firstRun remaining).trans tailRun
  refine ⟨out,tail,midBase,nextBase,mid,reached,firstRun,tailRun,fullRun,hp,tailPrefix,tailBases,?_⟩
  intro i within
  obtain ⟨r,identity,empty⟩ := prefix_new_ref hp i within
  have kept : Heap.Keeps tail.ext out.st.heap tail.st.heap := prefix_keeps_heap tailPrefix
  have finalEmpty : tail.st.heap.len (r.wk tail.ext) .dyn = 0 :=
    (kept.len r .dyn).trans empty
  have header := (finalRepr.heap.arrays .dyn (r.wk tail.ext)).length rfl
  exact ⟨r,identity,finalEmpty,tailBases r,by simpa only [finalEmpty] using header⟩

end Solidity.Evm.Memory.HorizonObjectAllocating
