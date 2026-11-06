import Solidity.Evm.MemoryLoopHorizonObjectAllocatingPrefixes

/-! Original typed objects survive actual empty-array allocation prefixes.
Successful body execution uses the owner allocation-preservation law; genuine
prefixes compose it across heap extensions and scope exit. Heap.Keeps retains
old contents with the required reference weakening. This supplies no physical
capacity, target-write preservation or general mutating-loop assertion. -/
namespace Solidity.Evm.Memory.HorizonObjectAllocating
variable {C : Contract} {Γ : Ctx}

theorem body_keeps_heap {state : State C Γ}
    {out : Solidity.Out C state.H (.mem (.array (.prim .uint))::Γ)}
    (step : body.run state = .ok out) : Heap.Keeps out.ext state.heap out.st.heap := by
  cases step
  exact SVal.keeps_copyStToM (SVal.dflt (.ref (.array (.prim .uint)))) rfl state.heap

theorem prefix_keeps_heap {state : State C Γ} {out : Solidity.Out C state.H Γ} {cost count : Nat}
    (hp : Construction.CountedLoopPrefix (.simple (.bool true)) body state out cost count) :
    Heap.Keeps out.ext state.heap out.st.heap := by
  induction hp with
  | start => exact Heap.Keeps.refl _
  | next hp hc hs ih => exact Heap.Keeps.trans ih (body_keeps_heap hs)

end Solidity.Evm.Memory.HorizonObjectAllocating
