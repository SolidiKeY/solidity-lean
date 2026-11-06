import Solidity.Evm.MemoryLoopHorizonObjectAllocatingPrefixes

/-! Exact typed source heap history for the empty-array allocating body.
Successful declarations append one uint-array object type, and genuine
prefixes preserve the initial type list followed by exactly count copies.
This derives from actual allocation, not from a cost-to-heap assumption,
and supplies no physical capacity or evaluator-budget change. -/
namespace Solidity.Evm.Memory.HorizonObjectAllocating
variable {C : Contract} {Γ : Ctx}

theorem body_heap_types {state : State C Γ}
    {out : Solidity.Out C state.H (.mem (.array (.prim .uint))::Γ)}
    (step : body.run state = .ok out) : out.st.H = state.H ++ [.array (.prim .uint)] := by
  cases step
  simp only [State.allocDefaultG, Objects.emptyArray_copy, State.grow, State.adopt, State.push, Grown.alloc]

theorem prefix_heap_types {state : State C Γ} {out : Solidity.Out C state.H Γ} {cost count : Nat}
    (hp : Construction.CountedLoopPrefix (.simple (.bool true)) body state out cost count) :
    out.st.H = state.H ++ List.replicate count (.array (.prim .uint)) := by
  induction hp with
  | start => simp only [List.replicate_zero, List.append_nil]
  | next hp hc hs ih =>
    have current := body_heap_types hs
    have extended := current.trans (congrArg (fun types => types ++ [.array (.prim .uint)]) ih)
    simpa only [List.replicate_succ', List.append_assoc] using extended

end Solidity.Evm.Memory.HorizonObjectAllocating
