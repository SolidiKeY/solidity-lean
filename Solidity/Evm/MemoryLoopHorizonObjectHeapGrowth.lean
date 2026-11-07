import Solidity.Evm.MemoryLoopHorizonObjectAllocatingPrefixes

/-! Actual source heap growth for the empty-array allocating loop body. Each
successful declaration appends one typed object, and genuine prefixes retain
that history through scope exit. A count-n source prefix has exactly n more
heap objects. This supplies no physical capacity, ownership conversion or
evaluator-budget change. -/
namespace Solidity.Evm.Memory.HorizonObjectAllocating
variable {C : Contract} {Γ : Ctx}

theorem body_heap_length {state : State C Γ}
    {out : Solidity.Out C state.H (.mem (.array (.prim .uint))::Γ)}
    (step : body.run state = .ok out) : out.st.H.length = state.H.length + 1 := by
  cases step
  simp only [State.allocDefaultG, Objects.emptyArray_copy, State.grow, State.adopt, State.push, Grown.alloc,
    List.length_append, List.length_cons, List.length_nil]

theorem prefix_heap_length {state : State C Γ} {out : Solidity.Out C state.H Γ} {cost count : Nat}
    (hp : Construction.CountedLoopPrefix (.simple (.bool true)) body state out cost count) :
    out.st.H.length = state.H.length + count := by
  induction hp with
  | start => exact (Nat.add_zero _).symm
  | next hp hc hs ih =>
    have current := body_heap_length hs
    simpa only [Nat.add_assoc] using current.trans (congrArg (fun size => size+1) ih)

end Solidity.Evm.Memory.HorizonObjectAllocating
