import Solidity.Backend.Passes.MemoryTripleAdmission

/-! Full legacy-memory output composition for an actual public joined
certificate. The second selected map is retained, rather than reselected
from the existential Rep of the joined execution. -/
namespace Solidity.Backend.Passes.MemoryJoinedOutput
open Evm Evm.Memory Evm.Compiler
variable {C : Contract} {b L frame : Nat} {Γ Δ Ξ : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ} {Q : Prog C Δ Ξ}

/-- The actual reached first source result supplies the heap extension and
cost evaluation point. Fragment equality is supplied by public selection;
no output preservation equality is assumed. -/
theorem compose (left : CompiledProg b F P) (right : CompiledProg b left.frag Q)
    (joined : CompiledProg b F (P.join Q))
    {base middleBase finalBase : Nat → Fin W}
    {state : State C Γ} {out : Solidity.Out C state.H Δ}
    {finalState : State C Ξ} {initial middle final : Machine}
    (reached : P.run state = .ok out) (frag : joined.frag = right.frag)
    (first : MappedOutput (.memory left) L frame base state initial out.st middle middleBase)
    (second : MappedOutput (.memory right) L frame middleBase out.st middle finalState final finalBase) :
    MappedOutput (.memory joined) L frame base state initial finalState final finalBase := by
  refine ⟨?_,BaseExtends.trans out.ext first.2.1 second.2.1,?_⟩
  · change StateRepr L b frame joined.frag finalState finalBase final
    rw [frag]
    exact second.1
  · change GrowsAllocator b frame (allocationCostProg (P.join Q) state)
      state base initial finalState finalBase final
    rw [MemoryJoinCost.successful_prefix P Q state out reached]
    exact GrowsAllocator.comp first.2.2 second.2.2

/-- Select the join through compileProg and retain its full output with the
actual suffix map. Source success is needed only for the reached prefix;
the supplied stage outputs already retain their original full predicates. -/
theorem public_compose (left : CompiledProg b F P) (right : CompiledProg b left.frag Q)
    (hl : Memory.compileProg b F P = some left)
    (hr : Memory.compileProg b left.frag Q = some right)
    {base middleBase finalBase : Nat → Fin W}
    {state : State C Γ} {out : Solidity.Out C state.H Δ}
    {finalState : State C Ξ} {initial middle final : Machine}
    (reached : P.run state = .ok out)
    (first : MappedOutput (.memory left) L frame base state initial out.st middle middleBase)
    (second : MappedOutput (.memory right) L frame middleBase out.st middle finalState final finalBase) :
    ∃ joined : CompiledProg b F (P.join Q),
      Memory.compileProg b F (P.join Q) = some joined ∧ joined.frag = right.frag ∧
      joined.code = left.code ++ right.code ∧
      MappedOutput (.memory joined) L frame base state initial finalState final finalBase := by
  obtain ⟨joined,accepted,frag,code⟩ := memory_compile_join left right hl hr
  exact ⟨joined,accepted,frag,code,compose left right joined reached frag first second⟩

#print axioms compose
#print axioms public_compose
end Solidity.Backend.Passes.MemoryJoinedOutput
