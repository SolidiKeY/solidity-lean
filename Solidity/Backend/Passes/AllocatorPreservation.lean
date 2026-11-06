import Solidity.Backend.Passes.HeapBoundary

/-! A nonallocating object pass preserves the REAL allocator. Its subsequent
allocation consumes that same selected map, original frame and reached cost. -/
namespace Solidity.Backend.Passes
open Evm Evm.Compiler
variable {C : Contract} {b L frame : Nat} {Γ Δ Ξ : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ} {Q : Prog C Δ Ξ}
  {base : Nat → Fin W} {σ : State C Γ} {m : Machine}

/-- Preserve the complete object allocator through the actual prefix. The
capacity premise is an ENTRY allocator/budget, not desired suffix preservation. -/
theorem objects_budgeted_construction_link (left : Memory.Objects.CompiledProg b F P)
    (right : Memory.Construction.CompiledProg b left.frag Q)
    (capacity : b + Memory.frameNeedProg Q ≤ frame)
    (budget : ∀ o : Solidity.Out C σ.H Δ, P.run σ = .ok o →
      Memory.Objects.AllocationInput b frame (Memory.Construction.allocationCostProg Q o.st)
        σ base m) :
    MappedBoundaryLink (.objects left) (.construction right) L frame base σ m := by
  intro o mid selected hs _ output
  rcases output with ⟨rfl,state,keeps⟩
  refine ⟨state,capacity,?_⟩
  rcases budget o hs with zero | ⟨positive,cursor,allocator,space⟩
  · exact .inl zero
  · exact .inr ⟨positive,cursor,keeps cursor positive allocator,space⟩

/-- The weaker old allocator is obtained by a proved projection ONLY after
the actual stronger allocator has survived the object pass. -/
theorem objects_budgeted_memory_link (left : Memory.Objects.CompiledProg b F P)
    (right : Memory.CompiledProg b left.frag Q)
    (capacity : b + Memory.frameNeedProg Q ≤ frame)
    (budget : ∀ o : Solidity.Out C σ.H Δ, P.run σ = .ok o →
      Memory.Objects.AllocationInput b frame (right.cert.cost o.st) σ base m) :
    MappedBoundaryLink (.objects left) (.memory right) L frame base σ m := by
  intro o mid selected hs _ output
  rcases output with ⟨rfl,state,keeps⟩
  refine ⟨state.legacy,capacity,?_⟩
  rcases budget o hs with zero | ⟨positive,cursor,allocator,space⟩
  · exact .inl zero
  · exact .inr ⟨positive,cursor,(keeps cursor positive allocator).legacy,space⟩

/-- An allocating construction prefix may similarly pass its reached complete
allocator into the existing legacy allocating compiler with the real SUM cost. -/
theorem construction_budgeted_memory_link (left : Memory.Construction.CompiledProg b F P)
    (right : Memory.CompiledProg b left.frag Q)
    (capacity : b + Memory.frameNeedProg Q ≤ frame)
    (budget : ∀ o : Solidity.Out C σ.H Δ, P.run σ = .ok o →
      Memory.Objects.AllocationInput b frame
        (Memory.Construction.allocationCostProg P σ + right.cert.cost o.st) σ base m) :
    MappedBoundaryLink (.construction left) (.memory right) L frame base σ m := by
  intro o mid selected hs _ output
  refine ⟨output.1.legacy,capacity,?_⟩
  rcases output.2.2.nextInput (budget o hs) with zero | ⟨positive,cursor,allocator,space⟩
  · exact .inl zero
  · exact .inr ⟨positive,cursor,allocator.legacy,space⟩

end Solidity.Backend.Passes
