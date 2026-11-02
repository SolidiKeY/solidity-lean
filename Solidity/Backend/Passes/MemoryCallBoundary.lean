import Solidity.Backend.Passes.MappedTail
import Solidity.Backend.Passes.CoreBoundary

/-! Physical links for the published expanded-memory-call branch. Exact
private frame need, reached cost and push-free constructor witness are retained;
legacy StateRepr is never upgraded to object ownership. -/
namespace Solidity.Backend.Passes
open Evm Evm.Compiler
variable {C : Contract} {b L frame : Nat} {Γ Δ Ξ : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ} {Q : Prog C Δ Ξ}
  {base : Nat → Fin W} {σ : State C Γ} {m : Machine}

theorem memoryCalls_memory_link (left : Memory.Calls.Program b F P)
    (pushFree : Evm.Prog.pushes P = 0) (right : Memory.CompiledProg b left.frag Q)
    (capacity : b + Memory.frameNeedProg Q ≤ frame)
    (nonallocating : Memory.hasAllocation Q = false) :
    MappedBoundaryLink (.memoryCalls left pushFree) (.memory right) L frame base σ m := by
  intro o mid selected _ _ output
  exact ⟨output.1,capacity,.inl (Memory.allocationCostProg_zero Q nonallocating o.st)⟩

theorem memoryCalls_budgeted_memory_link (left : Memory.Calls.Program b F P)
    (pushFree : Evm.Prog.pushes P = 0) (right : Memory.CompiledProg b left.frag Q)
    (capacity : b + Memory.frameNeedProg Q ≤ frame)
    (budget : ∀ o : Solidity.Out C σ.H Δ, P.run σ = .ok o →
      Memory.AllocationInput b frame (left.cost σ + right.cert.cost o.st) σ base m) :
    MappedBoundaryLink (.memoryCalls left pushFree) (.memory right) L frame base σ m := by
  intro o mid selected hs _ output
  exact ⟨output.1,capacity,output.2.2.nextInput (budget o hs)⟩

theorem memory_budgeted_memoryCalls_link (left : Memory.CompiledProg b F P)
    (right : Memory.Calls.Program b left.frag Q) (pushFree : Evm.Prog.pushes Q = 0)
    (capacity : b + right.need ≤ frame)
    (budget : ∀ o : Solidity.Out C σ.H Δ, P.run σ = .ok o →
      Memory.AllocationInput b frame (left.cert.cost σ + right.cost o.st) σ base m) :
    MappedBoundaryLink (.memory left) (.memoryCalls right pushFree) L frame base σ m := by
  intro o mid selected hs _ output
  exact ⟨output.1,capacity,output.2.2.nextInput (budget o hs)⟩

theorem memoryCalls_budgeted_link (left : Memory.Calls.Program b F P)
    (leftFree : Evm.Prog.pushes P = 0) (right : Memory.Calls.Program b left.frag Q)
    (rightFree : Evm.Prog.pushes Q = 0) (capacity : b + right.need ≤ frame)
    (budget : ∀ o : Solidity.Out C σ.H Δ, P.run σ = .ok o →
      Memory.AllocationInput b frame (left.cost σ + right.cost o.st) σ base m) :
    MappedBoundaryLink (.memoryCalls left leftFree) (.memoryCalls right rightFree) L frame base σ m := by
  intro o mid selected hs _ output
  exact ⟨output.1,capacity,output.2.2.nextInput (budget o hs)⟩

theorem memoryCalls_nonallocating_link (left : Memory.Calls.Program b F P)
    (leftFree : Evm.Prog.pushes P = 0) (right : Memory.Calls.Program b left.frag Q)
    (rightFree : Evm.Prog.pushes Q = 0) (capacity : b + right.need ≤ frame)
    (nonallocating : right.allocates = false) :
    MappedBoundaryLink (.memoryCalls left leftFree) (.memoryCalls right rightFree) L frame base σ m := by
  intro o mid selected _ _ output
  exact ⟨output.1,capacity,.inl (right.zeroCost nonallocating o.st)⟩

end Solidity.Backend.Passes
