import Solidity.Backend.InternalFlow.CallArgumentPrefix
import Solidity.Backend.InternalFlow.PublishedDirectCalls

/-! Exact ordinary target revert from actual argument evaluation. No failed
State, target trace, rollback or allocation-frontier observation is produced. -/
namespace Solidity.Backend.InternalFlow.ArgumentFailureTarget
open Evm Evm.Memory
variable {C : Contract}

theorem call_revert {b L frame : Nat} {Γ Δ ps rs Γf : Ctx} {F : Frag Γ}
    (name : Name) (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
    (body : Prog C (rs ++ ps) Γf)
    (compiled : Calls.Statement b F (.call name args ret body))
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m) (room : b + compiled.need ≤ frame)
    (capacity : AllocationInput b frame (compiled.cost σ) σ base m)
    (failed : args.evalT σ = .error .revert) :
    Evm.run compiled.code m = .revert := by
  apply PublishedDirectCalls.statement_revert compiled repr room capacity
  exact CallArgumentPrefix.call_failure args ret body.ext body.runR σ .revert failed

/-- The represented caller and its capacity come from the actual successful
prefix, not a supplied intermediate simulation. Growth describes that prefix
only: the failed call has no returned machine or State. -/
theorem after_prefix {b L frame : Nat} {Γ Δ Ξ ps rs Γf : Ctx} {F : Frag Γ}
    {pre : Prog C Γ Δ} (before : Calls.Program b F pre)
    (name : Name) (args : Args C Δ ps) (ret : CallRet Δ rs Ξ)
    (body : Prog C (rs ++ ps) Γf)
    (compiled : Calls.Statement b before.frag (.call name args ret body))
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m)
    (prefixRoom : b + before.need ≤ frame) (callRoom : b + compiled.need ≤ frame)
    (caller : Solidity.Out C σ.H Δ) (executed : pre.run σ = .ok caller)
    (capacity : AllocationInput b frame (before.cost σ + compiled.cost caller.st) σ base m)
    (failed : args.evalT caller.st = .error .revert) :
    ∃ m₁ base₁, Evm.run before.code m = .ok m₁ 0 ∧
      StateRepr L b frame before.frag caller.st base₁ m₁ ∧ m₁.stack = m.stack ∧
      BaseExtends σ.H base base₁ ∧
      GrowsAllocator b frame (before.cost σ) σ base m caller.st base₁ m₁ ∧
      Evm.run compiled.code m₁ = .revert := by
  obtain ⟨m₁,base₁,ht,hr,hk,he,hg⟩ := PublishedDirectCalls.program_endpoint before
    repr prefixRoom (capacity.of_le (Nat.le_add_right _ _)) caller executed
  exact ⟨m₁,base₁,ht,hr,hk,he,hg,
    call_revert name args ret body compiled hr callRoom (hg.nextInput capacity) failed⟩

end Solidity.Backend.InternalFlow.ArgumentFailureTarget
