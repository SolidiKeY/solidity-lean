import Solidity.Backend.InternalFlow.PublishedDirectCalls
import Solidity.Backend.InternalFlow.WorldResultEmission

/-! Actual successful world-frame execution pins the checked BODY endpoint.
This is not a simulation of world entry/settlement, callbacks, or rollback. -/
namespace Solidity.Backend.InternalFlow.WorldProgramTarget
open ContractWorld Evm Evm.Memory
variable {K : Type} [DecidableEq K] {contracts : K → Contract}

/-- Determinism identifies the represented entry with the entry extracted from
ACTUAL world execution. Only the checked body is executed on the target; world
entry/settlement themselves have no claimed target implementation here. -/
theorem frame_endpoint {k : K} {α : Type} {b L frame : Nat}
    (world next : World contracts) (self : Handle k) (method : Entry (contracts k) α)
    (context : Context) (final : State (contracts k) method.locals)
    (compiled : Calls.Program b (Frag.init []) method.body)
    (stored : Storage (contracts k)) (initial : State (contracts k) [])
    (lookup : world.storage? self = some stored)
    (entered : world.enter self.address context stored method.payable = .ok initial)
    {base : Nat → Fin W} {machine : Machine}
    (repr : StateRepr L b frame (Frag.init []) initial base machine)
    (room : b + compiled.need ≤ frame)
    (capacity : AllocationInput b frame (compiled.cost initial) initial base machine)
    (actual : world.callFrame self method context = .ok (next,final)) :
    ∃ (out : Solidity.Out (contracts k) initial.H method.locals) (reached : Machine) (addresses : Nat → Fin W),
      method.body.run initial = .ok out ∧ out.st = final ∧
      world.finish self.address out.st = .ok next ∧
      Evm.run compiled.code machine = .ok reached 0 ∧
      StateRepr L b frame compiled.frag final addresses reached ∧
      reached.stack = machine.stack ∧ BaseExtends initial.H base addresses ∧
      GrowsAllocator b frame (compiled.cost initial) initial base machine final addresses reached := by
  obtain ⟨st,σ,out,hs,he,hr,hf,hfinal⟩ := World.callFrame_ok actual
  have sameStorage : st = stored := Option.some.inj (hs.symm.trans lookup)
  subst st
  have sameInitial : σ = initial := Except.ok.inj (he.symm.trans entered)
  subst σ
  obtain ⟨m,addresses,ht,repr₂,stack,baseExtension,grows⟩ :=
    PublishedDirectCalls.program_endpoint compiled repr room capacity out hr
  refine ⟨out,m,addresses,hr,hfinal,hf,ht,?_,stack,baseExtension,?_⟩
  · rw [← hfinal];exact repr₂
  · rw [← hfinal];exact grows
/-- The SAME actual bare body failure drives ordinary source-world failure
and checked target-body revert. Other THalt classes are not collapsed to revert;
no failed source/target state, rollback or output bytes are inferred. -/
theorem frame_revert {k : K} {α : Type} {b L frame : Nat}
    (world : World contracts) (self : Handle k) (method : Entry (contracts k) α)
    (context : Context) (compiled : Calls.Program b (Frag.init []) method.body)
    (stored : Storage (contracts k)) (initial : State (contracts k) [])
    (admitted : (world.isLibrary k || (context.isStatic && !(emptyBody method.body))) = false)
    (lookup : world.storage? self = some stored)
    (entered : world.enter self.address context stored method.payable = .ok initial)
    {base : Nat → Fin W} {machine : Machine}
    (repr : StateRepr L b frame (Frag.init []) initial base machine)
    (room : b + compiled.need ≤ frame)
    (capacity : AllocationInput b frame (compiled.cost initial) initial base machine)
    (failed : method.body.run initial = .error .revert) :
    world.callFrame self method context = .error .revert ∧ Evm.run compiled.code machine = .revert := by
  refine ⟨WorldResultEmission.frame_failure world self method context stored initial .revert
    admitted lookup entered failed,?_⟩
  rcases compiled.sound repr room capacity with ⟨out,m,addresses,hs,_⟩ | ⟨_,ht⟩
  · rw [failed] at hs
    contradiction
  · exact ht

end Solidity.Backend.InternalFlow.WorldProgramTarget
