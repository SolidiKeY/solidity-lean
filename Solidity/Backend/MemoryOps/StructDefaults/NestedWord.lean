import Solidity.Backend.MemoryOps.StructDefaults.NestedIntrinsic
import Solidity.Evm.MemoryStructDefaultPlan

namespace Solidity.Backend.MemoryOps.StructDefaults
open Semantics

/-- Actual Source construction and published intrinsic/word allocation agree at
new nested observers, joined through the shared intrinsic heap (the word plan
is any `DefaultPlan`, not necessarily `defaultPlan?`). Initial target representation, allocator and whole-plan
capacity are explicit; the existing plan soundness carries every child step,
separation, old aliases and the zeroed target free region. -/
theorem source_nested_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (y : Source.EMState E Γ) (fuel : Nat) (σ : State C Δ)
    (layout : NestedLayout E innerDN outerDN innerS outerS tag child innerKey flagKey)
    (plan : Evm.Memory.DefaultPlan (.struct outerS))
    {L b frame : Nat} {F : Evm.Frag Δ} (base : Nat → Fin Evm.W)
    (cursor : Fin Evm.W) (m : Evm.Machine)
    (mapFree : (Ty.ref (.struct outerS)).mapFree = true)
    (represented : Evm.Memory.StateRepr L b frame F σ base m)
    (allocator : Evm.Memory.StructAllocatorRepr σ.heap base frame cursor m)
    (positiveBase : 0 < b) (space : cursor.val + plan.cost < Evm.W) :
    let g := σ.heap.allocDefault (.struct outerS) mapFree
    let z := ((Source.zeroVal (E := E) (Γ := Γ) (fuel+9) (.struct .memory outerDN)).run y).2
    ∃ (base' : Nat → Fin Evm.W) (mem : Nat → Evm.Word),
      Evm.Memory.StateRepr L b frame F (σ.adopt g).1 base' {m with mem := mem} ∧
      Evm.Memory.StructAllocatorRepr g.heap base' frame
        ⟨cursor.val + plan.cost, space⟩ {m with mem := mem} ∧
      Evm.Memory.BaseExtends σ.H base base' ∧
      base' g.val.id = Evm.wmod (cursor.val + plan.root) ∧
      Evm.run plan.code m = .ok (({m with mem := mem} : Evm.Machine).push
        (.val (Evm.wmod (cursor.val + plan.root)))) 0 ∧
      ((Source.zeroVal (E := E) (Γ := Γ) (fuel+9) (.struct .memory outerDN)).run y).1 =
        .ok (.memRef rfl (y.2.heap.next+2)) ∧
      NestedAt z (y.2.heap.next+2) (y.2.heap.next+1) y.2.heap.next g.heap g.val layout ∧
      Heap.Keeps g.ext σ.heap g.heap ∧
      (∀ a, y.2.heap.get a ≠ none → z.2.heap.get a = y.2.heap.get a) := by
  obtain ⟨base', mem, represented', allocator', extension, root, run⟩ :=
    plan.sound σ base cursor m mapFree represented allocator positiveBase space
  obtain ⟨relation, keeps, old⟩ := source_nested_intrinsic y σ.heap fuel layout mapFree
  obtain ⟨ifs, ofs, evaluated, _, _⟩ :=
    source_nested_default y innerDN outerDN layout.inner.source_types layout.source_outer fuel
  exact ⟨base', mem, represented', allocator', extension, root, run,
    congrArg Prod.fst evaluated, relation, keeps, old⟩

#print axioms source_nested_word
end Solidity.Backend.MemoryOps.StructDefaults
