import Solidity.Backend.MemoryCopies.NestedLocationPipeline
import Solidity.Backend.MemoryCopies.NestedStorageLive

/-! Contract only for the existing two-location nested pipeline on original
storage values with arbitrary retained shadows. Both reached phases and full
allocators remain explicit; this is not whole five-location adequacy. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def NestedLivePipelineResult {H : HTy} (heap : Heap H) {primitive : PrimTy}
    (value : SVal (.ref (.array (.ref (.array (.prim primitive))))))
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot)
    (fits : cursor.val + 2 * nestedStorageParentDemand (nestedStorageLiveRows value) < W) : Prop :=
  let first := value.copyStToM heap rfl
  let snapshot := MVal.copyMToSt first.heap first.val
  let second := snapshot.copyStToM first.heap rfl
  ∃ (firstFits : cursor.val + nestedStorageParentDemand (nestedStorageLiveRows value) < W),
    ∃ (base₁ : Nat → Fin W) (intermediate : Machine)
      (_secondFits : cursor.val + nestedStorageParentDemand (nestedStorageLiveRows value) + memoryParentDemand first.heap primitive first.val < W)
      (base₂ : Nat → Fin W) (target : Machine),
    run nestedStorageHeaderCode (machine.push (.slot source)) = .ok (intermediate.push (.val cursor)) 0 ∧
    Objects.AllocatorRepr first.heap base₁ frame ⟨cursor.val + nestedStorageParentDemand (nestedStorageLiveRows value), firstFits⟩ intermediate ∧
    base₁ first.val.id = cursor ∧
    run (nestedMemoryParentCode primitive) (intermediate.push (.val cursor)) =
      .ok (target.push (.val ⟨cursor.val + nestedStorageParentDemand (nestedStorageLiveRows value), firstFits⟩)) 0 ∧
    run (nestedLocationPipelineCode primitive) (machine.push (.slot source)) =
      .ok (target.push (.val ⟨cursor.val + nestedStorageParentDemand (nestedStorageLiveRows value), firstFits⟩)) 0 ∧
    Objects.AllocatorRepr second.heap base₂ frame ⟨cursor.val + 2 * nestedStorageParentDemand (nestedStorageLiveRows value), fits⟩ target ∧
    base₂ second.val.id = ⟨cursor.val + nestedStorageParentDemand (nestedStorageLiveRows value), firstFits⟩ ∧
    base₂ (first.val.wk second.ext).id = cursor ∧
    BaseExtends H base base₂ ∧ target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
    (∀ address, 0 < address → address < cursor.val + nestedStorageParentDemand (nestedStorageLiveRows value) →
      target.mem address = intermediate.mem address) ∧
    (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap second.heap base₂ lo hi) ∧
    Heap.Keeps (first.ext.trans second.ext) heap second.heap ∧ Heap.Keeps second.ext first.heap second.heap ∧
    first.val.id < second.val.id ∧ second.heap.len second.val .dyn = (nestedStorageLiveRows value).length ∧
    MVal.copyMToSt second.heap (first.val.wk second.ext) = value.strip ∧
    MVal.copyMToSt second.heap second.val = snapshot.strip

def NestedLivePipelineRefusal {H : HTy} (heap : Heap H) {primitive : PrimTy}
    (value : SVal (.ref (.array (.ref (.array (.prim primitive))))))
    (_base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot) : Prop :=
  let first := value.copyStToM heap rfl
  (¬ cursor.val + nestedStorageParentDemand (nestedStorageLiveRows value) < W ∧
    run nestedStorageHeaderCode (machine.push (.slot source)) = .revert) ∨
  ∃ (firstFits : cursor.val + nestedStorageParentDemand (nestedStorageLiveRows value) < W),
    ∃ (base₁ : Nat → Fin W) (intermediate : Machine),
    run nestedStorageHeaderCode (machine.push (.slot source)) = .ok (intermediate.push (.val cursor)) 0 ∧
    Objects.AllocatorRepr first.heap base₁ frame ⟨cursor.val + nestedStorageParentDemand (nestedStorageLiveRows value), firstFits⟩ intermediate ∧
    base₁ first.val.id = cursor ∧
    MVal.copyMToSt first.heap first.val = value.strip ∧
    ¬ cursor.val + 2 * nestedStorageParentDemand (nestedStorageLiveRows value) < W ∧
    run (nestedMemoryParentCode primitive) (intermediate.push (.val cursor)) = .revert

structure NestedLivePipelineCertificate : Prop where
  execute : ∀ {H : HTy} (heap : Heap H) {primitive : PrimTy}
    (value : SVal (.ref (.array (.ref (.array (.prim primitive))))))
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot) (L : Nat),
    Objects.AllocatorRepr heap base frame cursor machine →
    ReprAt machine.store L (.ref (.array (.ref (.array (.prim primitive))))) source
      value →
    (∃ fits, NestedLivePipelineResult heap value base frame cursor machine source fits) ∨
    (NestedLivePipelineRefusal heap value base frame cursor machine source ∧
      run (nestedLocationPipelineCode primitive) (machine.push (.slot source)) = .revert)
end Solidity.Backend.MemoryCopies
