import Solidity.Backend.MemoryCopies.NestedStorageHeader
import Solidity.Backend.MemoryCopies.NestedMemoryParent
import Solidity.Backend.MemoryCopies.NestedMemoryParentDemand

/-! A checked nested storage copy feeds its actual returned pointer into the
existing deep memory copy. Both phases retain their full allocators. This is a
word-machine composition, not Source, gas, numeric-Keccak or five-location adequacy. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def nestedLocationPipelineCode (primitive : PrimTy) : List Instr :=
  nestedStorageHeaderCode ++ nestedMemoryParentCode primitive

def NestedLocationPipelineResult {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (bounded : rows.length < W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot)
    (fits : cursor.val + 2 * nestedStorageParentDemand rows < W) : Prop :=
  let value := nestedStorageParentValue primitive rows bounded
  let first := value.copyStToM heap rfl
  let snapshot := MVal.copyMToSt first.heap first.val
  let second := snapshot.copyStToM first.heap rfl
  ∃ (firstFits : cursor.val + nestedStorageParentDemand rows < W),
    ∃ (base₁ : Nat → Fin W) (intermediate : Machine)
      (_secondFits : cursor.val + nestedStorageParentDemand rows + memoryParentDemand first.heap primitive first.val < W)
      (base₂ : Nat → Fin W) (target : Machine),
    run nestedStorageHeaderCode (machine.push (.slot source)) = .ok (intermediate.push (.val cursor)) 0 ∧
    Objects.AllocatorRepr first.heap base₁ frame ⟨cursor.val + nestedStorageParentDemand rows, firstFits⟩ intermediate ∧
    base₁ first.val.id = cursor ∧
    run (nestedMemoryParentCode primitive) (intermediate.push (.val cursor)) =
      .ok (target.push (.val ⟨cursor.val + nestedStorageParentDemand rows, firstFits⟩)) 0 ∧
    run (nestedLocationPipelineCode primitive) (machine.push (.slot source)) =
      .ok (target.push (.val ⟨cursor.val + nestedStorageParentDemand rows, firstFits⟩)) 0 ∧
    Objects.AllocatorRepr second.heap base₂ frame ⟨cursor.val + 2 * nestedStorageParentDemand rows, fits⟩ target ∧
    base₂ second.val.id = ⟨cursor.val + nestedStorageParentDemand rows, firstFits⟩ ∧
    base₂ (first.val.wk second.ext).id = cursor ∧
    BaseExtends H base base₂ ∧ target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
    (∀ address, 0 < address → address < cursor.val + nestedStorageParentDemand rows →
      target.mem address = intermediate.mem address) ∧
    (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap second.heap base₂ lo hi) ∧
    Heap.Keeps (first.ext.trans second.ext) heap second.heap ∧ Heap.Keeps second.ext first.heap second.heap ∧
    first.val.id < second.val.id ∧ second.heap.len second.val .dyn = rows.length ∧
    MVal.copyMToSt second.heap (first.val.wk second.ext) = value.strip ∧
    MVal.copyMToSt second.heap second.val = snapshot.strip

def NestedLocationPipelineRefusal {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (bounded : rows.length < W)
    (_base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot) : Prop :=
  let value := nestedStorageParentValue primitive rows bounded
  let first := value.copyStToM heap rfl
  (¬ cursor.val + nestedStorageParentDemand rows < W ∧
    run nestedStorageHeaderCode (machine.push (.slot source)) = .revert) ∨
  ∃ (firstFits : cursor.val + nestedStorageParentDemand rows < W),
    ∃ (base₁ : Nat → Fin W) (intermediate : Machine),
    run nestedStorageHeaderCode (machine.push (.slot source)) = .ok (intermediate.push (.val cursor)) 0 ∧
    Objects.AllocatorRepr first.heap base₁ frame ⟨cursor.val + nestedStorageParentDemand rows, firstFits⟩ intermediate ∧
    base₁ first.val.id = cursor ∧
    MVal.copyMToSt first.heap first.val = value.strip ∧
    ¬ cursor.val + 2 * nestedStorageParentDemand rows < W ∧
    run (nestedMemoryParentCode primitive) (intermediate.push (.val cursor)) = .revert

structure NestedLocationPipelineCertificate : Prop where
  execute : ∀ {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (bounded : rows.length < W)
    (shadow : SList (.ref (.array (.prim primitive))))
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot) (L : Nat),
    Objects.AllocatorRepr heap base frame cursor machine →
    ReprAt machine.store L (.ref (.array (.ref (.array (.prim primitive))))) source
      (nestedStorageHeaderValue primitive rows bounded shadow) →
    (∃ fits, NestedLocationPipelineResult heap primitive rows bounded base frame cursor machine source fits) ∨
    (NestedLocationPipelineRefusal heap primitive rows bounded base frame cursor machine source ∧
      run (nestedLocationPipelineCode primitive) (machine.push (.slot source)) = .revert)
end Solidity.Backend.MemoryCopies
