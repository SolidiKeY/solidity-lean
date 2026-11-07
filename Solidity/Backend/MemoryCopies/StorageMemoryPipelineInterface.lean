import Solidity.Backend.MemoryCopies.CheckedStorageArray
import Solidity.Backend.MemoryCopies.HeapContents

/-! Two actual checked location copies compose through the returned memory
pointer. Capacity refusal has two phases; no rollback, Source or five-location
adequacy is asserted. Both empty copies still allocate their header cells. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def storageMemoryPipelineCode : List Instr := checkedStorageArrayCode ++ checkedMemoryArrayCode

def StorageMemoryPipelineResult {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (values : List primitive.Denote) (bounded : values.length < W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot)
    (fits : cursor.val + 2 * (values.length + 1) < W) : Prop :=
  let value := primitiveArrayValue primitive values bounded
  let first := value.copyStToM heap rfl
  let snapshot := MVal.copyMToSt first.heap first.val
  let second := snapshot.copyStToM first.heap rfl
  ∃ (firstFits : cursor.val + (values.length + 1) < W), ∃ base₁ intermediate base₂ target,
    run checkedStorageArrayCode (machine.push (.slot source)) = .ok (intermediate.push (.val cursor)) 0 ∧
    Objects.AllocatorRepr first.heap base₁ frame ⟨cursor.val + (values.length + 1), firstFits⟩ intermediate ∧
    base₁ first.val.id = cursor ∧
    run storageMemoryPipelineCode (machine.push (.slot source)) =
      .ok (target.push (.val ⟨cursor.val + (values.length + 1), firstFits⟩)) 0 ∧
    Objects.AllocatorRepr second.heap base₂ frame ⟨cursor.val + 2 * (values.length + 1), fits⟩ target ∧
    base₂ second.val.id = ⟨cursor.val + (values.length + 1), firstFits⟩ ∧
    base₂ (first.val.wk second.ext).id = cursor ∧ BaseExtends H base base₂ ∧
    target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
    (∀ address, 0 < address → address < cursor.val + (values.length + 1) → target.mem address = intermediate.mem address) ∧
    (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap second.heap base₂ lo hi) ∧
    Heap.Keeps (first.ext.trans second.ext) heap second.heap ∧
    Heap.Keeps second.ext first.heap second.heap ∧ first.val.id < second.val.id ∧
    MVal.copyMToSt second.heap (first.val.wk second.ext) = value.strip ∧
    MVal.copyMToSt second.heap second.val = snapshot.strip

def StorageMemoryPipelineRefusal {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (values : List primitive.Denote) (bounded : values.length < W)
    (_base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot) : Prop :=
  let value := primitiveArrayValue primitive values bounded
  let first := value.copyStToM heap rfl
  (¬ cursor.val + (values.length + 1) < W ∧
    run checkedStorageArrayCode (machine.push (.slot source)) = .revert) ∨
  ∃ (firstFits : cursor.val + (values.length + 1) < W), ∃ base₁ intermediate,
    run checkedStorageArrayCode (machine.push (.slot source)) = .ok (intermediate.push (.val cursor)) 0 ∧
    Objects.AllocatorRepr first.heap base₁ frame ⟨cursor.val + (values.length + 1), firstFits⟩ intermediate ∧
    base₁ first.val.id = cursor ∧
    MVal.copyMToSt first.heap first.val = value.strip ∧
    ¬ cursor.val + 2 * (values.length + 1) < W ∧
    run checkedMemoryArrayCode (intermediate.push (.val cursor)) = .revert

structure StorageMemoryPipelineCertificate : Prop where
  execute : ∀ {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (values : List primitive.Denote) (bounded : values.length < W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot) (L : Nat),
    Objects.AllocatorRepr heap base frame cursor machine →
    ReprAt machine.store L (.ref (.array (.prim primitive))) source (primitiveArrayValue primitive values bounded) →
    (∃ fits, StorageMemoryPipelineResult heap primitive values bounded base frame cursor machine source fits) ∨
    (StorageMemoryPipelineRefusal heap primitive values bounded base frame cursor machine source ∧
      run storageMemoryPipelineCode (machine.push (.slot source)) = .revert)
end Solidity.Backend.MemoryCopies
