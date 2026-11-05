import Solidity.Backend.MemoryCopies.RuntimeStorageArray
import Solidity.Backend.MemoryCopies.CheckedMemoryArray

/-! Actual storage header and memory cursor loads check allocation demand
before deep primitive-array copying. Symbolic capacity refusal is explicit. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def storageArrayCapacityGuard : List Instr :=
  [.dup 1,.sload,.mload 0,.push (.val (wmod (W - 1))),.sub,.gt] ++ assertTop

def checkedStorageArrayCode : List Instr := storageArrayCapacityGuard ++ runtimeStorageArrayCode

def CheckedStorageArrayResult {H : HTy} (heap : Heap H) (primitive : PrimTy) (values : List primitive.Denote)
    (bounded : values.length < W) (base : Nat → Fin W) (frame : Nat) (cursor : Fin W)
    (machine : Machine) (source : Slot) (fits : cursor.val + (values.length + 1) < W) : Prop :=
    let grown := (primitiveArrayValue primitive values bounded).copyStToM heap rfl
    ∃ base' target,
      run checkedStorageArrayCode (machine.push (.slot source)) = .ok (target.push (.val cursor)) 0 ∧
      Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + (values.length + 1),fits⟩ target ∧
      base' grown.val.id = cursor ∧ BaseExtends H base base' ∧
      target = {machine with mem := target.mem} ∧
      (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
      (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi)

structure CheckedStorageArrayCertificate : Prop where
  execute : ∀ {H : HTy} (heap : Heap H) (primitive : PrimTy) (values : List primitive.Denote)
    (bounded : values.length < W) (base : Nat → Fin W) (frame : Nat) (cursor : Fin W)
    (machine : Machine) (source : Slot) (L : Nat),
    Objects.AllocatorRepr heap base frame cursor machine →
    ReprAt machine.store L (.ref (.array (.prim primitive))) source (primitiveArrayValue primitive values bounded) →
    (∃ fits, CheckedStorageArrayResult heap primitive values bounded base frame cursor machine source fits) ∨
      (¬ cursor.val + (values.length + 1) < W ∧ run checkedStorageArrayCode (machine.push (.slot source)) = .revert)
end Solidity.Backend.MemoryCopies
