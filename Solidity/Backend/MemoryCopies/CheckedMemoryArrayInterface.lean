import Solidity.Backend.MemoryCopies.RuntimeMemoryArray

/-! Capacity-checked fresh primitive-array copying. Actual cursor and length
loads select success or word-machine refusal; no Source panic/gas claim. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def memoryArrayCapacityGuard : List Instr :=
  [.dup 1,.mloadAt,.mload 0,.push (.val (wmod (W - 1))),.sub,.gt] ++ assertTop

def checkedMemoryArrayCode : List Instr := memoryArrayCapacityGuard ++ runtimeMemoryArrayCode

def CheckedMemoryArrayResult {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (input : HRef H (.array (.prim primitive))) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (fits : cursor.val + (heap.len input .dyn + 1) < W) : Prop :=
    let grown := (MVal.copyMToSt heap (T := .ref (.array (.prim primitive))) input).copyStToM heap rfl
    ∃ base' target,
      run checkedMemoryArrayCode (machine.push (.val (base input.id))) = .ok (target.push (.val cursor)) 0 ∧
      Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + (heap.len input .dyn + 1),fits⟩ target ∧
      base' grown.val.id = cursor ∧ BaseExtends H base base' ∧
      target = {machine with mem := target.mem} ∧
      (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
      (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
      Heap.Keeps grown.ext heap grown.heap ∧ input.id < grown.val.id

structure CheckedMemoryArrayCertificate : Prop where
  execute : ∀ {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (input : HRef H (.array (.prim primitive))) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine),
    Objects.AllocatorRepr heap base frame cursor machine →
    (∃ fits, CheckedMemoryArrayResult heap primitive input base frame cursor machine fits) ∨
      (¬ cursor.val + (heap.len input .dyn + 1) < W ∧
        run checkedMemoryArrayCode (machine.push (.val (base input.id))) = .revert)
end Solidity.Backend.MemoryCopies
