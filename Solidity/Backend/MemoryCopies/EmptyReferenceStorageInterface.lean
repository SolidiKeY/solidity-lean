import Solidity.Backend.MemoryCopies.CheckedStorageArray
import Solidity.Evm.MemoryDefaultCompile

/-! Actual header-driven copying for empty live arrays at any map-free element
type. Stored shadows and unused child implementations are not traversed. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def emptyStoredArray (element : Ty) (shadow : SList element) : SVal (.ref (.array element)) :=
  .array .nil shadow SVal.zero_lt_bound

def EmptyStorageCopyResult (code : List Instr) {H : HTy} (heap : Heap H) (element : Ty)
    (shadow : SList element) (memory : (Ty.ref (.array element)).mapFree = true)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot)
    (fits : cursor.val + 1 < W) : Prop :=
  let grown := (emptyStoredArray element shadow).copyStToM heap memory
  ∃ base' target,
    run code (machine.push (.slot source)) = .ok (target.push (.val cursor)) 0 ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + 1, fits⟩ target ∧
    base' grown.val.id = cursor ∧ BaseExtends H base base' ∧
    target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
    (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
    grown.val.id = H.length ∧ grown.heap.len grown.val .dyn = 0

structure EmptyStorageCopyCertificate : Prop where
  runtime : ∀ {H : HTy} (heap : Heap H) (element : Ty) (shadow : SList element)
    (memory : (Ty.ref (.array element)).mapFree = true) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot) (L : Nat),
    Objects.AllocatorRepr heap base frame cursor machine →
    ReprAt machine.store L (.ref (.array element)) source (emptyStoredArray element shadow) →
    ∀ fits : cursor.val + 1 < W,
    EmptyStorageCopyResult runtimeStorageArrayCode heap element shadow memory base frame cursor machine source fits
  checked : ∀ {H : HTy} (heap : Heap H) (element : Ty) (shadow : SList element)
    (memory : (Ty.ref (.array element)).mapFree = true) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot) (L : Nat),
    Objects.AllocatorRepr heap base frame cursor machine →
    ReprAt machine.store L (.ref (.array element)) source (emptyStoredArray element shadow) →
    (∃ fits, EmptyStorageCopyResult checkedStorageArrayCode heap element shadow memory
      base frame cursor machine source fits) ∨
    (¬ cursor.val + 1 < W ∧ run checkedStorageArrayCode (machine.push (.slot source)) = .revert)

end Solidity.Backend.MemoryCopies
