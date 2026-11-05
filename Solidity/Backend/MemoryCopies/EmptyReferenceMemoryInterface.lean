import Solidity.Backend.MemoryCopies.EmptyReferenceStorage

/-! Actual fresh memory-to-memory copying for empty live arrays at arbitrary
map-free element types. Existing ownership supplies source bounds; no child
compiler or general overlap/source-admission theorem is postulated. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def EmptyMemoryCopyResult (code : List Instr) {H : HTy} (heap : Heap H) (element : Ty)
    (input : HRef H (.array element)) (memory : (Ty.ref (.array element)).mapFree = true)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (fits : cursor.val + 1 < W) : Prop :=
  let grown := (MVal.copyMToSt heap (T := .ref (.array element)) input).copyStToM heap memory
  ∃ base' target,
    run code (machine.push (.val (base input.id))) = .ok (target.push (.val cursor)) 0 ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + 1, fits⟩ target ∧
    base' grown.val.id = cursor ∧ BaseExtends H base base' ∧
    target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
    (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
    Heap.Keeps grown.ext heap grown.heap ∧ input.id < grown.val.id ∧
    grown.val.id = H.length ∧ grown.heap.len grown.val .dyn = 0

structure EmptyMemoryCopyCertificate : Prop where
  runtime : ∀ {H : HTy} (heap : Heap H) (element : Ty) (input : HRef H (.array element))
    (memory : (Ty.ref (.array element)).mapFree = true) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine),
    heap.len input .dyn = 0 → Objects.AllocatorRepr heap base frame cursor machine →
    ∀ fits : cursor.val + 1 < W,
    EmptyMemoryCopyResult runtimeMemoryArrayCode heap element input memory base frame cursor machine fits
  checked : ∀ {H : HTy} (heap : Heap H) (element : Ty) (input : HRef H (.array element))
    (memory : (Ty.ref (.array element)).mapFree = true) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine),
    heap.len input .dyn = 0 → Objects.AllocatorRepr heap base frame cursor machine →
    (∃ fits, EmptyMemoryCopyResult checkedMemoryArrayCode heap element input memory base frame cursor machine fits) ∨
    (¬ cursor.val + 1 < W ∧ run checkedMemoryArrayCode (machine.push (.val (base input.id))) = .revert)

end Solidity.Backend.MemoryCopies
