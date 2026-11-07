import Solidity.Backend.MemoryCopies.FixedMemoryCopy
import Solidity.Backend.MemoryCopies.CheckedDefault

/-! Fixed memory copies check the complete positive reservation before copying.
Fresh-copy success and target refusal do not assert Source panic semantics. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def checkedFixedMemoryCode (count : Nat) : List Instr :=
  defaultCapacityGuard (max 1 count) ++ runtimeFixedMemoryCode count

def CheckedFixedMemoryResult {H : HTy} (heap : Heap H) (primitive : PrimTy) (count : Nat)
    (input : HRef H (.fixed (.prim primitive) count)) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (fits : cursor.val + max 1 count < W) : Prop :=
  let grown := (MVal.copyMToSt heap (T := .ref (.fixed (.prim primitive) count)) input).copyStToM heap rfl
  ∃ base' target,
    run (checkedFixedMemoryCode count) (machine.push (.val (base input.id))) = .ok (target.push (.val cursor)) 0 ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + max 1 count,fits⟩ target ∧
    base' grown.val.id = cursor ∧ BaseExtends H base base' ∧ target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
    (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
    Heap.Keeps grown.ext heap grown.heap ∧ input.id < grown.val.id

structure CheckedFixedMemoryCertificate : Prop where
  execute : ∀ {H : HTy} (heap : Heap H) (primitive : PrimTy) (count : Nat)
    (input : HRef H (.fixed (.prim primitive) count)) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine), Objects.AllocatorRepr heap base frame cursor machine →
    (∃ fits, CheckedFixedMemoryResult heap primitive count input base frame cursor machine fits) ∨
    (¬ cursor.val + max 1 count < W ∧
      run (checkedFixedMemoryCode count) (machine.push (.val (base input.id))) = .revert)
end Solidity.Backend.MemoryCopies
