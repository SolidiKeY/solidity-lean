import Solidity.Backend.MemoryCopies.FixedStorageCopy
import Solidity.Backend.MemoryCopies.CheckedDefault

/-! Guarded headerless fixed storage copying retains the existing allocator
and freshness clauses. Capacity refusal is a target outcome, not Source panic. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def checkedFixedStorageCode (count : Nat) : List Instr :=
  defaultCapacityGuard (max 1 count) ++ runtimeFixedStorageCode count

def CheckedFixedStorageResult {H : HTy} (heap : Heap H) (primitive : PrimTy) (count : Nat)
    (value : SVal (.ref (.fixed (.prim primitive) count))) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (source : Slot) (fits : cursor.val + max 1 count < W) : Prop :=
  let grown := value.copyStToM heap rfl
  ∃ base' target,
    run (checkedFixedStorageCode count) (machine.push (.slot source)) = .ok (target.push (.val cursor)) 0 ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + max 1 count,fits⟩ target ∧
    base' grown.val.id = cursor ∧ BaseExtends H base base' ∧ target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
    (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
    Heap.Keeps grown.ext heap grown.heap ∧ (∀ {Q : RefTy} (old : HRef H Q), old.id < grown.val.id)

structure CheckedFixedStorageCertificate : Prop where
  execute : ∀ {H : HTy} (heap : Heap H) (primitive : PrimTy) (count : Nat)
    (value : SVal (.ref (.fixed (.prim primitive) count))) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (source : Slot) (limit : Nat),
    Objects.AllocatorRepr heap base frame cursor machine →
    ReprAt machine.store limit (.ref (.fixed (.prim primitive) count)) source value →
    (∃ fits, CheckedFixedStorageResult heap primitive count value base frame cursor machine source fits) ∨
    (¬ cursor.val + max 1 count < W ∧ run (checkedFixedStorageCode count) (machine.push (.slot source)) = .revert)
end Solidity.Backend.MemoryCopies
