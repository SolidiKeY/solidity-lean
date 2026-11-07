import Solidity.Backend.MemoryCopies.FixedMemoryCopy

/-! Headerless fixed storage copying reuses the published storage word loop.
Capacity and initial storage/allocator representation remain explicit. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def fixedStorageEnter (count : Nat) : List Instr :=
  allocateStructCode (max 1 count) ++ [.dup 1,.swap 2,.swap 1,.push (.val (wmod count)),.push w[0]]

def runtimeFixedStorageCode (count : Nat) : List Instr :=
  fixedStorageEnter count ++ [.loop copyRangeCond storageReadRangeBody] ++ [.pop,.pop,.pop,.pop]

structure FixedStorageCopyCertificate : Prop where
  success : ∀ {H : HTy} (heap : Heap H) (primitive : PrimTy) (count : Nat)
    (value : SVal (.ref (.fixed (.prim primitive) count))) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (source : Slot) (limit : Nat),
    Objects.AllocatorRepr heap base frame cursor machine →
    ReprAt machine.store limit (.ref (.fixed (.prim primitive) count)) source value →
    ∀ fits : cursor.val + max 1 count < W,
    let grown := value.copyStToM heap rfl
    ∃ base' target,
      run (runtimeFixedStorageCode count) (machine.push (.slot source)) = .ok (target.push (.val cursor)) 0 ∧
      Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + max 1 count,fits⟩ target ∧
      base' grown.val.id = cursor ∧ BaseExtends H base base' ∧ target = {machine with mem := target.mem} ∧
      (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
      (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
      Heap.Keeps grown.ext heap grown.heap ∧ (∀ {Q : RefTy} (old : HRef H Q), old.id < grown.val.id)
end Solidity.Backend.MemoryCopies
