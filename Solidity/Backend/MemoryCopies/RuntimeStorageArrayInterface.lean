import Solidity.Backend.MemoryCopies.PrimitiveArray
import Solidity.Evm.MemoryStorageCopyLoop

/-! Runtime header-driven storage-to-memory word copying. Reuses the existing
loop controller and allocator. Source-path compilation and size failures remain separate. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def storageReadRangeBody : List Instr :=
  [.dup 4,.dup 2,.add,.sload,.dup 4,.dup 3,.add,.mstoreAt,.push w[1],.add]

def storageReadEnter : List Instr :=
  [.dup 1,.sload,.swap 1,.keccakArr,.swap 1,.dup 1] ++ allocateArrayCode ++
    [.dup 1,.push w[1],.add,.swap 1,.swap 3,.swap 2,.push w[0]]

def runtimeStorageArrayCode : List Instr :=
  storageReadEnter ++ [.loop copyRangeCond storageReadRangeBody] ++ [.pop,.pop,.pop,.pop]

structure RuntimeStorageArrayCertificate : Prop where
  success : ∀ {H : HTy} (heap : Heap H) (primitive : PrimTy) (values : List primitive.Denote)
    (bounded : values.length < W) (base : Nat → Fin W) (frame : Nat) (cursor : Fin W)
    (machine : Machine) (source : Slot) (L : Nat),
    Objects.AllocatorRepr heap base frame cursor machine →
    ReprAt machine.store L (.ref (.array (.prim primitive))) source (primitiveArrayValue primitive values bounded) →
    ∀ fits : cursor.val + (values.length + 1) < W,
    let grown := (primitiveArrayValue primitive values bounded).copyStToM heap rfl
    ∃ base' target,
      run runtimeStorageArrayCode (machine.push (.slot source)) = .ok (target.push (.val cursor)) 0 ∧
      Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + (values.length + 1),fits⟩ target ∧
      base' grown.val.id = cursor ∧ BaseExtends H base base' ∧
      target = {machine with mem := target.mem} ∧
      (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
      (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi)
end Solidity.Backend.MemoryCopies
