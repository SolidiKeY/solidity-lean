import Solidity.Backend.MemoryCopies.NestedStorageParent

/-! Actual outer storage header loading and symbolic data-base selection for
nested primitive dynamic arrays. Outer storage shadows are arbitrary. Numeric
Keccak, Source evaluation/authority and general graph selection remain open. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def nestedStorageHeaderValue (primitive : PrimTy) (rows : List (PrimitiveStorageRow primitive))
    (bounded : rows.length < W) (shadow : SList (.ref (.array (.prim primitive)))) :
    SVal (.ref (.array (.ref (.array (.prim primitive))))) :=
  .array (nestedStorageValues primitive rows) shadow bounded

def nestedStorageHeaderEnter : List Instr := [.dup 1, .sload, .swap 1, .keccakArr, .swap 1]

def nestedStorageHeaderCode : List Instr := nestedStorageHeaderEnter ++ nestedStorageParentCode

def NestedStorageHeaderResult {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (bounded : rows.length < W)
    (shadow : SList (.ref (.array (.prim primitive))))
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (source : Slot) (fits : cursor.val + nestedStorageParentDemand rows < W) : Prop :=
  let value := nestedStorageParentValue primitive rows bounded
  let grown := value.copyStToM heap rfl
  ∃ base' target,
    run nestedStorageHeaderCode (machine.push (.slot source)) = .ok (target.push (.val cursor)) 0 ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + nestedStorageParentDemand rows, fits⟩ target ∧
    base' grown.val.id = cursor ∧ BaseExtends H base base' ∧
    target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
    (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
    Heap.Keeps grown.ext heap grown.heap ∧ H.length ≤ grown.val.id ∧
    grown.heap.len grown.val .dyn = rows.length ∧ MVal.copyMToSt grown.heap grown.val = value.strip ∧
    (nestedStorageHeaderValue primitive rows bounded shadow).copyStToM heap rfl = grown

structure NestedStorageHeaderCertificate : Prop where
  execute : ∀ {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (bounded : rows.length < W)
    (shadow : SList (.ref (.array (.prim primitive))))
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (source : Slot) (L : Nat),
    Objects.AllocatorRepr heap base frame cursor machine →
    ReprAt machine.store L (.ref (.array (.ref (.array (.prim primitive))))) source
      (nestedStorageHeaderValue primitive rows bounded shadow) →
    (∃ fits, NestedStorageHeaderResult heap primitive rows bounded shadow base frame cursor machine source fits) ∨
    (¬ cursor.val + nestedStorageParentDemand rows < W ∧
      run nestedStorageHeaderCode (machine.push (.slot source)) = .revert)

end Solidity.Backend.MemoryCopies
