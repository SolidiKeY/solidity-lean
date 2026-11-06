import Solidity.Backend.MemoryCopies.FixedReferenceLive
import Solidity.Backend.MemoryCopies.NestedStorageHeader

/-! Contract only for actual dynamic outer arrays with arbitrary retained
outer and primitive-child shadows. Runtime execution reuses the existing
header-driven checked copier, without Source/physical/gas adequacy claims. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def nestedStorageLiveRows {primitive : PrimTy}
    (value : SVal (.ref (.array (.ref (.array (.prim primitive)))))) : List (PrimitiveStorageRow primitive) :=
  value.view.elems.toList.map fixedReferenceLiveRow

def nestedStorageLiveCanonical {primitive : PrimTy} :
    SVal (.ref (.array (.ref (.array (.prim primitive))))) → SVal (.ref (.array (.ref (.array (.prim primitive)))))
  | .array elements _ bounded =>
      .array (SVec.ofLen fixedReferenceLiveChild _ elements.toList (SVec.length_toList elements)) .nil bounded

def NestedStorageLiveResult {H : HTy} {primitive : PrimTy} (heap : Heap H)
    (value : SVal (.ref (.array (.ref (.array (.prim primitive))))))
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot)
    (fits : cursor.val + nestedStorageParentDemand (nestedStorageLiveRows value) < W) : Prop :=
  let grown := value.copyStToM heap rfl
  ∃ base' target,
    run nestedStorageHeaderCode (machine.push (.slot source)) = .ok (target.push (.val cursor)) 0 ∧
    Objects.AllocatorRepr grown.heap base' frame
      ⟨cursor.val + nestedStorageParentDemand (nestedStorageLiveRows value),fits⟩ target ∧
    base' grown.val.id = cursor ∧ BaseExtends H base base' ∧ target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
    (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
    Heap.Keeps grown.ext heap grown.heap ∧ H.length ≤ grown.val.id ∧
    grown.heap.len grown.val .dyn = (nestedStorageLiveRows value).length ∧
    MVal.copyMToSt grown.heap grown.val = value.strip

structure NestedStorageLiveCertificate : Prop where
  bounded : ∀ {primitive : PrimTy} (value : SVal (.ref (.array (.ref (.array (.prim primitive)))))),
    (nestedStorageLiveRows value).length < W
  copying : ∀ {H : HTy} {primitive : PrimTy} (value : SVal (.ref (.array (.ref (.array (.prim primitive)))))) (heap : Heap H),
    value.copyStToM heap rfl = (nestedStorageLiveCanonical value).copyStToM heap rfl
  representation : ∀ {primitive : PrimTy} (value : SVal (.ref (.array (.ref (.array (.prim primitive))))))
    (store : WordStore) (L : Nat) (source : Slot),
    ReprAt store L (.ref (.array (.ref (.array (.prim primitive))))) source value →
    ReprAt store L (.ref (.array (.ref (.array (.prim primitive))))) source (nestedStorageLiveCanonical value)
  execute : ∀ {H : HTy} {primitive : PrimTy} (heap : Heap H)
    (value : SVal (.ref (.array (.ref (.array (.prim primitive))))))
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot) (L : Nat),
    Objects.AllocatorRepr heap base frame cursor machine →
    ReprAt machine.store L (.ref (.array (.ref (.array (.prim primitive))))) source value →
    (∃ fits, NestedStorageLiveResult heap value base frame cursor machine source fits) ∨
    (¬ cursor.val + nestedStorageParentDemand (nestedStorageLiveRows value) < W ∧
      run nestedStorageHeaderCode (machine.push (.slot source)) = .revert)

end Solidity.Backend.MemoryCopies
