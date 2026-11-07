import Solidity.Backend.MemoryCopies.MemoryParentSnapshot
import Solidity.Backend.MemoryCopies.NestedMemoryLoop
import Solidity.Backend.MemoryCopies.NestedStorageParent

/-! Actual source-header loading, checked reservation, existing child traversal
and typed parent adoption. This fixes nested dynamic primitive-array copying,
not Source entry selection or arbitrary recursive graph compilation. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def nestedMemoryParentBody (primitive : PrimTy) : List Instr := referenceCapacityGuard 0 ++
  (Objects.nestedPrefix ++ (nestedMemoryLoopCode primitive ++ nestedStorageParentExit))

def nestedMemoryParentCode (primitive : PrimTy) : List Instr := [.dup 1, .mloadAt] ++ nestedMemoryParentBody primitive

def memoryParentDemand {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive))))) : Nat :=
  nestedStorageParentDemand (memoryChildRows heap primitive source)

def NestedMemoryParentResult {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive))))) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine)
    (fits : cursor.val + memoryParentDemand heap primitive source < W) : Prop :=
  let snapshot := MVal.copyMToSt heap (T := .ref (.array (.ref (.array (.prim primitive))))) source
  let grown := snapshot.copyStToM heap rfl
  ∃ base' target,
    run (nestedMemoryParentCode primitive) (machine.push (.val (base source.id))) = .ok (target.push (.val cursor)) 0 ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + memoryParentDemand heap primitive source, fits⟩ target ∧
    base' grown.val.id = cursor ∧ BaseExtends H base base' ∧ target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
    (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
    Heap.Keeps grown.ext heap grown.heap ∧ H.length ≤ grown.val.id ∧
    grown.heap.len grown.val .dyn = heap.len source .dyn ∧ MVal.copyMToSt grown.heap grown.val = snapshot.strip ∧
    MVal.copyMToSt grown.heap (T := .ref (.array (.ref (.array (.prim primitive))))) (source.wk grown.ext) = snapshot

structure NestedMemoryParentCertificate : Prop where
  execute : ∀ {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive))))) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine),
    Objects.AllocatorRepr heap base frame cursor machine →
    (∃ fits, NestedMemoryParentResult heap primitive source base frame cursor machine fits) ∨
    (¬ cursor.val + memoryParentDemand heap primitive source < W ∧
      run (nestedMemoryParentCode primitive) (machine.push (.val (base source.id))) = .revert)

end Solidity.Backend.MemoryCopies
