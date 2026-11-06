import Solidity.Backend.MemoryCopies.SelectedDefaultDemand
import Solidity.Backend.MemoryCopies.CheckedReference

/-! Actual typed demand of the existing runtime reference-array constructor.
Compiler selection remains explicit. No child feasibility or capacity premise
is imposed; Source panic, physical byte layout and gas remain separate. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def referenceDefaultValue (root : RefTy) (size : Fin W) :
    SVal (.ref (.array (.ref root))) :=
  .array (SVec.replicate (SVal.dflt (.ref root)) size.val) .nil size.isLt

def referenceDefaultWords (root : RefTy) (size : Fin W) : Nat :=
  liveWordCount (referenceDefaultValue root size)

structure ReferenceDefaultDemandCertificate : Prop where
  demand : ∀ {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (selected : SelectedCheckedDefault root memory) (size : Fin W),
    referenceDefaultWords root size =
      size.val + 1 + size.val * ReferenceDefaults.defaultCells (.ref root)
  allocation : ∀ {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (selected : SelectedCheckedDefault root memory) {H : HTy} (heap : Heap H) (size : Fin W),
    heapWords (Objects.referenceArrayCopy heap root memory size).heap =
      heapWords heap + referenceDefaultWords root size
  checked : ∀ {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (selected : SelectedCheckedDefault root memory) {H : HTy} (heap : Heap H) (size : Fin W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine),
    Objects.AllocatorRepr heap base frame cursor machine →
    run (checkedReferenceCode selected) (machine.push (.val size)) =
      if cursor.val + referenceDefaultWords root size < W
      then run (Objects.referenceArrayCode selected.builder.code) (machine.push (.val size))
      else .revert

end Solidity.Backend.MemoryCopies
