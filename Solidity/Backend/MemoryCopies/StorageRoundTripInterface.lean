import Solidity.Backend.MemoryCopies.StorageMemoryPipeline
import Solidity.Evm.MemoryStorageCopyLaws

/-! Actual primitive-array copy-back after the two checked memory allocations.
The old destination is represented, original payload is copied, and old live
suffix cleanup and outside-layout framing remain visible. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def storageRoundTripCode (destination : Slot) : List Instr :=
  storageMemoryPipelineCode ++ [.push (.slot destination)] ++ memoryArrayCopyCode

def StorageRoundTripResult {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (values : List primitive.Denote) (bounded : values.length < W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (source destination : Slot) (L : Nat) (old : SVal (.ref (.array (.prim primitive))))
    (fits : cursor.val + 2*(values.length+1) < W) : Prop :=
  let value := primitiveArrayValue primitive values bounded
  let first := value.copyStToM heap rfl
  let second := (MVal.copyMToSt first.heap first.val).copyStToM first.heap rfl
  ∃ (firstFits : cursor.val + (values.length+1) < W), ∃ base' middle,
    StorageMemoryPipelineResult heap primitive values bounded base frame cursor machine source fits ∧
    run storageMemoryPipelineCode (machine.push (.slot source)) =
      .ok (middle.push (.val ⟨cursor.val+(values.length+1),firstFits⟩)) 0 ∧
    Objects.AllocatorRepr second.heap base' frame ⟨cursor.val+2*(values.length+1),fits⟩ middle ∧
    base' second.val.id = ⟨cursor.val+(values.length+1),firstFits⟩ ∧
    base' (first.val.wk second.ext).id = cursor ∧ BaseExtends H base base' ∧ first.val.id < second.val.id ∧
    let address : Fin W := ⟨cursor.val+(values.length+1),firstFits⟩
    let words := fun i => payloadWord (middle.mem (address.val+1+i))
    let final : Machine := {middle with store := arrayCopyStore middle.store destination values.length words}
    run (storageRoundTripCode destination) (machine.push (.slot source)) = .ok final 0 ∧
    run memoryArrayCopyCode ((middle.push (.val address)).push (.slot destination)) = .ok final 0 ∧
    Objects.AllocatorRepr second.heap base' frame ⟨cursor.val+2*(values.length+1),fits⟩ final ∧
    ReprAt final.store L (.ref (.array (.prim primitive))) destination (old.overlay value) ∧
    final.store destination = values.length ∧
    (∀ i, i < values.length → final.store (.data destination i) = (words i).val) ∧
    (∀ i, values.length ≤ i → i < old.view.n → final.store (.data destination i) = 0) ∧
    (∀ slot, ¬ Occ (.ref (.array (.prim primitive))) destination slot → final.store slot = machine.store slot) ∧
    final.mem = middle.mem ∧ final.stack = machine.stack ∧
    (∀ address, 0 < address → address < cursor.val → final.mem address = machine.mem address)

structure StorageRoundTripCertificate : Prop where
  execute : ∀ {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (values : List primitive.Denote) (bounded : values.length < W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (source destination : Slot) (L : Nat) (old : SVal (.ref (.array (.prim primitive)))),
    Objects.AllocatorRepr heap base frame cursor machine →
    ReprAt machine.store L (.ref (.array (.prim primitive))) source (primitiveArrayValue primitive values bounded) →
    ReprAt machine.store L (.ref (.array (.prim primitive))) destination old →
    (∃ fits, StorageRoundTripResult heap primitive values bounded base frame cursor machine source destination L old fits) ∨
    (StorageMemoryPipelineRefusal heap primitive values bounded base frame cursor machine source ∧
      run (storageRoundTripCode destination) (machine.push (.slot source)) = .revert)

end Solidity.Backend.MemoryCopies
