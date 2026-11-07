import Solidity.Backend.MemoryCopies.FixedReferenceDeclare

/-! Contract only for checked fixed-reference local rebinding. Successful
intrinsic TRun and full object StateRepr are required. Capacity refusal remains
a machine result, not H16 Source-machine allocation-failure adequacy. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def fixedReferenceRebindCode {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat}
    (b : Nat) (destination : Idx Γ (.mem (.fixed (.ref (.array (.prim primitive))) count)))
    (path : SPath C Γ (.ref (.fixed (.ref (.array (.prim primitive))) count))) : List Instr :=
  fixedReferencePathCopyCode b path ++ [.mstore (cellOf b destination)]

def FixedReferenceRebindResult {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat}
    (L b frame : Nat) (frag : Frag Γ) (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (destination : Idx Γ (.mem (.fixed (.ref (.array (.prim primitive))) count)))
    (path : SPath C Γ (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (value : SVal (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (fits : cursor.val + fixedReferenceStorageParentDemand (fixedReferenceLiveRows value) < W) : Prop :=
  let grown := value.copyStToM state.heap rfl
  let after := (state.adopt grown).1.setLocal destination (some grown.val)
  ∃ base' target,
    TRun.rebindMem destination (.copy path rfl) state = .ok ⟨after,grown.ext⟩ ∧
    run (fixedReferenceRebindCode b destination path) machine = .ok target 0 ∧
    Objects.StateRepr L b frame frag after base' target ∧
    Objects.AllocatorRepr grown.heap base' frame
      ⟨cursor.val + fixedReferenceStorageParentDemand (fixedReferenceLiveRows value),fits⟩ target ∧
    BaseExtends state.H base base' ∧ target.stack = machine.stack ∧ base' grown.val.id = cursor ∧
    target.mem (cellOf b destination) = .val cursor ∧
    (∀ address, 0 < address → address < cursor.val → address ≠ cellOf b destination → target.mem address = machine.mem address) ∧
    Heap.Keeps grown.ext state.heap grown.heap ∧
    (∀ {R : RefTy} (old : HRef state.H R), (old.wk grown.ext).id < grown.val.id) ∧
    MVal.copyMToSt grown.heap grown.val = value.strip

structure FixedReferenceRebindCertificate : Prop where
  execute : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (destination : Idx Γ (.mem (.fixed (.ref (.array (.prim primitive))) count)))
    (path : SPath C Γ (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (reference : SRef C (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (value : SVal (.ref (.fixed (.ref (.array (.prim primitive))) count))),
    Objects.StateRepr L b frame frag state base machine → Objects.AllocatorRepr state.heap base frame cursor machine →
    0 < b → spathIn frag false path = true → path.resolveT state = .ok reference →
    state.storage.find reference = some value →
    (∃ fits, FixedReferenceRebindResult L b frame frag state base cursor machine destination path value fits) ∨
    (¬ cursor.val + fixedReferenceStorageParentDemand (fixedReferenceLiveRows value) < W ∧
      run (fixedReferenceRebindCode b destination path) machine = .revert)

end Solidity.Backend.MemoryCopies
