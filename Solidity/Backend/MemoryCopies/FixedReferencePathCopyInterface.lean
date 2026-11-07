import Solidity.Backend.MemoryCopies.FixedReferencePath

/-! Contract only for actual path-prefix plus checked fixed-parent copying of
arbitrary stored child shadows. The companion must inhabit it. This does not
claim Source statement execution, physical storage layout or gas adequacy. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def fixedReferencePathCopyCode {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat}
    (b : Nat) (path : SPath C Γ (.ref (.fixed (.ref (.array (.prim primitive))) count))) : List Instr :=
  compileSPath b path ++ fixedReferenceStorageParentCode count

def FixedReferencePathCopyResult {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat}
    (b frame : Nat) (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (value : SVal (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (fits : cursor.val + fixedReferenceStorageParentDemand (fixedReferenceLiveRows value) < W) : Prop :=
  let grown := value.copyStToM state.heap rfl
  ∃ base' target,
    run (fixedReferencePathCopyCode b path) machine = .ok (target.push (.val cursor)) 0 ∧
    Objects.AllocatorRepr grown.heap base' frame
      ⟨cursor.val + fixedReferenceStorageParentDemand (fixedReferenceLiveRows value),fits⟩ target ∧
    base' grown.val.id = cursor ∧ BaseExtends state.H base base' ∧
    target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
    (∀ lo hi, Objects.Gap state.heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
    Heap.Keeps grown.ext state.heap grown.heap ∧ state.H.length ≤ grown.val.id ∧
    grown.heap.len grown.val .fixed = count ∧ MVal.copyMToSt grown.heap grown.val = value.strip ∧
    heapWords grown.heap = heapWords state.heap + fixedReferenceStorageParentDemand (fixedReferenceLiveRows value)

structure FixedReferencePathCopyCertificate : Prop where
  execute : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (reference : SRef C (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (value : SVal (.ref (.fixed (.ref (.array (.prim primitive))) count))),
    Sim C L b frag state machine → Objects.AllocatorRepr state.heap base frame cursor machine →
    spathIn frag false path = true → path.resolveT state = .ok reference →
    state.storage.find reference = some value →
    (∃ fits, FixedReferencePathCopyResult b frame state base cursor machine path value fits) ∨
    (¬ cursor.val + fixedReferenceStorageParentDemand (fixedReferenceLiveRows value) < W ∧
      run (fixedReferencePathCopyCode b path) machine = .revert)

end Solidity.Backend.MemoryCopies
