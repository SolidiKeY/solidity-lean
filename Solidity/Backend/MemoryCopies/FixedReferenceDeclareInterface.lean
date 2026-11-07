import Solidity.Backend.MemoryCopies.FixedReferencePathCopy
import Solidity.Backend.MemoryCopies.LoadedArray

/-! Contract only for checked fixed-reference declarations. Successful actual
TRun execution and object StateRepr are required; capacity refusal is a machine
result only, pending Source allocation-failure semantics. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def fixedReferenceDeclareCode {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat}
    (b : Nat) (path : SPath C Γ (.ref (.fixed (.ref (.array (.prim primitive))) count))) : List Instr :=
  fixedReferencePathCopyCode b path ++ [.mstore (cell (b + Γ.length))]

def FixedReferenceDeclareResult {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat}
    (L b frame : Nat) (frag : Frag Γ) (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (value : SVal (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (fits : cursor.val + fixedReferenceStorageParentDemand (fixedReferenceLiveRows value) < W) : Prop :=
  let grown := value.copyStToM state.heap rfl
  let after := (state.adopt grown).1.push (t := .mem (.fixed (.ref (.array (.prim primitive))) count)) (some grown.val)
  ∃ base' target,
    TRun.declMem (.fixed (.ref (.array (.prim primitive))) count) (some (.copy path rfl)) rfl state = .ok ⟨after,grown.ext⟩ ∧
    run (fixedReferenceDeclareCode b path) machine = .ok target 0 ∧
    Objects.StateRepr L b frame (frag.push (.mem (.fixed (.ref (.array (.prim primitive))) count)) .ok) after base' target ∧
    Objects.AllocatorRepr grown.heap base' frame
      ⟨cursor.val + fixedReferenceStorageParentDemand (fixedReferenceLiveRows value),fits⟩ target ∧
    BaseExtends state.H base base' ∧ target.stack = machine.stack ∧ base' grown.val.id = cursor ∧
    target.mem (cell (b + Γ.length)) = .val cursor ∧
    (∀ address, 0 < address → address < cursor.val → address ≠ cell (b + Γ.length) → target.mem address = machine.mem address) ∧
    Heap.Keeps grown.ext state.heap grown.heap ∧
    MVal.copyMToSt grown.heap grown.val = value.strip

structure FixedReferenceDeclareCertificate : Prop where
  execute : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (reference : SRef C (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (value : SVal (.ref (.fixed (.ref (.array (.prim primitive))) count))),
    Objects.StateRepr L b frame frag state base machine → Objects.AllocatorRepr state.heap base frame cursor machine →
    0 < b → spathIn frag false path = true → path.resolveT state = .ok reference →
    state.storage.find reference = some value → b + (Γ.length + 1) ≤ frame →
    (∃ fits, FixedReferenceDeclareResult L b frame frag state base cursor machine path value fits) ∨
    (¬ cursor.val + fixedReferenceStorageParentDemand (fixedReferenceLiveRows value) < W ∧
      run (fixedReferenceDeclareCode b path) machine = .revert)

end Solidity.Backend.MemoryCopies
