import Solidity.Backend.MemoryCopies.CheckedStorageArray
import Solidity.Backend.MemoryCopies.RuntimePathArray
import Solidity.Backend.MemoryCopies.LoadedArray

/-! Existing storage-path compilation feeds checked copying. Success retains
scoped declaration/rebinding results; capacity refusal is a target outcome. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def checkedStoragePathCode {C : Contract} {Γ : Ctx} {primitive : PrimTy} (b : Nat)
    (path : SPath C Γ (.ref (.array (.prim primitive)))) : List Instr :=
  Evm.compileSPath b path ++ checkedStorageArrayCode

def checkedStoragePathDeclareCode {C : Contract} {Γ : Ctx} {primitive : PrimTy} (b : Nat)
    (path : SPath C Γ (.ref (.array (.prim primitive)))) : List Instr :=
  checkedStoragePathCode b path ++ [.mstore (cell (b + Γ.length))]

def checkedStoragePathRebindCode {C : Contract} {Γ : Ctx} {primitive : PrimTy} (b : Nat)
    (destination : Idx Γ (.mem (.array (.prim primitive))))
    (path : SPath C Γ (.ref (.array (.prim primitive)))) : List Instr :=
  checkedStoragePathCode b path ++ [.mstore (cellOf b destination)]

def CheckedStoragePathBodyResult {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (b frame : Nat) (path : SPath C Γ (.ref (.array (.prim primitive))))
    (values : List primitive.Denote) (bounded : values.length < W) (state : State C Γ)
    (base : Nat → Fin W) (cursor : Fin W) (machine : Machine) (fits : cursor.val + (values.length + 1) < W) : Prop :=
  let grown := (primitiveArrayValue primitive values bounded).copyStToM state.heap rfl
  ∃ base' target,
    run (checkedStoragePathCode b path) machine = .ok (target.push (.val cursor)) 0 ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + (values.length + 1),fits⟩ target ∧
    base' grown.val.id = cursor ∧ BaseExtends state.H base base' ∧ target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
    (∀ lo hi, Objects.Gap state.heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi)

def CheckedStoragePathDeclarationResult {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (L b frame : Nat) (frag : Frag Γ) (state : State C Γ) (base : Nat → Fin W)
    (cursor : Fin W) (machine : Machine) (path : SPath C Γ (.ref (.array (.prim primitive))))
    (values : List primitive.Denote) (bounded : values.length < W) (fits : cursor.val + (values.length + 1) < W) : Prop :=
  let grown := (primitiveArrayValue primitive values bounded).copyStToM state.heap rfl
  let after := (state.adopt grown).1.push (t := .mem (.array (.prim primitive))) (some grown.val)
  ∃ base' target,
    TRun.declMem (.array (.prim primitive)) (some (.copy path rfl)) rfl state = .ok ⟨after,grown.ext⟩ ∧
    run (checkedStoragePathDeclareCode b path) machine = .ok target 0 ∧
    Objects.StateRepr L b frame (frag.push (.mem (.array (.prim primitive))) .ok) after base' target ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + (values.length + 1),fits⟩ target ∧
    BaseExtends state.H base base' ∧ target.stack = machine.stack ∧ base' grown.val.id = cursor ∧
    target.mem (cell (b + Γ.length)) = .val cursor ∧
    (∀ address, 0 < address → address < cursor.val → address ≠ cell (b + Γ.length) → target.mem address = machine.mem address)

def CheckedStoragePathRebindResult {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (L b frame : Nat) (frag : Frag Γ) (state : State C Γ) (base : Nat → Fin W)
    (cursor : Fin W) (machine : Machine) (destination : Idx Γ (.mem (.array (.prim primitive))))
    (path : SPath C Γ (.ref (.array (.prim primitive)))) (values : List primitive.Denote)
    (bounded : values.length < W) (fits : cursor.val + (values.length + 1) < W) : Prop :=
  let grown := (primitiveArrayValue primitive values bounded).copyStToM state.heap rfl
  let after := (state.adopt grown).1.setLocal destination (some grown.val)
  ∃ base' target,
    TRun.rebindMem destination (.copy path rfl) state = .ok ⟨after,grown.ext⟩ ∧
    run (checkedStoragePathRebindCode b destination path) machine = .ok target 0 ∧
    Objects.StateRepr L b frame frag after base' target ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + (values.length + 1),fits⟩ target ∧
    BaseExtends state.H base base' ∧ target.stack = machine.stack ∧ base' grown.val.id = cursor ∧
    target.mem (cellOf b destination) = .val cursor ∧
    (∀ address, 0 < address → address < cursor.val → address ≠ cellOf b destination → target.mem address = machine.mem address) ∧
    Heap.Keeps grown.ext state.heap grown.heap ∧
    (∀ {R : RefTy} (old : HRef state.H R), (old.wk grown.ext).id < grown.val.id)

structure CheckedStoragePathCertificate : Prop where
  body : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.array (.prim primitive)))) (reference : SRef C (.ref (.array (.prim primitive))))
    (values : List primitive.Denote) (bounded : values.length < W),
    Objects.StateRepr L b frame frag state base machine → Objects.AllocatorRepr state.heap base frame cursor machine →
    spathIn frag false path = true → path.resolveT state = .ok reference →
    state.storage.find reference = some (primitiveArrayValue primitive values bounded) →
    (∃ fits, CheckedStoragePathBodyResult b frame path values bounded state base cursor machine fits) ∨
      (¬ cursor.val + (values.length + 1) < W ∧ run (checkedStoragePathCode b path) machine = .revert)
  declaration : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.array (.prim primitive)))) (reference : SRef C (.ref (.array (.prim primitive))))
    (values : List primitive.Denote) (bounded : values.length < W),
    Objects.StateRepr L b frame frag state base machine → Objects.AllocatorRepr state.heap base frame cursor machine → 0 < b →
    spathIn frag false path = true → path.resolveT state = .ok reference →
    state.storage.find reference = some (primitiveArrayValue primitive values bounded) →
    b + (Γ.length + 1) ≤ frame →
    (∃ fits, CheckedStoragePathDeclarationResult L b frame frag state base cursor machine path values bounded fits) ∨
      (¬ cursor.val + (values.length + 1) < W ∧ run (checkedStoragePathDeclareCode b path) machine = .revert)
  rebind : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (destination : Idx Γ (.mem (.array (.prim primitive))))
    (path : SPath C Γ (.ref (.array (.prim primitive)))) (reference : SRef C (.ref (.array (.prim primitive))))
    (values : List primitive.Denote) (bounded : values.length < W),
    Objects.StateRepr L b frame frag state base machine → Objects.AllocatorRepr state.heap base frame cursor machine → 0 < b →
    spathIn frag false path = true → path.resolveT state = .ok reference →
    state.storage.find reference = some (primitiveArrayValue primitive values bounded) →
    (∃ fits, CheckedStoragePathRebindResult L b frame frag state base cursor machine destination path values bounded fits) ∨
      (¬ cursor.val + (values.length + 1) < W ∧ run (checkedStoragePathRebindCode b destination path) machine = .revert)
  refusal : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b : Nat} {frag : Frag Γ}
    (state : State C Γ) (machine : Machine) (path : SPath C Γ (.ref (.array (.prim primitive)))),
    Sim C L b frag state machine → spathIn frag false path = true → path.resolveT state = .error .revert →
    (MRhs.copy path rfl).evalT state = .error .revert ∧ run (checkedStoragePathCode b path) machine = .revert
end Solidity.Backend.MemoryCopies
