import Solidity.Backend.MemoryCopies.CheckedFixedStorage
import Solidity.Backend.MemoryCopies.FixedStoragePath
import Solidity.Backend.MemoryCopies.RuntimeLiveArray

/-! Existing storage-path compilation feeds headerless fixed storage copies.
The actual Source MRhs/TRun and intrinsic copied heap remain explicit. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def checkedFixedStoragePathCode {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} (b : Nat)
    (path : SPath C Γ (.ref (.fixed (.prim primitive) count))) : List Instr :=
  Evm.compileSPath b path ++ checkedFixedStorageCode count

def checkedFixedStoragePathDeclareCode {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} (b : Nat)
    (path : SPath C Γ (.ref (.fixed (.prim primitive) count))) : List Instr :=
  checkedFixedStoragePathCode b path ++ [.mstore (cell (b + Γ.length))]

def checkedFixedStoragePathRebindCode {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} (b : Nat)
    (destination : Idx Γ (.mem (.fixed (.prim primitive) count)))
    (path : SPath C Γ (.ref (.fixed (.prim primitive) count))) : List Instr :=
  checkedFixedStoragePathCode b path ++ [.mstore (cellOf b destination)]


def CheckedFixedStoragePathBodyResult {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat}
    (b frame : Nat) (path : SPath C Γ (.ref (.fixed (.prim primitive) count)))
    (value : SVal (.ref (.fixed (.prim primitive) count))) (state : State C Γ)
    (base : Nat → Fin W) (cursor : Fin W) (machine : Machine) (fits : cursor.val + max 1 count < W) : Prop :=
  let grown := value.copyStToM state.heap rfl
  ∃ base' target,
    run (checkedFixedStoragePathCode b path) machine = .ok (target.push (.val cursor)) 0 ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + max 1 count,fits⟩ target ∧
    base' grown.val.id = cursor ∧ BaseExtends state.H base base' ∧ target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
    (∀ lo hi, Objects.Gap state.heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi)

def CheckedFixedStoragePathDeclarationResult {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat}
    (L b frame : Nat) (frag : Frag Γ) (state : State C Γ) (base : Nat → Fin W)
    (cursor : Fin W) (machine : Machine) (path : SPath C Γ (.ref (.fixed (.prim primitive) count)))
    (value : SVal (.ref (.fixed (.prim primitive) count))) (fits : cursor.val + max 1 count < W) : Prop :=
  let grown := value.copyStToM state.heap rfl
  let after := (state.adopt grown).1.push (t := .mem (.fixed (.prim primitive) count)) (some grown.val)
  ∃ base' target,
    TRun.declMem (.fixed (.prim primitive) count) (some (.copy path rfl)) rfl state = .ok ⟨after,grown.ext⟩ ∧
    run (checkedFixedStoragePathDeclareCode b path) machine = .ok target 0 ∧
    Objects.StateRepr L b frame (frag.push (.mem (.fixed (.prim primitive) count)) .ok) after base' target ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + max 1 count,fits⟩ target ∧
    BaseExtends state.H base base' ∧ target.stack = machine.stack ∧ base' grown.val.id = cursor ∧
    target.mem (cell (b + Γ.length)) = .val cursor ∧
    (∀ address, 0 < address → address < cursor.val → address ≠ cell (b + Γ.length) → target.mem address = machine.mem address)

def CheckedFixedStoragePathRebindResult {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat}
    (L b frame : Nat) (frag : Frag Γ) (state : State C Γ) (base : Nat → Fin W)
    (cursor : Fin W) (machine : Machine) (destination : Idx Γ (.mem (.fixed (.prim primitive) count)))
    (path : SPath C Γ (.ref (.fixed (.prim primitive) count))) (value : SVal (.ref (.fixed (.prim primitive) count))) (fits : cursor.val + max 1 count < W) : Prop :=
  let grown := value.copyStToM state.heap rfl
  let after := (state.adopt grown).1.setLocal destination (some grown.val)
  ∃ base' target,
    TRun.rebindMem destination (.copy path rfl) state = .ok ⟨after,grown.ext⟩ ∧
    run (checkedFixedStoragePathRebindCode b destination path) machine = .ok target 0 ∧
    Objects.StateRepr L b frame frag after base' target ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + max 1 count,fits⟩ target ∧
    BaseExtends state.H base base' ∧ target.stack = machine.stack ∧ base' grown.val.id = cursor ∧
    target.mem (cellOf b destination) = .val cursor ∧
    (∀ address, 0 < address → address < cursor.val → address ≠ cellOf b destination → target.mem address = machine.mem address) ∧
    Heap.Keeps grown.ext state.heap grown.heap ∧
    (∀ {R : RefTy} (old : HRef state.H R), (old.wk grown.ext).id < grown.val.id)

structure CheckedFixedStoragePathCertificate : Prop where
  body : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.fixed (.prim primitive) count))) (reference : SRef C (.ref (.fixed (.prim primitive) count)))
    (value : SVal (.ref (.fixed (.prim primitive) count))),
    Objects.StateRepr L b frame frag state base machine → Objects.AllocatorRepr state.heap base frame cursor machine →
    spathIn frag false path = true → path.resolveT state = .ok reference → state.storage.find reference = some value →
    (∃ fits, CheckedFixedStoragePathBodyResult b frame path value state base cursor machine fits) ∨
      (¬ cursor.val + max 1 count < W ∧ run (checkedFixedStoragePathCode b path) machine = .revert)
  declaration : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.fixed (.prim primitive) count))) (reference : SRef C (.ref (.fixed (.prim primitive) count)))
    (value : SVal (.ref (.fixed (.prim primitive) count))),
    Objects.StateRepr L b frame frag state base machine → Objects.AllocatorRepr state.heap base frame cursor machine → 0 < b →
    spathIn frag false path = true → path.resolveT state = .ok reference → state.storage.find reference = some value →
    b + (Γ.length + 1) ≤ frame →
    (∃ fits, CheckedFixedStoragePathDeclarationResult L b frame frag state base cursor machine path value fits) ∨
      (¬ cursor.val + max 1 count < W ∧ run (checkedFixedStoragePathDeclareCode b path) machine = .revert)
  rebind : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (destination : Idx Γ (.mem (.fixed (.prim primitive) count)))
    (path : SPath C Γ (.ref (.fixed (.prim primitive) count))) (reference : SRef C (.ref (.fixed (.prim primitive) count)))
    (value : SVal (.ref (.fixed (.prim primitive) count))),
    Objects.StateRepr L b frame frag state base machine → Objects.AllocatorRepr state.heap base frame cursor machine → 0 < b →
    spathIn frag false path = true → path.resolveT state = .ok reference → state.storage.find reference = some value →
    (∃ fits, CheckedFixedStoragePathRebindResult L b frame frag state base cursor machine destination path value fits) ∨
      (¬ cursor.val + max 1 count < W ∧ run (checkedFixedStoragePathRebindCode b destination path) machine = .revert)
  refusal : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {L b : Nat} {frag : Frag Γ}
    (state : State C Γ) (machine : Machine) (path : SPath C Γ (.ref (.fixed (.prim primitive) count))),
    Sim C L b frag state machine → spathIn frag false path = true → path.resolveT state = .error .revert →
    (MRhs.copy path rfl).evalT state = .error .revert ∧ run (checkedFixedStoragePathCode b path) machine = .revert
end Solidity.Backend.MemoryCopies
