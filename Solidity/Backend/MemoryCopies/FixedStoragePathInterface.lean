import Solidity.Backend.MemoryCopies.FixedStorageCopy
import Solidity.Backend.MemoryCopies.RuntimeLiveArray

/-! Existing storage-path compilation feeds headerless fixed storage copies.
The actual Source MRhs/TRun and intrinsic copied heap remain explicit. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def fixedStoragePathCode {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} (b : Nat)
    (path : SPath C Γ (.ref (.fixed (.prim primitive) count))) : List Instr :=
  Evm.compileSPath b path ++ runtimeFixedStorageCode count

def fixedStoragePathDeclareCode {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} (b : Nat)
    (path : SPath C Γ (.ref (.fixed (.prim primitive) count))) : List Instr :=
  fixedStoragePathCode b path ++ [.mstore (cell (b + Γ.length))]

def fixedStoragePathRebindCode {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} (b : Nat)
    (destination : Idx Γ (.mem (.fixed (.prim primitive) count)))
    (path : SPath C Γ (.ref (.fixed (.prim primitive) count))) : List Instr :=
  fixedStoragePathCode b path ++ [.mstore (cellOf b destination)]


def FixedStoragePathBodyResult {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat}
    (b frame : Nat) (path : SPath C Γ (.ref (.fixed (.prim primitive) count)))
    (value : SVal (.ref (.fixed (.prim primitive) count))) (state : State C Γ)
    (base : Nat → Fin W) (cursor : Fin W) (machine : Machine) (fits : cursor.val + max 1 count < W) : Prop :=
  let grown := value.copyStToM state.heap rfl
  ∃ base' target,
    run (fixedStoragePathCode b path) machine = .ok (target.push (.val cursor)) 0 ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + max 1 count,fits⟩ target ∧
    base' grown.val.id = cursor ∧ BaseExtends state.H base base' ∧ target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
    (∀ lo hi, Objects.Gap state.heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi)

def FixedStoragePathDeclarationResult {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat}
    (L b frame : Nat) (frag : Frag Γ) (state : State C Γ) (base : Nat → Fin W)
    (cursor : Fin W) (machine : Machine) (path : SPath C Γ (.ref (.fixed (.prim primitive) count)))
    (value : SVal (.ref (.fixed (.prim primitive) count))) (fits : cursor.val + max 1 count < W) : Prop :=
  let grown := value.copyStToM state.heap rfl
  let after := (state.adopt grown).1.push (t := .mem (.fixed (.prim primitive) count)) (some grown.val)
  ∃ base' target,
    TRun.declMem (.fixed (.prim primitive) count) (some (.copy path rfl)) rfl state = .ok ⟨after,grown.ext⟩ ∧
    run (fixedStoragePathDeclareCode b path) machine = .ok target 0 ∧
    Objects.StateRepr L b frame (frag.push (.mem (.fixed (.prim primitive) count)) .ok) after base' target ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + max 1 count,fits⟩ target ∧
    BaseExtends state.H base base' ∧ target.stack = machine.stack ∧ base' grown.val.id = cursor ∧
    target.mem (cell (b + Γ.length)) = .val cursor ∧
    (∀ address, 0 < address → address < cursor.val → address ≠ cell (b + Γ.length) → target.mem address = machine.mem address)

def FixedStoragePathRebindResult {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat}
    (L b frame : Nat) (frag : Frag Γ) (state : State C Γ) (base : Nat → Fin W)
    (cursor : Fin W) (machine : Machine) (destination : Idx Γ (.mem (.fixed (.prim primitive) count)))
    (path : SPath C Γ (.ref (.fixed (.prim primitive) count))) (value : SVal (.ref (.fixed (.prim primitive) count))) (fits : cursor.val + max 1 count < W) : Prop :=
  let grown := value.copyStToM state.heap rfl
  let after := (state.adopt grown).1.setLocal destination (some grown.val)
  ∃ base' target,
    TRun.rebindMem destination (.copy path rfl) state = .ok ⟨after,grown.ext⟩ ∧
    run (fixedStoragePathRebindCode b destination path) machine = .ok target 0 ∧
    Objects.StateRepr L b frame frag after base' target ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + max 1 count,fits⟩ target ∧
    BaseExtends state.H base base' ∧ target.stack = machine.stack ∧ base' grown.val.id = cursor ∧
    target.mem (cellOf b destination) = .val cursor ∧
    (∀ address, 0 < address → address < cursor.val → address ≠ cellOf b destination → target.mem address = machine.mem address) ∧
    Heap.Keeps grown.ext state.heap grown.heap ∧
    (∀ {R : RefTy} (old : HRef state.H R), (old.wk grown.ext).id < grown.val.id)

structure FixedStoragePathCertificate : Prop where
  body : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.fixed (.prim primitive) count))) (reference : SRef C (.ref (.fixed (.prim primitive) count)))
    (value : SVal (.ref (.fixed (.prim primitive) count))),
    Objects.StateRepr L b frame frag state base machine → Objects.AllocatorRepr state.heap base frame cursor machine →
    spathIn frag false path = true → path.resolveT state = .ok reference →
    state.storage.find reference = some value →
    ∀ fits : cursor.val + max 1 count < W,
    FixedStoragePathBodyResult b frame path value state base cursor machine fits
  declaration : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.fixed (.prim primitive) count))) (reference : SRef C (.ref (.fixed (.prim primitive) count)))
    (value : SVal (.ref (.fixed (.prim primitive) count))),
    Objects.StateRepr L b frame frag state base machine → Objects.AllocatorRepr state.heap base frame cursor machine → 0 < b →
    spathIn frag false path = true → path.resolveT state = .ok reference →
    state.storage.find reference = some value →
    ∀ fits : cursor.val + max 1 count < W, b + (Γ.length + 1) ≤ frame →
    FixedStoragePathDeclarationResult L b frame frag state base cursor machine path value fits
  rebind : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (destination : Idx Γ (.mem (.fixed (.prim primitive) count)))
    (path : SPath C Γ (.ref (.fixed (.prim primitive) count))) (reference : SRef C (.ref (.fixed (.prim primitive) count)))
    (value : SVal (.ref (.fixed (.prim primitive) count))),
    Objects.StateRepr L b frame frag state base machine → Objects.AllocatorRepr state.heap base frame cursor machine → 0 < b →
    spathIn frag false path = true → path.resolveT state = .ok reference →
    state.storage.find reference = some value →
    ∀ fits : cursor.val + max 1 count < W,
    FixedStoragePathRebindResult L b frame frag state base cursor machine destination path value fits
  refusal : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {L b : Nat} {frag : Frag Γ}
    (state : State C Γ) (machine : Machine) (path : SPath C Γ (.ref (.fixed (.prim primitive) count))),
    Sim C L b frag state machine → spathIn frag false path = true → path.resolveT state = .error .revert →
    (MRhs.copy path rfl).evalT state = .error .revert ∧ run (fixedStoragePathCode b path) machine = .revert
end Solidity.Backend.MemoryCopies
