import Solidity.Backend.MemoryCopies.NestedStorageLive
import Solidity.Backend.MemoryCopies.LoadedArray

/-! Contract only for actual dynamic-outer storage paths, checked copy and
intrinsic declaration/rebinding transport. Existing runtime and typed local
APIs are reused; machine capacity refusal does not claim H16 Source adequacy. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def nestedStoragePathCode {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (b : Nat) (path : SPath C Γ (.ref (.array (.ref (.array (.prim primitive)))))) : List Instr :=
  compileSPath b path ++ nestedStorageHeaderCode

def NestedStoragePathResult {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (b frame : Nat) (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.array (.ref (.array (.prim primitive))))))
    (value : SVal (.ref (.array (.ref (.array (.prim primitive))))))
    (fits : cursor.val + nestedStorageParentDemand (nestedStorageLiveRows value) < W) : Prop :=
  let grown := value.copyStToM state.heap rfl
  ∃ base' target,
    run (nestedStoragePathCode b path) machine = .ok (target.push (.val cursor)) 0 ∧
    Objects.AllocatorRepr grown.heap base' frame
      ⟨cursor.val + nestedStorageParentDemand (nestedStorageLiveRows value),fits⟩ target ∧
    base' grown.val.id = cursor ∧ BaseExtends state.H base base' ∧
    target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
    (∀ lo hi, Objects.Gap state.heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
    Heap.Keeps grown.ext state.heap grown.heap ∧ state.H.length ≤ grown.val.id ∧
    grown.heap.len grown.val .dyn = (nestedStorageLiveRows value).length ∧ MVal.copyMToSt grown.heap grown.val = value.strip ∧
    heapWords grown.heap = heapWords state.heap + nestedStorageParentDemand (nestedStorageLiveRows value)


def nestedStoragePathDeclareCode {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (b : Nat) (path : SPath C Γ (.ref (.array (.ref (.array (.prim primitive)))))) : List Instr :=
  nestedStoragePathCode b path ++ [.mstore (cell (b + Γ.length))]

def NestedStoragePathDeclareResult {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (L b frame : Nat) (frag : Frag Γ) (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.array (.ref (.array (.prim primitive))))))
    (value : SVal (.ref (.array (.ref (.array (.prim primitive))))))
    (fits : cursor.val + nestedStorageParentDemand (nestedStorageLiveRows value) < W) : Prop :=
  let grown := value.copyStToM state.heap rfl
  let after := (state.adopt grown).1.push (t := .mem (.array (.ref (.array (.prim primitive))))) (some grown.val)
  ∃ base' target,
    TRun.declMem (.array (.ref (.array (.prim primitive)))) (some (.copy path rfl)) rfl state = .ok ⟨after,grown.ext⟩ ∧
    run (nestedStoragePathDeclareCode b path) machine = .ok target 0 ∧
    Objects.StateRepr L b frame (frag.push (.mem (.array (.ref (.array (.prim primitive))))) .ok) after base' target ∧
    Objects.AllocatorRepr grown.heap base' frame
      ⟨cursor.val + nestedStorageParentDemand (nestedStorageLiveRows value),fits⟩ target ∧
    BaseExtends state.H base base' ∧ target.stack = machine.stack ∧ base' grown.val.id = cursor ∧
    target.mem (cell (b + Γ.length)) = .val cursor ∧
    (∀ address, 0 < address → address < cursor.val → address ≠ cell (b + Γ.length) → target.mem address = machine.mem address) ∧
    Heap.Keeps grown.ext state.heap grown.heap ∧
    MVal.copyMToSt grown.heap grown.val = value.strip


def nestedStoragePathRebindCode {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (b : Nat) (destination : Idx Γ (.mem (.array (.ref (.array (.prim primitive))))))
    (path : SPath C Γ (.ref (.array (.ref (.array (.prim primitive)))))) : List Instr :=
  nestedStoragePathCode b path ++ [.mstore (cellOf b destination)]

def NestedStoragePathRebindResult {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (L b frame : Nat) (frag : Frag Γ) (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (destination : Idx Γ (.mem (.array (.ref (.array (.prim primitive))))))
    (path : SPath C Γ (.ref (.array (.ref (.array (.prim primitive))))))
    (value : SVal (.ref (.array (.ref (.array (.prim primitive))))))
    (fits : cursor.val + nestedStorageParentDemand (nestedStorageLiveRows value) < W) : Prop :=
  let grown := value.copyStToM state.heap rfl
  let after := (state.adopt grown).1.setLocal destination (some grown.val)
  ∃ base' target,
    TRun.rebindMem destination (.copy path rfl) state = .ok ⟨after,grown.ext⟩ ∧
    run (nestedStoragePathRebindCode b destination path) machine = .ok target 0 ∧
    Objects.StateRepr L b frame frag after base' target ∧
    Objects.AllocatorRepr grown.heap base' frame
      ⟨cursor.val + nestedStorageParentDemand (nestedStorageLiveRows value),fits⟩ target ∧
    BaseExtends state.H base base' ∧ target.stack = machine.stack ∧ base' grown.val.id = cursor ∧
    target.mem (cellOf b destination) = .val cursor ∧
    (∀ address, 0 < address → address < cursor.val → address ≠ cellOf b destination → target.mem address = machine.mem address) ∧
    Heap.Keeps grown.ext state.heap grown.heap ∧
    (∀ {R : RefTy} (old : HRef state.H R), (old.wk grown.ext).id < grown.val.id) ∧
    MVal.copyMToSt grown.heap grown.val = value.strip


structure NestedStoragePathCertificate : Prop where
  copy : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.array (.ref (.array (.prim primitive))))))
    (reference : SRef C (.ref (.array (.ref (.array (.prim primitive))))))
    (value : SVal (.ref (.array (.ref (.array (.prim primitive)))))),
    Sim C L b frag state machine → Objects.AllocatorRepr state.heap base frame cursor machine →
    spathIn frag false path = true → path.resolveT state = .ok reference →
    state.storage.find reference = some value →
    (∃ fits, NestedStoragePathResult b frame state base cursor machine path value fits) ∨
    (¬ cursor.val + nestedStorageParentDemand (nestedStorageLiveRows value) < W ∧
      run (nestedStoragePathCode b path) machine = .revert)
  declare : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.array (.ref (.array (.prim primitive))))))
    (reference : SRef C (.ref (.array (.ref (.array (.prim primitive))))))
    (value : SVal (.ref (.array (.ref (.array (.prim primitive)))))),
    Objects.StateRepr L b frame frag state base machine → Objects.AllocatorRepr state.heap base frame cursor machine →
    0 < b → spathIn frag false path = true → path.resolveT state = .ok reference →
    state.storage.find reference = some value → b + (Γ.length + 1) ≤ frame →
    (∃ fits, NestedStoragePathDeclareResult L b frame frag state base cursor machine path value fits) ∨
    (¬ cursor.val + nestedStorageParentDemand (nestedStorageLiveRows value) < W ∧
      run (nestedStoragePathDeclareCode b path) machine = .revert)
  rebind : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (destination : Idx Γ (.mem (.array (.ref (.array (.prim primitive))))))
    (path : SPath C Γ (.ref (.array (.ref (.array (.prim primitive))))))
    (reference : SRef C (.ref (.array (.ref (.array (.prim primitive))))))
    (value : SVal (.ref (.array (.ref (.array (.prim primitive)))))),
    Objects.StateRepr L b frame frag state base machine → Objects.AllocatorRepr state.heap base frame cursor machine →
    0 < b → spathIn frag false path = true → path.resolveT state = .ok reference →
    state.storage.find reference = some value →
    (∃ fits, NestedStoragePathRebindResult L b frame frag state base cursor machine destination path value fits) ∨
    (¬ cursor.val + nestedStorageParentDemand (nestedStorageLiveRows value) < W ∧
      run (nestedStoragePathRebindCode b destination path) machine = .revert)

end Solidity.Backend.MemoryCopies
