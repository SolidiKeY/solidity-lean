import Solidity.Backend.MemoryCopies.CanonicalSingleton

/-! A populated storage copy replaces one local binding with a fresh identity.
All earlier heap objects survive independently of which locals name them. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def canonicalRebindCode {C : Contract} {Γ : Ctx} {primitive : PrimTy} (b : Nat)
    (destination : Idx Γ (.mem (.array (.prim primitive))))
    (path : SPath C Γ (.ref (.array (.prim primitive)))) : List Instr :=
  loadedSingletonCopyCode b (canonicalSingletonExpression path) ++ [.mstore (cellOf b destination)]

def CanonicalRebindResult {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (L b frame : Nat) (frag : Frag Γ) (state : State C Γ) (base : Nat → Fin W)
    (cursor : Fin W) (machine : Machine) (destination : Idx Γ (.mem (.array (.prim primitive))))
    (path : SPath C Γ (.ref (.array (.prim primitive)))) (value : primitive.Denote)
    (fits : cursor.val + 2 < W) : Prop :=
  let grown := (singletonArrayValue primitive value).copyStToM state.heap rfl
  let after := (state.adopt grown).1.setLocal destination (some grown.val)
  ∃ base' target,
    TRun.rebindMem destination (.copy path rfl) state = .ok ⟨after,grown.ext⟩ ∧
    run (canonicalRebindCode b destination path) machine = .ok target 0 ∧
    Objects.StateRepr L b frame frag after base' target ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + 2,fits⟩ target ∧
    BaseExtends state.H base base' ∧ target.stack = machine.stack ∧
    base' grown.val.id = cursor ∧ target.mem (cellOf b destination) = .val cursor ∧
    (∀ address, 0 < address → address < cursor.val → address ≠ cellOf b destination →
      target.mem address = machine.mem address) ∧
    Heap.Keeps grown.ext state.heap grown.heap ∧
    (∀ {R : RefTy} (old : HRef state.H R), (old.wk grown.ext).id < grown.val.id)

structure CanonicalRebindCertificate : Prop where
  success : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (destination : Idx Γ (.mem (.array (.prim primitive))))
    (path : SPath C Γ (.ref (.array (.prim primitive))))
    (reference : SRef C (.ref (.array (.prim primitive)))) (value : primitive.Denote),
    Objects.StateRepr L b frame frag state base machine →
    Objects.AllocatorRepr state.heap base frame cursor machine → 0 < b →
    spathIn frag false path = true → path.resolveT state = .ok reference →
    state.storage.find reference = some (singletonArrayValue primitive value) →
    ∀ fits : cursor.val + 2 < W,
    CanonicalRebindResult L b frame frag state base cursor machine destination path value fits
  refusal : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b : Nat} {frag : Frag Γ}
    (state : State C Γ) (machine : Machine)
    (destination : Idx Γ (.mem (.array (.prim primitive))))
    (path : SPath C Γ (.ref (.array (.prim primitive)))),
    Sim C L b frag state machine → spathIn frag false path = true →
    path.resolveT state = .error .revert →
    TRun.rebindMem destination (.copy path rfl) state = .error .revert ∧
    run (canonicalRebindCode b destination path) machine = .revert
end Solidity.Backend.MemoryCopies
