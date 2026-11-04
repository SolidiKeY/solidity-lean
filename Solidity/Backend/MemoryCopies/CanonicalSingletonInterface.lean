import Solidity.Backend.MemoryCopies.LoadedSingleton
import Solidity.Theory.Typed.Leaves

/-! The copied storage path selects its own existing typed element expression.
Singleton lookup remains explicit; no independent expression/value link is required. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def canonicalSingletonExpression {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (path : SPath C Γ (.ref (.array (.prim primitive)))) : Val C Γ primitive :=
  .read (.index (.arr .dyn) path (.simple (.lit 0 rfl)))

def canonicalSingletonCode {C : Contract} {Γ : Ctx} {primitive : PrimTy} (b : Nat)
    (path : SPath C Γ (.ref (.array (.prim primitive)))) : List Instr :=
  loadedSingletonDeclareCode b (canonicalSingletonExpression path)

def CanonicalSingletonResult {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (L b frame : Nat) (frag : Frag Γ) (state : State C Γ) (base : Nat → Fin W)
    (cursor : Fin W) (machine : Machine) (path : SPath C Γ (.ref (.array (.prim primitive))))
    (value : primitive.Denote) (fits : cursor.val + 2 < W) : Prop :=
  let grown := (singletonArrayValue primitive value).copyStToM state.heap rfl
  let after := (state.adopt grown).1.push (t := .mem (.array (.prim primitive))) (some grown.val)
  ∃ base' target, TRun.declMem (.array (.prim primitive)) (some (.copy path rfl)) rfl state = .ok ⟨after,grown.ext⟩ ∧
    run (canonicalSingletonCode b path) machine = .ok target 0 ∧
    Objects.StateRepr L b frame (frag.push (.mem (.array (.prim primitive))) .ok) after base' target ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + 2,fits⟩ target ∧
    BaseExtends state.H base base' ∧ target.stack = machine.stack ∧
    base' grown.val.id = cursor ∧ target.mem (cell (b + Γ.length)) = .val cursor ∧
    (∀ address, 0 < address → address < cursor.val → address ≠ cell (b + Γ.length) →
      target.mem address = machine.mem address)

structure CanonicalSingletonCertificate : Prop where
  supported : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} (frag : Frag Γ)
    (path : SPath C Γ (.ref (.array (.prim primitive)))),
    spathIn frag false path = true → valIn frag (canonicalSingletonExpression path) = true
  evaluation : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (state : State C Γ) (path : SPath C Γ (.ref (.array (.prim primitive))))
    (reference : SRef C (.ref (.array (.prim primitive)))) (value : primitive.Denote),
    path.resolveT state = .ok reference → state.storage.find reference = some (singletonArrayValue primitive value) →
    (canonicalSingletonExpression path).evalT state = .ok value
  declaration : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.array (.prim primitive))))
    (reference : SRef C (.ref (.array (.prim primitive)))) (value : primitive.Denote),
    Objects.StateRepr L b frame frag state base machine →
    Objects.AllocatorRepr state.heap base frame cursor machine → 0 < b → spathIn frag false path = true →
    path.resolveT state = .ok reference → state.storage.find reference = some (singletonArrayValue primitive value) →
    ∀ fits : cursor.val + 2 < W, b + (Γ.length + 1) ≤ frame →
    CanonicalSingletonResult L b frame frag state base cursor machine path value fits
  refusal : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b : Nat} {frag : Frag Γ}
    (state : State C Γ) (machine : Machine) (path : SPath C Γ (.ref (.array (.prim primitive)))),
    Sim C L b frag state machine → spathIn frag false path = true → path.resolveT state = .error .revert →
    TRun.declMem (.array (.prim primitive)) (some (.copy path rfl)) rfl state = .error .revert ∧
      run (canonicalSingletonCode b path) machine = .revert
end Solidity.Backend.MemoryCopies
