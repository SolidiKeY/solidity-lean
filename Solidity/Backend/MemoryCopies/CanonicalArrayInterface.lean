import Solidity.Backend.MemoryCopies.LoadedArray
import Solidity.Theory.Typed.Leaves

/-! The copied path and finite count select every existing typed index read.
A separate existing path check also executes for an empty selected array. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def canonicalArrayExpression {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (path : SPath C Γ (.ref (.array (.prim primitive)))) (index : Fin W) : Val C Γ primitive :=
  .read (.index (.arr .dyn) path (.simple (.lit (indexValue index).val (indexValue index).property)))

def canonicalArrayExpressions {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (path : SPath C Γ (.ref (.array (.prim primitive)))) (count : Nat) (bounded : count < W) : List (Val C Γ primitive) :=
  List.ofFn (fun index : Fin count => canonicalArrayExpression path ⟨index.val,Nat.lt_trans index.isLt bounded⟩)

def canonicalArrayGuardCode {C : Contract} {Γ : Ctx} {primitive : PrimTy} (b : Nat)
    (path : SPath C Γ (.ref (.array (.prim primitive)))) : List Instr := Evm.compileSPath b path ++ [.pop]

def canonicalArrayCode {C : Contract} {Γ : Ctx} {primitive : PrimTy} (b : Nat)
    (path : SPath C Γ (.ref (.array (.prim primitive)))) (count : Nat) (bounded : count < W) : List Instr :=
  canonicalArrayGuardCode b path ++ loadedArrayDeclareCode b (canonicalArrayExpressions path count bounded)

def CanonicalArrayResult {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (L b frame : Nat) (frag : Frag Γ) (state : State C Γ) (base : Nat → Fin W)
    (cursor : Fin W) (machine : Machine) (path : SPath C Γ (.ref (.array (.prim primitive))))
    (values : List primitive.Denote) (bounded : values.length < W)
    (fits : cursor.val + (values.length + 1) < W) : Prop :=
  let grown := (primitiveArrayValue primitive values bounded).copyStToM state.heap rfl
  let after := (state.adopt grown).1.push (t := .mem (.array (.prim primitive))) (some grown.val)
  ∃ base' target,
    TRun.declMem (.array (.prim primitive)) (some (.copy path rfl)) rfl state = .ok ⟨after,grown.ext⟩ ∧
    run (canonicalArrayCode b path values.length bounded) machine = .ok target 0 ∧
    Objects.StateRepr L b frame (frag.push (.mem (.array (.prim primitive))) .ok) after base' target ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + (values.length + 1),fits⟩ target ∧
    BaseExtends state.H base base' ∧ target.stack = machine.stack ∧
    base' grown.val.id = cursor ∧ target.mem (cell (b + Γ.length)) = .val cursor ∧
    (∀ address, 0 < address → address < cursor.val → address ≠ cell (b + Γ.length) → target.mem address = machine.mem address)

structure CanonicalArrayCertificate : Prop where
  inputs : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} (frag : Frag Γ) (state : State C Γ)
    (path : SPath C Γ (.ref (.array (.prim primitive)))) (reference : SRef C (.ref (.array (.prim primitive))))
    (values : List primitive.Denote) (bounded : values.length < W),
    spathIn frag false path = true → path.resolveT state = .ok reference →
    state.storage.find reference = some (primitiveArrayValue primitive values bounded) →
    PrimitiveLoadInputs frag state (canonicalArrayExpressions path values.length bounded) values
  declaration : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.array (.prim primitive)))) (reference : SRef C (.ref (.array (.prim primitive))))
    (values : List primitive.Denote) (bounded : values.length < W),
    Objects.StateRepr L b frame frag state base machine →
    Objects.AllocatorRepr state.heap base frame cursor machine → 0 < b →
    spathIn frag false path = true → path.resolveT state = .ok reference →
    state.storage.find reference = some (primitiveArrayValue primitive values bounded) →
    ∀ fits : cursor.val + (values.length + 1) < W, b + (Γ.length + 1) ≤ frame →
    CanonicalArrayResult L b frame frag state base cursor machine path values bounded fits
  refusal : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b : Nat} {frag : Frag Γ}
    (state : State C Γ) (machine : Machine) (path : SPath C Γ (.ref (.array (.prim primitive))))
    (count : Nat) (bounded : count < W),
    Sim C L b frag state machine → spathIn frag false path = true → path.resolveT state = .error .revert →
    TRun.declMem (.array (.prim primitive)) (some (.copy path rfl)) rfl state = .error .revert ∧
    run (canonicalArrayCode b path count bounded) machine = .revert
end Solidity.Backend.MemoryCopies
