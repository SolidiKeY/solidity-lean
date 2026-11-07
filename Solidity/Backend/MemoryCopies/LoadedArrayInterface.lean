import Solidity.Backend.MemoryCopies.PrimitiveArray
import Solidity.Evm.Expr

/-! Finite arrays loaded by existing expression compilation before allocation.
Expression evaluation and its link to actual copied storage remain explicit. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

structure PrimitiveLoadInputs {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (frag : Frag Γ) (state : State C Γ) (expressions : List (Val C Γ primitive))
    (values : List primitive.Denote) : Prop where
  supported : ∀ expression ∈ expressions, valIn frag expression = true
  evaluation : expressions.mapM (fun expression => expression.evalT state) = .ok values

def primitiveLoadsCode {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (b : Nat) : List (Val C Γ primitive) → List Instr
  | [] => []
  | expression :: expressions => primitiveLoadsCode b expressions ++ Evm.compileVal b expression

def arrayStackCode (offset : Nat) : Nat → List Instr
  | 0 => []
  | count + 1 => [.swap 1,.dup 2] ++ writeFieldCode offset ++ arrayStackCode (offset + 1) count

def arrayFillCode (count : Nat) : List Instr :=
  [.push (.val (wmod count))] ++ allocateArrayCode ++ arrayStackCode 1 count

def loadedArrayCode {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (b : Nat) (expressions : List (Val C Γ primitive)) : List Instr :=
  primitiveLoadsCode b expressions ++ arrayFillCode expressions.length

def LoadedArrayBodyResult {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (b frame : Nat) (expressions : List (Val C Γ primitive)) (values : List primitive.Denote)
    (bounded : values.length < W) (state : State C Γ) (base : Nat → Fin W)
    (cursor : Fin W) (machine : Machine) (fits : cursor.val + (values.length + 1) < W) : Prop :=
  let grown := (primitiveArrayValue primitive values bounded).copyStToM state.heap rfl
  ∃ words base' target, PrimitiveWords primitive values words ∧
    run (loadedArrayCode b expressions) machine = .ok (target.push (.val cursor)) 0 ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + (values.length + 1),fits⟩ target ∧
    base' grown.val.id = cursor ∧ BaseExtends state.H base base' ∧
    target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
    (∀ lo hi, Objects.Gap state.heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi)

structure LoadedArrayCertificate : Prop where
  success : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (expressions : List (Val C Γ primitive)) (values : List primitive.Denote)
    (bounded : values.length < W) (state : State C Γ) (base : Nat → Fin W)
    (cursor : Fin W) (machine : Machine),
    Objects.StateRepr L b frame frag state base machine →
    Objects.AllocatorRepr state.heap base frame cursor machine →
    PrimitiveLoadInputs frag state expressions values →
    ∀ fits : cursor.val + (values.length + 1) < W,
      LoadedArrayBodyResult b frame expressions values bounded state base cursor machine fits
end Solidity.Backend.MemoryCopies
