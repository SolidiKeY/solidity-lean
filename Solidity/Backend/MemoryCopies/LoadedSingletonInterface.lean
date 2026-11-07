import Solidity.Backend.MemoryCopies.SingletonCopy

/-! A primitive load from the existing compiler precedes actual singleton-copy
allocation. Successful expression evaluation is explicit; no target run is assumed. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def singletonFillCode : List Instr :=
  [.push w[1]] ++ allocateArrayCode ++ [.swap 1,.dup 2] ++ writeFieldCode 1

def loadedSingletonCopyCode {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (base : Nat) (expression : Val C Γ primitive) : List Instr :=
  compileVal base expression ++ singletonFillCode

def LoadedSingletonBodyResult {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (b frame : Nat) (expression : Val C Γ primitive) (value : primitive.Denote)
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (fits : cursor.val + 2 < W) : Prop :=
  let grown := (singletonArrayValue primitive value).copyStToM state.heap rfl
  ∃ word base' target, ReprV primitive value word ∧
    run (loadedSingletonCopyCode b expression) machine = .ok (target.push (.val cursor)) 0 ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + 2,fits⟩ target ∧
    base' grown.val.id = cursor ∧ BaseExtends state.H base base' ∧
    target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
    (∀ lo hi, Objects.Gap state.heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi)

structure LoadedSingletonCertificate : Prop where
  success : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (expression : Val C Γ primitive) (value : primitive.Denote) (state : State C Γ)
    (base : Nat → Fin W) (cursor : Fin W) (machine : Machine),
    Objects.StateRepr L b frame frag state base machine →
    Objects.AllocatorRepr state.heap base frame cursor machine →
    valIn frag expression = true → expression.evalT state = .ok value →
    ∀ fits : cursor.val + 2 < W, LoadedSingletonBodyResult b frame expression value state base cursor machine fits
  refusal : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b : Nat} {frag : Frag Γ}
    (expression : Val C Γ primitive) (state : State C Γ) (machine : Machine),
    Sim C L b frag state machine → valIn frag expression = true → expression.evalT state = .error .revert →
    run (loadedSingletonCopyCode b expression) machine = .revert
end Solidity.Backend.MemoryCopies
