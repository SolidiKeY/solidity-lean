import Solidity.Backend.MemoryCopies.CheckedMemoryArray
import Solidity.Backend.MemoryCopies.AliasBinding

/-! Selected pointer execution feeds checked fresh copying. Path bounds and
allocation capacity remain distinct target refusal reasons. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def SelectedAlias.checkedDeepCode {C : Contract} {Γ : Ctx} {primitive : PrimTy} {b : Nat} {frag : Frag Γ}
    {path : MPath C Γ (.ref (.array (.prim primitive)))} (chosen : SelectedAlias b frag path) : List Instr :=
  chosen.pointer.code ++ checkedMemoryArrayCode

def SelectedAlias.checkedDeepBindCode {C : Contract} {Γ : Ctx} {primitive : PrimTy} {b : Nat} {frag : Frag Γ}
    {path : MPath C Γ (.ref (.array (.prim primitive)))} (chosen : SelectedAlias b frag path)
    (destination : Idx Γ (.mem (.array (.prim primitive)))) : List Instr :=
  chosen.checkedDeepCode ++ [.mstore (cellOf b destination)]

def CheckedPathFailure {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (state : State C Γ) (cursor : Fin W) (path : MPath C Γ (.ref (.array (.prim primitive)))) : Prop :=
  path.mvalT state = .error .revert ∨ ∃ reference,
    path.mvalT state = .ok reference ∧ ¬ cursor.val + (state.heap.len reference .dyn + 1) < W

def CheckedPathCopyOutcome {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (L b frame : Nat) (frag : Frag Γ) (state : State C Γ) (base : Nat → Fin W)
    (cursor : Fin W) (machine : Machine) (path : MPath C Γ (.ref (.array (.prim primitive))))
    (code : List Instr) : Prop :=
  (∃ reference, path.mvalT state = .ok reference ∧ ∃ fits : cursor.val + (state.heap.len reference .dyn + 1) < W,
    let grown := (MVal.copyMToSt state.heap (T := .ref (.array (.prim primitive))) reference).copyStToM state.heap rfl
    ∃ base' target,
      run code machine = .ok (target.push (.val cursor)) 0 ∧
      Objects.StateRepr L b frame frag (state.adopt grown).1 base' target ∧
      Objects.AllocatorRepr grown.heap base' frame
        ⟨cursor.val + (state.heap.len reference .dyn + 1),fits⟩ target ∧
      base' grown.val.id = cursor ∧ BaseExtends state.H base base' ∧ target = {machine with mem := target.mem} ∧
      (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
      (∀ lo hi, Objects.Gap state.heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
      Heap.Keeps grown.ext state.heap grown.heap ∧ reference.id < grown.val.id) ∨
  (CheckedPathFailure state cursor path ∧ run code machine = .revert)

def CheckedPathBindOutcome {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (L b frame : Nat) (frag : Frag Γ) (state : State C Γ) (base : Nat → Fin W)
    (cursor : Fin W) (machine : Machine) (path : MPath C Γ (.ref (.array (.prim primitive))))
    (destination : Idx Γ (.mem (.array (.prim primitive)))) (code : List Instr) : Prop :=
  (∃ reference, path.mvalT state = .ok reference ∧ ∃ fits : cursor.val + (state.heap.len reference .dyn + 1) < W,
    let grown := (MVal.copyMToSt state.heap (T := .ref (.array (.prim primitive))) reference).copyStToM state.heap rfl
    let after := (state.adopt grown).1.setLocal destination (some grown.val)
    ∃ base' target,
      run code machine = .ok target 0 ∧ Objects.StateRepr L b frame frag after base' target ∧
      Objects.AllocatorRepr grown.heap base' frame
        ⟨cursor.val + (state.heap.len reference .dyn + 1),fits⟩ target ∧
      base' grown.val.id = cursor ∧ BaseExtends state.H base base' ∧ target.stack = machine.stack ∧
      target.mem (cellOf b destination) = .val cursor ∧
      (∀ address, 0 < address → address < cursor.val → address ≠ cellOf b destination → target.mem address = machine.mem address) ∧
      Heap.Keeps grown.ext state.heap grown.heap ∧ reference.id < grown.val.id) ∨
  (CheckedPathFailure state cursor path ∧ run code machine = .revert)

structure CheckedPathCopyCertificate : Prop where
  execute : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    {path : MPath C Γ (.ref (.array (.prim primitive)))} (chosen : SelectedAlias b frag path)
    {state : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {machine : Machine},
    Objects.StateRepr L b frame frag state base machine → Objects.AllocatorRepr state.heap base frame cursor machine →
    0 < b →
    CheckedPathCopyOutcome L b frame frag state base cursor machine path chosen.checkedDeepCode
  bind : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    {path : MPath C Γ (.ref (.array (.prim primitive)))} (chosen : SelectedAlias b frag path)
    {state : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {machine : Machine},
    Objects.StateRepr L b frame frag state base machine → Objects.AllocatorRepr state.heap base frame cursor machine →
    0 < b → ∀ destination : Idx Γ (.mem (.array (.prim primitive))),
    CheckedPathBindOutcome L b frame frag state base cursor machine path destination (chosen.checkedDeepBindCode destination)
end Solidity.Backend.MemoryCopies
