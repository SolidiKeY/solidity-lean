import Solidity.Backend.MemoryCopies.RuntimeMemoryArray
import Solidity.Backend.MemoryCopies.AliasBinding

/-! Reuse the existing selected memory-pointer compiler for fresh copy leaves.
These contracts describe intrinsic heap adoption, not a new Source MRhs. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def SelectedAlias.deepCode {C : Contract} {Γ : Ctx} {primitive : PrimTy} {b : Nat} {frag : Frag Γ}
    {path : MPath C Γ (.ref (.array (.prim primitive)))} (chosen : SelectedAlias b frag path) : List Instr :=
  chosen.pointer.code ++ runtimeMemoryArrayCode

def SelectedAlias.deepBindCode {C : Contract} {Γ : Ctx} {primitive : PrimTy} {b : Nat} {frag : Frag Γ}
    {path : MPath C Γ (.ref (.array (.prim primitive)))} (chosen : SelectedAlias b frag path)
    (destination : Idx Γ (.mem (.array (.prim primitive)))) : List Instr :=
  chosen.deepCode ++ [.mstore (cellOf b destination)]

def MemoryPathRoom {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (state : State C Γ) (cursor : Fin W) (path : MPath C Γ (.ref (.array (.prim primitive)))) : Prop :=
  ∀ reference, path.mvalT state = .ok reference → cursor.val + (state.heap.len reference .dyn + 1) < W

def MemoryPathCopyOutcome {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (L b frame : Nat) (frag : Frag Γ) (state : State C Γ) (base : Nat → Fin W)
    (cursor : Fin W) (machine : Machine) (path : MPath C Γ (.ref (.array (.prim primitive))))
    (code : List Instr) (fits : MemoryPathRoom state cursor path) : Prop :=
  (∃ reference, ∃ resolved : path.mvalT state = .ok reference,
    let grown := (MVal.copyMToSt state.heap (T := .ref (.array (.prim primitive))) reference).copyStToM state.heap rfl
    ∃ base' target,
      run code machine = .ok (target.push (.val cursor)) 0 ∧
      Objects.StateRepr L b frame frag (state.adopt grown).1 base' target ∧
      Objects.AllocatorRepr grown.heap base' frame
        ⟨cursor.val + (state.heap.len reference .dyn + 1),fits reference resolved⟩ target ∧
      base' grown.val.id = cursor ∧ BaseExtends state.H base base' ∧ target = {machine with mem := target.mem} ∧
      (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
      (∀ lo hi, Objects.Gap state.heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
      Heap.Keeps grown.ext state.heap grown.heap ∧ reference.id < grown.val.id) ∨
  (path.mvalT state = .error .revert ∧ run code machine = .revert)

def MemoryPathBindOutcome {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (L b frame : Nat) (frag : Frag Γ) (state : State C Γ) (base : Nat → Fin W)
    (cursor : Fin W) (machine : Machine) (path : MPath C Γ (.ref (.array (.prim primitive))))
    (destination : Idx Γ (.mem (.array (.prim primitive)))) (code : List Instr)
    (fits : MemoryPathRoom state cursor path) : Prop :=
  (∃ reference, ∃ resolved : path.mvalT state = .ok reference,
    let grown := (MVal.copyMToSt state.heap (T := .ref (.array (.prim primitive))) reference).copyStToM state.heap rfl
    let after := (state.adopt grown).1.setLocal destination (some grown.val)
    ∃ base' target,
      run code machine = .ok target 0 ∧ Objects.StateRepr L b frame frag after base' target ∧
      Objects.AllocatorRepr grown.heap base' frame
        ⟨cursor.val + (state.heap.len reference .dyn + 1),fits reference resolved⟩ target ∧
      base' grown.val.id = cursor ∧ BaseExtends state.H base base' ∧ target.stack = machine.stack ∧
      target.mem (cellOf b destination) = .val cursor ∧
      (∀ address, 0 < address → address < cursor.val → address ≠ cellOf b destination → target.mem address = machine.mem address) ∧
      Heap.Keeps grown.ext state.heap grown.heap ∧ reference.id < grown.val.id) ∨
  (path.mvalT state = .error .revert ∧ run code machine = .revert)

structure MemoryPathCopyCertificate : Prop where
  execute : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    {path : MPath C Γ (.ref (.array (.prim primitive)))} (chosen : SelectedAlias b frag path)
    {state : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {machine : Machine},
    Objects.StateRepr L b frame frag state base machine → Objects.AllocatorRepr state.heap base frame cursor machine →
    0 < b → ∀ fits : MemoryPathRoom state cursor path,
    MemoryPathCopyOutcome L b frame frag state base cursor machine path chosen.deepCode fits
  bind : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    {path : MPath C Γ (.ref (.array (.prim primitive)))} (chosen : SelectedAlias b frag path)
    {state : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {machine : Machine},
    Objects.StateRepr L b frame frag state base machine → Objects.AllocatorRepr state.heap base frame cursor machine →
    0 < b → ∀ (fits : MemoryPathRoom state cursor path) (destination : Idx Γ (.mem (.array (.prim primitive)))),
    MemoryPathBindOutcome L b frame frag state base cursor machine path destination (chosen.deepBindCode destination) fits
end Solidity.Backend.MemoryCopies
