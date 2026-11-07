import Solidity.Backend.MemoryCopies.FixedMemoryCopy
import Solidity.Backend.MemoryCopies.AliasBinding

/-! Reuse the existing selected memory-pointer compiler for fresh copy leaves.
Fixed payloads remain headerless; these contracts describe intrinsic heap adoption. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def SelectedAlias.fixedDeepCode {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {b : Nat} {frag : Frag Γ}
    {path : MPath C Γ (.ref (.fixed (.prim primitive) count))} (chosen : SelectedAlias b frag path) : List Instr :=
  chosen.pointer.code ++ runtimeFixedMemoryCode count

def SelectedAlias.fixedDeepBindCode {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {b : Nat} {frag : Frag Γ}
    {path : MPath C Γ (.ref (.fixed (.prim primitive) count))} (chosen : SelectedAlias b frag path)
    (destination : Idx Γ (.mem (.fixed (.prim primitive) count))) : List Instr :=
  chosen.fixedDeepCode ++ [.mstore (cellOf b destination)]

def FixedPathRoom {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat}
    (state : State C Γ) (cursor : Fin W) (path : MPath C Γ (.ref (.fixed (.prim primitive) count))) : Prop :=
  ∀ reference, path.mvalT state = .ok reference → cursor.val + max 1 count < W

def FixedPathCopyOutcome {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat}
    (L b frame : Nat) (frag : Frag Γ) (state : State C Γ) (base : Nat → Fin W)
    (cursor : Fin W) (machine : Machine) (path : MPath C Γ (.ref (.fixed (.prim primitive) count)))
    (code : List Instr) (fits : FixedPathRoom state cursor path) : Prop :=
  (∃ reference, ∃ resolved : path.mvalT state = .ok reference,
    let grown := (MVal.copyMToSt state.heap (T := .ref (.fixed (.prim primitive) count)) reference).copyStToM state.heap rfl
    ∃ base' target,
      run code machine = .ok (target.push (.val cursor)) 0 ∧
      Objects.StateRepr L b frame frag (state.adopt grown).1 base' target ∧
      Objects.AllocatorRepr grown.heap base' frame
        ⟨cursor.val + max 1 count,fits reference resolved⟩ target ∧
      base' grown.val.id = cursor ∧ BaseExtends state.H base base' ∧ target = {machine with mem := target.mem} ∧
      (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
      (∀ lo hi, Objects.Gap state.heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
      Heap.Keeps grown.ext state.heap grown.heap ∧ reference.id < grown.val.id) ∨
  (path.mvalT state = .error .revert ∧ run code machine = .revert)

def FixedPathBindOutcome {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat}
    (L b frame : Nat) (frag : Frag Γ) (state : State C Γ) (base : Nat → Fin W)
    (cursor : Fin W) (machine : Machine) (path : MPath C Γ (.ref (.fixed (.prim primitive) count)))
    (destination : Idx Γ (.mem (.fixed (.prim primitive) count))) (code : List Instr)
    (fits : FixedPathRoom state cursor path) : Prop :=
  (∃ reference, ∃ resolved : path.mvalT state = .ok reference,
    let grown := (MVal.copyMToSt state.heap (T := .ref (.fixed (.prim primitive) count)) reference).copyStToM state.heap rfl
    let after := (state.adopt grown).1.setLocal destination (some grown.val)
    ∃ base' target,
      run code machine = .ok target 0 ∧ Objects.StateRepr L b frame frag after base' target ∧
      Objects.AllocatorRepr grown.heap base' frame
        ⟨cursor.val + max 1 count,fits reference resolved⟩ target ∧
      base' grown.val.id = cursor ∧ BaseExtends state.H base base' ∧ target.stack = machine.stack ∧
      target.mem (cellOf b destination) = .val cursor ∧
      (∀ address, 0 < address → address < cursor.val → address ≠ cellOf b destination → target.mem address = machine.mem address) ∧
      Heap.Keeps grown.ext state.heap grown.heap ∧ reference.id < grown.val.id) ∨
  (path.mvalT state = .error .revert ∧ run code machine = .revert)

structure FixedPathCopyCertificate : Prop where
  execute : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {L b frame : Nat} {frag : Frag Γ}
    {path : MPath C Γ (.ref (.fixed (.prim primitive) count))} (chosen : SelectedAlias b frag path)
    {state : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {machine : Machine},
    Objects.StateRepr L b frame frag state base machine → Objects.AllocatorRepr state.heap base frame cursor machine →
    0 < b → ∀ fits : FixedPathRoom state cursor path,
    FixedPathCopyOutcome L b frame frag state base cursor machine path chosen.fixedDeepCode fits
  bind : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {L b frame : Nat} {frag : Frag Γ}
    {path : MPath C Γ (.ref (.fixed (.prim primitive) count))} (chosen : SelectedAlias b frag path)
    {state : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {machine : Machine},
    Objects.StateRepr L b frame frag state base machine → Objects.AllocatorRepr state.heap base frame cursor machine →
    0 < b → ∀ (fits : FixedPathRoom state cursor path) (destination : Idx Γ (.mem (.fixed (.prim primitive) count))),
    FixedPathBindOutcome L b frame frag state base cursor machine path destination (chosen.fixedDeepBindCode destination) fits
end Solidity.Backend.MemoryCopies
