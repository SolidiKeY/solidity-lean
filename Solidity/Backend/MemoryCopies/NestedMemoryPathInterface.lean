import Solidity.Backend.MemoryCopies.AliasBinding
import Solidity.Backend.MemoryCopies.NestedMemoryParent
import Solidity.Backend.MemoryCopies.NestedMemoryParentDemand

/-! Contract only for selected nested memory paths feeding the existing deep
snapshot copier. This is explicit intrinsic adoption/binding, not a new MRhs
or a claim that ordinary memory alias assignment performs a deep copy. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def SelectedAlias.nestedDeepCode {C : Contract} {Γ : Ctx} {primitive : PrimTy} {b : Nat} {frag : Frag Γ}
    {path : MPath C Γ (.ref (.array (.ref (.array (.prim primitive)))))} (chosen : SelectedAlias b frag path) : List Instr :=
  chosen.pointer.code ++ nestedMemoryParentCode primitive

def SelectedAlias.nestedDeepBindCode {C : Contract} {Γ : Ctx} {primitive : PrimTy} {b : Nat} {frag : Frag Γ}
    {path : MPath C Γ (.ref (.array (.ref (.array (.prim primitive)))))} (chosen : SelectedAlias b frag path)
    (destination : Idx Γ (.mem (.array (.ref (.array (.prim primitive)))))) : List Instr :=
  chosen.nestedDeepCode ++ [.mstore (cellOf b destination)]

def NestedMemoryPathRefusal {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (state : State C Γ) (cursor : Fin W) (machine : Machine)
    (path : MPath C Γ (.ref (.array (.ref (.array (.prim primitive)))))) (code : List Instr) : Prop :=
  (path.mvalT state = .error .revert ∧ run code machine = .revert) ∨
  (∃ reference, path.mvalT state = .ok reference ∧
    ¬ cursor.val + memoryParentDemand state.heap primitive reference < W ∧ run code machine = .revert)

def NestedMemoryPathSuccess {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (L b frame : Nat) (frag : Frag Γ) (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (reference : HRef state.H (.array (.ref (.array (.prim primitive))))) (code : List Instr)
    (fits : cursor.val + memoryParentDemand state.heap primitive reference < W) : Prop :=
  let snapshot := MVal.copyMToSt state.heap (T := .ref (.array (.ref (.array (.prim primitive))))) reference
  let grown := snapshot.copyStToM state.heap rfl
  ∃ base' target,
    run code machine = .ok (target.push (.val cursor)) 0 ∧
    Objects.StateRepr L b frame frag (state.adopt grown).1 base' target ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + memoryParentDemand state.heap primitive reference,fits⟩ target ∧
    base' grown.val.id = cursor ∧ BaseExtends state.H base base' ∧ target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
    (∀ lo hi, Objects.Gap state.heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
    Heap.Keeps grown.ext state.heap grown.heap ∧ reference.id < grown.val.id ∧
    MVal.copyMToSt grown.heap grown.val = snapshot.strip ∧
    MVal.copyMToSt grown.heap (T := .ref (.array (.ref (.array (.prim primitive))))) (reference.wk grown.ext) = snapshot

def NestedMemoryPathBindSuccess {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (L b frame : Nat) (frag : Frag Γ) (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (reference : HRef state.H (.array (.ref (.array (.prim primitive)))))
    (destination : Idx Γ (.mem (.array (.ref (.array (.prim primitive)))))) (code : List Instr)
    (fits : cursor.val + memoryParentDemand state.heap primitive reference < W) : Prop :=
  let snapshot := MVal.copyMToSt state.heap (T := .ref (.array (.ref (.array (.prim primitive))))) reference
  let grown := snapshot.copyStToM state.heap rfl
  let after := (state.adopt grown).1.setLocal destination (some grown.val)
  ∃ base' target,
    run code machine = .ok target 0 ∧ Objects.StateRepr L b frame frag after base' target ∧
    Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + memoryParentDemand state.heap primitive reference,fits⟩ target ∧
    base' grown.val.id = cursor ∧ BaseExtends state.H base base' ∧ target.stack = machine.stack ∧
    target.mem (cellOf b destination) = .val cursor ∧
    (∀ address, 0 < address → address < cursor.val → address ≠ cellOf b destination → target.mem address = machine.mem address) ∧
    Heap.Keeps grown.ext state.heap grown.heap ∧ reference.id < grown.val.id ∧
    MVal.copyMToSt grown.heap grown.val = snapshot.strip ∧
    MVal.copyMToSt grown.heap (T := .ref (.array (.ref (.array (.prim primitive))))) (reference.wk grown.ext) = snapshot

structure NestedMemoryPathCertificate : Prop where
  copy : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    {path : MPath C Γ (.ref (.array (.ref (.array (.prim primitive)))))} (chosen : SelectedAlias b frag path)
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine),
    Objects.StateRepr L b frame frag state base machine → Objects.AllocatorRepr state.heap base frame cursor machine → 0 < b →
    (∃ reference, path.mvalT state = .ok reference ∧ ∃ fits,
      NestedMemoryPathSuccess L b frame frag state base cursor machine reference chosen.nestedDeepCode fits) ∨
    NestedMemoryPathRefusal state cursor machine path chosen.nestedDeepCode
  bind : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    {path : MPath C Γ (.ref (.array (.ref (.array (.prim primitive)))))} (chosen : SelectedAlias b frag path)
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (destination : Idx Γ (.mem (.array (.ref (.array (.prim primitive)))))),
    Objects.StateRepr L b frame frag state base machine → Objects.AllocatorRepr state.heap base frame cursor machine → 0 < b →
    (∃ reference, path.mvalT state = .ok reference ∧ ∃ fits,
      NestedMemoryPathBindSuccess L b frame frag state base cursor machine reference destination (chosen.nestedDeepBindCode destination) fits) ∨
    NestedMemoryPathRefusal state cursor machine path (chosen.nestedDeepBindCode destination)

end Solidity.Backend.MemoryCopies
