import Solidity.Backend.MemoryCopies.NestedMemoryPathInterface

/-! Additive contract only for gap transport across explicit selected nested
deep binding. The frozen original binding contract is unchanged. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def NestedMemoryPathFramedBindSuccess {C : Contract} {Γ : Ctx} {primitive : PrimTy}
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
    (∀ lo hi, Objects.Gap state.heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
    Heap.Keeps grown.ext state.heap grown.heap ∧ reference.id < grown.val.id ∧
    MVal.copyMToSt grown.heap grown.val = snapshot.strip ∧
    MVal.copyMToSt grown.heap (T := .ref (.array (.ref (.array (.prim primitive))))) (reference.wk grown.ext) = snapshot

structure NestedMemoryPathFrameCertificate : Prop where
  bind : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    {path : MPath C Γ (.ref (.array (.ref (.array (.prim primitive)))))} (chosen : SelectedAlias b frag path)
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (destination : Idx Γ (.mem (.array (.ref (.array (.prim primitive)))))),
    Objects.StateRepr L b frame frag state base machine → Objects.AllocatorRepr state.heap base frame cursor machine → 0 < b →
    (∃ reference, path.mvalT state = .ok reference ∧ ∃ fits,
      NestedMemoryPathFramedBindSuccess L b frame frag state base cursor machine reference destination (chosen.nestedDeepBindCode destination) fits) ∨
    NestedMemoryPathRefusal state cursor machine path (chosen.nestedDeepBindCode destination)

end Solidity.Backend.MemoryCopies
