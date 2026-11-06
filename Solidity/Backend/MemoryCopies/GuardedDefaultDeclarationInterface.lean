import Solidity.Backend.MemoryCopies.DefaultSelection
import Solidity.Backend.MemoryCopies.SelectedDefaultDemand

/-! A guard around an ACTUAL production-selected declaration, not a replacement
compiler selector. Initial representation/local-frame bounds remain explicit;
no input allocation-capacity witness is required. Source panic correspondence,
physical byte/gas adequacy and compiler-domain coverage remain separate. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def guardedDefaultDeclarationCode {C : Contract} {Γ : Ctx} {b : Nat} {frag : Frag Γ}
    {root : RefTy} {name : Var} {defaultable : (Ty.ref root).defaultOkS = true}
    {memory : (Ty.ref root).mapFree = true}
    (selected : SelectedDefaultDeclaration (C := C) b frag root name defaultable memory) : List Instr :=
  defaultCapacityGuard (ReferenceDefaults.defaultCells (.ref root)) ++ selected.compiled.code

def GuardedDefaultDeclarationSuccess {C : Contract} {Γ : Ctx} {b : Nat} {frag : Frag Γ}
    {root : RefTy} {name : Var} {defaultable : (Ty.ref root).defaultOkS = true}
    {memory : (Ty.ref root).mapFree = true}
    (selected : SelectedDefaultDeclaration (C := C) b frag root name defaultable memory)
    {L frame : Nat} (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (fits : cursor.val + ReferenceDefaults.defaultCells (.ref root) < W) : Prop :=
  let grown := state.heap.allocDefault root memory
  let after := (state.adopt grown).1.push (t := .mem root) (some grown.val)
  ∃ base' target,
    run (guardedDefaultDeclarationCode selected) machine = .ok target 0 ∧
    Objects.StateRepr L b frame selected.compiled.frag after base' target ∧
    target.stack = machine.stack ∧ BaseExtends state.H base base' ∧
    Objects.GrowsAllocator b frame (ReferenceDefaults.defaultCells (.ref root))
      state base machine after base' target ∧
    Objects.AllocatorRepr grown.heap base' frame
      ⟨cursor.val + ReferenceDefaults.defaultCells (.ref root), fits⟩ target ∧
    heapWords grown.heap = heapWords state.heap + ReferenceDefaults.defaultCells (.ref root)

structure GuardedDefaultDeclarationCertificate : Prop where
  checked : ∀ {C : Contract} {Γ : Ctx} {b : Nat} {frag : Frag Γ}
    {root : RefTy} {name : Var} {defaultable : (Ty.ref root).defaultOkS = true}
    {memory : (Ty.ref root).mapFree = true} (child : SelectedCheckedDefault root memory)
    (selected : SelectedDefaultDeclaration (C := C) b frag root name defaultable memory)
    {frame : Nat} (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine),
    Objects.AllocatorRepr state.heap base frame cursor machine →
    run (guardedDefaultDeclarationCode selected) machine =
      if cursor.val + liveWordCount (SVal.dflt (.ref root)) < W
      then run selected.compiled.code machine else .revert
  execute : ∀ {C : Contract} {Γ : Ctx} {b : Nat} {frag : Frag Γ}
    {root : RefTy} {name : Var} {defaultable : (Ty.ref root).defaultOkS = true}
    {memory : (Ty.ref root).mapFree = true} (child : SelectedCheckedDefault root memory)
    (selected : SelectedDefaultDeclaration (C := C) b frag root name defaultable memory)
    {L frame : Nat} (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine),
    Objects.StateRepr L b frame frag state base machine →
    Objects.AllocatorRepr state.heap base frame cursor machine → 0 < b →
    b + frameNeedStmt (Stmt.declMem (C := C) (Γ := Γ) root name none defaultable memory) ≤ frame →
    (∃ fits, GuardedDefaultDeclarationSuccess (L := L) (frame := frame)
      selected state base cursor machine fits) ∨
    (¬ cursor.val + ReferenceDefaults.defaultCells (.ref root) < W ∧
      run (guardedDefaultDeclarationCode selected) machine = .revert)

end Solidity.Backend.MemoryCopies
