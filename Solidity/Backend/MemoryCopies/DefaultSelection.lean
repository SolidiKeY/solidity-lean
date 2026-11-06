import Solidity.Backend.MemoryCopies.DefaultSelectionInterface
import Solidity.Backend.MemoryCopies.NestedDefaults

/-! Prove support in the existing statement compiler and extract its actual
certificate. Execution uses the existing compiler correctness theorem. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory Semantics

theorem default_statement_selected {C : Contract} {Γ : Ctx} (b : Nat) (frag : Frag Γ)
    (root : RefTy) (name : Var) (defaultable : (Ty.ref root).defaultOkS = true)
    (memory : (Ty.ref root).mapFree = true) (positive : 0 < b)
    (available : (ReferenceDefaults.compileDefault root memory).isSome = true) :
    (Construction.compileStmt (C := C) b frag (.declMem root name none defaultable memory)).isSome = true := by
  cases older : Objects.compileStmt (C := C) b frag (.declMem root name none defaultable memory) with
  | some compiled => simp only [Construction.compileStmt,older,Option.isSome_some]
  | none =>
    cases chosen : ReferenceDefaults.compileDefault root memory with
    | none => rw [chosen] at available; cases available
    | some builder =>
      cases root with
      | array element =>
        rw [Construction.compileStmt,older,dif_pos positive]
        cases element with
        | prim primitive => rfl
        | ref child => cases child <;> rfl
      | struct structureName =>
        rw [Construction.compileStmt,older,dif_pos positive]
        change ((ReferenceDefaults.compileDefault (.struct structureName) memory).bind _).isSome = true
        rw [chosen]
        rfl
      | fixed element count =>
        rw [Construction.compileStmt,older,dif_pos positive]
        change ((ReferenceDefaults.compileDefault (.fixed element count) memory).bind _).isSome = true
        rw [chosen]
        rfl
      | mapping key value => cases memory

def defaultSelection : DefaultSelectionCertificate := ⟨default_statement_selected⟩

def selectedDefaultDeclaration {C : Contract} {Γ : Ctx} (b : Nat) (frag : Frag Γ)
    (root : RefTy) (name : Var) (defaultable : (Ty.ref root).defaultOkS = true)
    (memory : (Ty.ref root).mapFree = true) (positive : 0 < b)
    (available : (ReferenceDefaults.compileDefault root memory).isSome = true) :
    SelectedDefaultDeclaration (C := C) b frag root name defaultable memory where
  compiled := (Construction.compileStmt (C := C) b frag (.declMem root name none defaultable memory)).get
    (default_statement_selected (C := C) b frag root name defaultable memory positive available)
  selected := (Option.some_get (default_statement_selected (C := C) b frag root name defaultable memory positive available)).symm

theorem nested_statement_selected {C : Contract} {Γ : Ctx} (b : Nat) (frag : Frag Γ)
    (element : Ty) (dimensions : List Nat) (name : Var)
    (defaultable : (Ty.ref (nestedArrayType element dimensions)).defaultOkS = true)
    (memory : (Ty.ref (nestedArrayType element dimensions)).mapFree = true) (positive : 0 < b) :
    (Construction.compileStmt (C := C) b frag
      (.declMem (nestedArrayType element dimensions) name none defaultable memory)).isSome = true :=
  default_statement_selected (C := C) b frag _ name defaultable memory positive (nested_selection_total element dimensions memory)

theorem fixed_statement_selected {C : Contract} {Γ : Ctx} (b : Nat) (frag : Frag Γ)
    (root : RefTy) (dimensions : List Nat) (name : Var)
    (defaultable : (Ty.ref (fixedDefaultType root dimensions)).defaultOkS = true)
    (memory : (Ty.ref (fixedDefaultType root dimensions)).mapFree = true) (positive : 0 < b)
    (available : ∀ proof : (Ty.ref root).mapFree = true, (ReferenceDefaults.compileDefault root proof).isSome = true) :
    (Construction.compileStmt (C := C) b frag
      (.declMem (fixedDefaultType root dimensions) name none defaultable memory)).isSome = true :=
  default_statement_selected (C := C) b frag _ name defaultable memory positive (fixed_selection_total root dimensions memory available)

theorem primitive_struct_statement_selected {C : Contract} {Γ : Ctx} (b : Nat) (frag : Frag Γ)
    (name : Var) (structureName : Name) (primitive : primitiveMembers (structDef structureName) = true)
    (defaultable : (Ty.ref (.struct structureName)).defaultOkS = true)
    (memory : (Ty.ref (.struct structureName)).mapFree = true) (positive : 0 < b) :
    (Construction.compileStmt (C := C) b frag (.declMem (.struct structureName) name none defaultable memory)).isSome = true :=
  default_statement_selected (C := C) b frag _ name defaultable memory positive (primitive_struct_selected structureName primitive memory)

theorem default_statement_cost {C : Contract} {Γ : Ctx} (root : RefTy) (name : Var)
    (defaultable : (Ty.ref root).defaultOkS = true) (memory : (Ty.ref root).mapFree = true)
    (state : State C Γ) :
    Construction.allocationCostStmt (Stmt.declMem (C := C) (Γ := Γ) root name none defaultable memory) state =
      ReferenceDefaults.defaultCells (.ref root) := by cases root <;> rfl

theorem SelectedDefaultDeclaration.execute {C : Contract} {Γ : Ctx} {b : Nat} {frag : Frag Γ}
    {root : RefTy} {name : Var} {defaultable : (Ty.ref root).defaultOkS = true}
    {memory : (Ty.ref root).mapFree = true}
    (selected : SelectedDefaultDeclaration (C := C) b frag root name defaultable memory)
    {L frame : Nat} (state : State C Γ) (base : Nat → Fin W) (machine : Machine)
    (represented : Objects.StateRepr L b frame frag state base machine)
    (locals : b + frameNeedStmt (Stmt.declMem (C := C) (Γ := Γ) root name none defaultable memory) ≤ frame)
    (room : Objects.AllocationInput b frame (ReferenceDefaults.defaultCells (.ref root)) state base machine) :
    let grown := state.heap.allocDefault root memory
    let after := (state.adopt grown).1.push (t := .mem root) (some grown.val)
    ∃ base' target, run selected.compiled.code machine = .ok target 0 ∧
      Objects.StateRepr L b frame selected.compiled.frag after base' target ∧
      target.stack = machine.stack ∧ BaseExtends state.H base base' ∧
      Objects.GrowsAllocator b frame (ReferenceDefaults.defaultCells (.ref root)) state base machine after base' target := by
  have source : (Stmt.declMem root name none defaultable memory).run state =
      .ok ⟨(state.adopt (state.heap.allocDefault root memory)).1.push (t := .mem root)
        (some (state.heap.allocDefault root memory).val),(state.heap.allocDefault root memory).ext⟩ := rfl
  have actualRoom : Objects.AllocationInput b frame
      (Construction.allocationCostStmt (Stmt.declMem (C := C) (Γ := Γ) root name none defaultable memory) state)
      state base machine := by
    rw [default_statement_cost]
    exact room
  rcases selected.compiled.cert.correct represented locals actualRoom with
    ⟨out,target,base',sourceRun,targetRun,reached,stack,extension,growth⟩ | ⟨refused,_⟩
  · rw [source] at sourceRun
    cases sourceRun
    rw [default_statement_cost] at growth
    exact ⟨base',target,targetRun,reached,stack,extension,growth⟩
  · rw [source] at refused
    cases refused

#print axioms default_statement_selected
#print axioms defaultSelection
#print axioms selectedDefaultDeclaration
#print axioms nested_statement_selected
#print axioms fixed_statement_selected
#print axioms primitive_struct_statement_selected
#print axioms default_statement_cost
#print axioms SelectedDefaultDeclaration.execute
end Solidity.Backend.MemoryCopies
