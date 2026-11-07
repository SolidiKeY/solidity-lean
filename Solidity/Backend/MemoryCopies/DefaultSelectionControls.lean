import Solidity.Backend.MemoryCopies.DefaultSelection
import Solidity.Evm.MemoryObjectArrayExamples

/-! Actual statement compiler choices and executions over populated ownership.
Unsupported existing shapes and missing room remain visibly separate gaps. -/
namespace Solidity.Backend.MemoryCopies.DefaultSelectionControls
open Evm Evm.Memory Semantics
private structure Input where
  contract : Contract
  context : Ctx
  frag : Frag context
  state : State contract context
  base : Nat → Fin W
  machine : Machine
  represented : Objects.StateRepr 1 1 8 frag state base machine
  allocator : Objects.AllocatorRepr state.heap base 8 ⟨40,by decide⟩ machine
private def input : Input := ⟨_,_,_,_,_,_,ObjectArrayExamples.initial_repr,ObjectArrayExamples.initial_allocator⟩
private def pairName : Name := "Pair{left:uint;flag:bool}"
private def child : RefTy := .array (.prim .uint)
private def nested : RefTy := nestedArrayType (.prim .uint) [2,3]
private def chosen (root : RefTy) (defaultable : (Ty.ref root).defaultOkS = true)
    (memory : (Ty.ref root).mapFree = true)
    (available : (ReferenceDefaults.compileDefault root memory).isSome = true) :
    SelectedDefaultDeclaration (C := input.contract) 1 input.frag root (.user "fresh") defaultable memory :=
  selectedDefaultDeclaration (C := input.contract) 1 input.frag root (.user "fresh") defaultable memory (by decide) available

theorem certificate_inhabited : DefaultSelectionCertificate := defaultSelection

theorem nested_compiler_support (dimensions : List Nat)
    (defaultable : (Ty.ref (nestedArrayType (.prim .uint) dimensions)).defaultOkS = true) :
    (Construction.compileStmt (C := input.contract) 1 input.frag
      (.declMem (nestedArrayType (.prim .uint) dimensions) (.user "fresh") none defaultable
        (nested_mapFree (.prim .uint) dimensions))).isSome = true :=
  nested_statement_selected 1 input.frag (.prim .uint) dimensions (.user "fresh") defaultable _ (by decide)

theorem fixed_struct_support (dimensions : List Nat)
    (defaultable : (Ty.ref (fixedDefaultType (.struct pairName) dimensions)).defaultOkS = true)
    (memory : (Ty.ref (fixedDefaultType (.struct pairName) dimensions)).mapFree = true) :
    (Construction.compileStmt (C := input.contract) 1 input.frag
      (.declMem (fixedDefaultType (.struct pairName) dimensions) (.user "fresh") none defaultable memory)).isSome = true :=
  fixed_statement_selected 1 input.frag (.struct pairName) dimensions (.user "fresh") defaultable memory (by decide)
    (fun proof => primitive_struct_selected pairName (by decide +kernel) proof)

theorem selected_is_actual :
    Construction.compileStmt (C := input.contract) 1 input.frag
      (.declMem nested (.user "fresh") none (by decide +kernel) (by decide +kernel)) =
      some (chosen nested (by decide +kernel) (by decide +kernel)
        (nested_selection_total (.prim .uint) [2,3] _)).compiled :=
  (chosen nested (by decide +kernel) (by decide +kernel) (nested_selection_total (.prim .uint) [2,3] _)).selected

theorem execution_cursor (root : RefTy) (defaultable : (Ty.ref root).defaultOkS = true)
    (memory : (Ty.ref root).mapFree = true)
    (available : (ReferenceDefaults.compileDefault root memory).isSome = true)
    (fits : 40 + ReferenceDefaults.defaultCells (.ref root) < W) :
    ∃ target, run (chosen root defaultable memory available).compiled.code input.machine = .ok target 0 ∧
      target.mem 0 = .val (wmod (40 + ReferenceDefaults.defaultCells (.ref root))) ∧
      target.stack = input.machine.stack := by
  have locals : 1 + frameNeedStmt
      (Stmt.declMem (C := input.contract) (Γ := input.context) root (.user "fresh") none defaultable memory) ≤ 8 := by
    change 1 + max 3 (max 4 0) ≤ 8
    decide
  obtain ⟨base',target,ran,_,stack,_,growth⟩ :=
    (chosen root defaultable memory available).execute input.state input.base input.machine input.represented locals
      (.inr ⟨by decide,⟨40,by decide⟩,input.allocator,by change 40 + ReferenceDefaults.defaultCells (.ref root) < W; exact fits⟩)
  have allocated : Objects.AllocatorRepr
      ((input.state.adopt (input.state.heap.allocDefault root memory)).1.push
        (t := .mem root) (some (input.state.heap.allocDefault root memory).val)).heap
      base' 8 ⟨40 + ReferenceDefaults.defaultCells (.ref root),fits⟩ target :=
    growth ⟨40,by decide⟩ (by decide) input.allocator
      (by change 40 + ReferenceDefaults.defaultCells (.ref root) < W; exact fits)
  exact ⟨target,ran,by simpa only [wmod_of_lt fits] using allocated.free.cell,stack⟩

theorem empty_dynamic :
    ∃ target, run (chosen (.array (.ref child)) rfl rfl (by decide +kernel)).compiled.code input.machine = .ok target 0 ∧
      target.mem 0 = w[41] ∧ target.stack = input.machine.stack :=
  execution_cursor (.array (.ref child)) rfl rfl (by decide +kernel) (by decide +kernel)

theorem nested_default :
    ∃ target, run (chosen nested (by decide +kernel) (by decide +kernel)
      (nested_selection_total (.prim .uint) [2,3] _)).compiled.code input.machine = .ok target 0 ∧
      target.mem 0 = w[54] ∧ target.stack = input.machine.stack :=
  execution_cursor nested (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

theorem empty_fixed :
    ∃ target, run (chosen (.fixed (.ref child) 0) rfl rfl (by decide +kernel)).compiled.code input.machine = .ok target 0 ∧
      target.mem 0 = w[41] ∧ target.stack = input.machine.stack :=
  execution_cursor (.fixed (.ref child) 0) rfl rfl _ (by decide +kernel)

theorem long_fixed :
    ∃ target, run (chosen (.fixed (.ref child) 64) rfl rfl (by decide +kernel)).compiled.code input.machine = .ok target 0 ∧
      target.mem 0 = w[168] ∧ target.stack = input.machine.stack :=
  execution_cursor (.fixed (.ref child) 64) rfl rfl _ (by decide +kernel)

theorem primitive_struct_default :
    ∃ target, run (chosen (.struct pairName) (by decide +kernel) (by decide +kernel)
      (primitive_struct_selected pairName (by decide +kernel) _)).compiled.code input.machine = .ok target 0 ∧
      target.mem 0 = w[42] ∧ target.stack = input.machine.stack :=
  execution_cursor (.struct pairName) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

/-- This existing unsupported reference-field shape remains an implementation gap. -/
theorem unsupported_reference_struct :
    (Construction.compileStmt (C := input.contract) 1 input.frag
      (.declMem (.struct "WithChild{items:bool[]}") (.user "fresh") none (by decide +kernel) (by decide +kernel))).isSome = false :=
  by decide +kernel

theorem zero_base_refused :
    (Construction.compileStmt (C := input.contract) 0 input.frag
      (.declMem nested (.user "fresh") none (by decide +kernel) (by decide +kernel))).isSome = false := by decide +kernel

theorem wrong_cursor_rejected (target : Machine)
    (ran : run (chosen nested (by decide +kernel) (by decide +kernel)
      (nested_selection_total (.prim .uint) [2,3] _)).compiled.code input.machine = .ok target 0) :
    target.mem 0 ≠ w[53] := by
  obtain ⟨actual,execution,cursor,_⟩ := nested_default
  rw [ran] at execution
  cases execution
  rw [cursor]
  decide

theorem skipped_code_rejected :
    ¬ ∃ target, run ([] : List Instr) input.machine = .ok target 0 ∧ target.mem 0 = w[54] := by
  rintro ⟨target,ran,cursor⟩
  cases ran
  have different : input.machine.mem 0 ≠ w[54] := by decide +kernel
  exact different cursor

#print axioms certificate_inhabited
#print axioms nested_compiler_support
#print axioms fixed_struct_support
#print axioms selected_is_actual
#print axioms execution_cursor
#print axioms empty_dynamic
#print axioms nested_default
#print axioms empty_fixed
#print axioms long_fixed
#print axioms primitive_struct_default
#print axioms unsupported_reference_struct
#print axioms zero_base_refused
#print axioms wrong_cursor_rejected
#print axioms skipped_code_rejected
end Solidity.Backend.MemoryCopies.DefaultSelectionControls
