import Solidity.Backend.Passes.HeapBoundaryControls

/-! Guard empty admission of a construction/reference-array/memory composition,
loss of caller-tail observations, or replacing the actual mutated heap answer.
Retain the original per-tail map quantifier order and empty-heap refutation. -/
namespace Solidity.Backend.Passes.AuditHeapBoundary
open Evm Evm.Memory Evm.Compiler
open Solidity.Backend.Passes
open HeapBoundaryControls

theorem joint :
    (Compilation.construction allocation).Input 1 8 base initial machine ∧
    allocate.run initial = .ok first ∧
    mutate.run first.st = .ok second ∧
    read.run second.st = .ok third :=
  ⟨HeapBoundaryControls.input,allocation_source,mutation_source,observation_source⟩
def empty_heap := @Solidity.Backend.Passes.HeapBoundaryControls.empty_heap
def physical := @Solidity.Backend.Passes.HeapBoundaryControls.physical
def allocator := @Solidity.Backend.Passes.HeapBoundaryControls.allocator
def cost := @Solidity.Backend.Passes.HeapBoundaryControls.cost
def input := @Solidity.Backend.Passes.HeapBoundaryControls.input
def allocation_source := @Solidity.Backend.Passes.HeapBoundaryControls.allocation_source
def mutation_source := @Solidity.Backend.Passes.HeapBoundaryControls.mutation_source
def observation_source := @Solidity.Backend.Passes.HeapBoundaryControls.observation_source
def reached_link := @Solidity.Backend.Passes.HeapBoundaryControls.reached_link
def success := @Solidity.Backend.Passes.HeapBoundaryControls.success
def source_answer := @Solidity.Backend.Passes.HeapBoundaryControls.source_answer

/-- info: 'Solidity.Backend.Passes.AuditHeapBoundary.joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditHeapBoundary.joint

/-- info: 'Solidity.Backend.Passes.AuditHeapBoundary.empty_heap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditHeapBoundary.empty_heap

/-- info: 'Solidity.Backend.Passes.AuditHeapBoundary.physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditHeapBoundary.physical

/-- info: 'Solidity.Backend.Passes.AuditHeapBoundary.allocator' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditHeapBoundary.allocator

/-- info: 'Solidity.Backend.Passes.AuditHeapBoundary.cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditHeapBoundary.cost

/-- info: 'Solidity.Backend.Passes.AuditHeapBoundary.input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditHeapBoundary.input

/-- info: 'Solidity.Backend.Passes.AuditHeapBoundary.allocation_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditHeapBoundary.allocation_source

/-- info: 'Solidity.Backend.Passes.AuditHeapBoundary.mutation_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditHeapBoundary.mutation_source

/-- info: 'Solidity.Backend.Passes.AuditHeapBoundary.observation_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditHeapBoundary.observation_source

/-- info: 'Solidity.Backend.Passes.AuditHeapBoundary.reached_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditHeapBoundary.reached_link

/-- info: 'Solidity.Backend.Passes.AuditHeapBoundary.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditHeapBoundary.success

/-- info: 'Solidity.Backend.Passes.AuditHeapBoundary.source_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditHeapBoundary.source_answer

macro "heapBoundaryPrivate%" n:ident : term =>
  pure (Lean.mkIdentFrom n ((Lean.Name.num `_private.Solidity.Backend.Passes.HeapBoundaryControls 0) ++
    `Solidity.Backend.Passes.HeapBoundaryControls ++ n.getId))
example : (allocate.run initial).toOption.isSome = true := heapBoundaryPrivate% first_some
example : (mutate.run first.st).toOption.isSome = true := heapBoundaryPrivate% second_some
example : (read.run second.st).toOption.isSome = true := heapBoundaryPrivate% third_some
example {R : RefTy} (r : HRef initial.H R) : False := (heapBoundaryPrivate% noRefs) r

theorem noRefs_premises_impossible (R : RefTy) : ¬ Nonempty (HRef initial.H R) := by
  rintro ⟨r⟩
  exact (heapBoundaryPrivate% noRefs) r

/-- info: 'Solidity.Backend.Passes.AuditHeapBoundary.noRefs_premises_impossible' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditHeapBoundary.noRefs_premises_impossible
/-- info: _private.Solidity.Backend.Passes.HeapBoundaryControls.0.Solidity.Backend.Passes.HeapBoundaryControls.first_some: [propext,
 Classical.choice,
 Quot.sound]
---
info: _private.Solidity.Backend.Passes.HeapBoundaryControls.0.Solidity.Backend.Passes.HeapBoundaryControls.second_some: [propext,
 Classical.choice,
 Quot.sound]
---
info: _private.Solidity.Backend.Passes.HeapBoundaryControls.0.Solidity.Backend.Passes.HeapBoundaryControls.third_some: [propext,
 Classical.choice,
 Quot.sound]
---
info: _private.Solidity.Backend.Passes.HeapBoundaryControls.0.Solidity.Backend.Passes.HeapBoundaryControls.noRefs: [propext] -/
#guard_msgs in
run_cmd do
  for short in [`first_some, `second_some, `third_some, `noRefs] do
    let name := (Lean.Name.num `_private.Solidity.Backend.Passes.HeapBoundaryControls 0) ++
      `Solidity.Backend.Passes.HeapBoundaryControls ++ short
    let axes ← Lean.collectAxioms name
    Lean.logInfo m!"{name}: {axes}"
end Solidity.Backend.Passes.AuditHeapBoundary
