import Solidity.Backend.Passes.PreservedAllocatorControls

/-! Guard assuming a nonidentity object pass preserved the allocator without
an actual reached mapped prefix, or choosing allocator maps after caller tails.
Reuse existing object preservation and budgeted construction/memory links. -/
namespace Solidity.Backend.Passes.AuditPreservedAllocator
open Evm Evm.Memory Evm.Compiler
open Solidity.Backend.Passes
open HeapBoundaryControls

theorem joint :
    (Compilation.construction allocation).Input 1 8 base initial machine ∧
    PreservedAllocatorControls.suffixProgram.run second.st =
      .ok PreservedAllocatorControls.suffixOut ∧
    (∃ (selected : Nat → Fin W) (middle : Machine),
      MappedOutput (.construction allocation) 1 8 base initial {machine with stack := []}
        first.st middle selected) := by
  refine ⟨HeapBoundaryControls.input,PreservedAllocatorControls.suffix_source,?_⟩
  obtain ⟨mb,nb,ob,mid,next,final,_,runs⟩ := PreservedAllocatorControls.shared
  rcases runs [] with ⟨_,_,_,_,_,mapped,_,_⟩
  exact ⟨mb,{mid with stack := []},mapped⟩
def suffix_source := @Solidity.Backend.Passes.PreservedAllocatorControls.suffix_source
def suffix_cost := @Solidity.Backend.Passes.PreservedAllocatorControls.suffix_cost
def memory_cost := @Solidity.Backend.Passes.PreservedAllocatorControls.memory_cost
def object_code := @Solidity.Backend.Passes.PreservedAllocatorControls.object_code
def suffix_codes := @Solidity.Backend.Passes.PreservedAllocatorControls.suffix_codes
def reached_allocator := @Solidity.Backend.Passes.PreservedAllocatorControls.reached_allocator
def reached_link := @Solidity.Backend.Passes.PreservedAllocatorControls.reached_link
def reached_memory_link := @Solidity.Backend.Passes.PreservedAllocatorControls.reached_memory_link
def shared := @Solidity.Backend.Passes.PreservedAllocatorControls.shared

/-- info: 'Solidity.Backend.Passes.AuditPreservedAllocator.joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPreservedAllocator.joint

/-- info: 'Solidity.Backend.Passes.AuditPreservedAllocator.suffix_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPreservedAllocator.suffix_source

/-- info: 'Solidity.Backend.Passes.AuditPreservedAllocator.suffix_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPreservedAllocator.suffix_cost

/-- info: 'Solidity.Backend.Passes.AuditPreservedAllocator.memory_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPreservedAllocator.memory_cost

/-- info: 'Solidity.Backend.Passes.AuditPreservedAllocator.object_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPreservedAllocator.object_code

/-- info: 'Solidity.Backend.Passes.AuditPreservedAllocator.suffix_codes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPreservedAllocator.suffix_codes

/-- info: 'Solidity.Backend.Passes.AuditPreservedAllocator.reached_allocator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPreservedAllocator.reached_allocator

/-- info: 'Solidity.Backend.Passes.AuditPreservedAllocator.reached_link' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPreservedAllocator.reached_link

/-- info: 'Solidity.Backend.Passes.AuditPreservedAllocator.reached_memory_link' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPreservedAllocator.reached_memory_link

/-- info: 'Solidity.Backend.Passes.AuditPreservedAllocator.shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditPreservedAllocator.shared

macro "preservedAllocatorPrivate%" n:ident : term =>
  pure (Lean.mkIdentFrom n ((Lean.Name.num `_private.Solidity.Backend.Passes.PreservedAllocatorControls 0) ++
    `Solidity.Backend.Passes.PreservedAllocatorControls ++ n.getId))
example : (PreservedAllocatorControls.suffixProgram.run second.st).toOption.isSome = true :=
  preservedAllocatorPrivate% suffix_some

/-- info: _private.Solidity.Backend.Passes.PreservedAllocatorControls.0.Solidity.Backend.Passes.PreservedAllocatorControls.suffix_some: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
run_cmd do
  let name := (Lean.Name.num `_private.Solidity.Backend.Passes.PreservedAllocatorControls 0) ++
    `Solidity.Backend.Passes.PreservedAllocatorControls.suffix_some
  let axes ← Lean.collectAxioms name
  Lean.logInfo m!"{name}: {axes}"
end Solidity.Backend.Passes.AuditPreservedAllocator
