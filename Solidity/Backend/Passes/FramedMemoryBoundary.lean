import Solidity.Backend.Selection.FramedLoweringInterface
import Solidity.Backend.Passes.MemoryJoinCostControls

/-! The published scalar framed-lowering interface keeps all nonstack fields.
An actual allocating compiler pass cannot inhabit it as a whole. This is a
scope boundary, not a replacement memory/world certificate or a producer fix. -/
namespace Solidity.Backend.Passes.FramedMemoryBoundary
open Evm Evm.Memory Evm.Compiler Backend.Selection

/-- Conditional use of the exact published field. This does not construct a
framed producer or infer any machine uniqueness from representation. -/
theorem preserves_memory {ir : List Evm.Instr} {block : Backend.Block}
    (certificate : FramedLoweringCertificate ir block)
    (input : Backend.Scalar.Stack) (initial final : Machine) (skip : Nat)
    (stack : initial.stack = irStack input) (executed : run ir initial = .ok final skip) :
    final.mem = initial.mem := by
  obtain ⟨output,_,frame,_⟩ := certificate.reflect input initial final skip stack executed
  rw [frame]

/-- A real reached memory change refutes a whole-pass scalar frame certificate.
Success and numeric entry-stack alignment remain actual premises. -/
theorem changed_memory_refutes {ir : List Evm.Instr} (block : Backend.Block)
    (input : Backend.Scalar.Stack) (initial final : Machine) (skip cell : Nat)
    (stack : initial.stack = irStack input) (executed : run ir initial = .ok final skip)
    (changed : final.mem cell ≠ initial.mem cell) :
    ¬ Nonempty (FramedLoweringCertificate ir block) := by
  rintro ⟨certificate⟩
  apply changed
  rw [preserves_memory certificate input initial final skip stack executed]

open Backend.Passes.Controls.Fixture AllocatingControls MemoryJoinCost.Controls

/-- The counterexample uses publicly accepted intrinsic allocation, a real
initial Input, full reached map and preserved arbitrary saved tails. -/
theorem allocation_witness :
    Memory.compileProg 1 (Frag.init []) ReachabilityControls.populatedBuilder = some allocationStage ∧
    ReachabilityControls.populatedBuilder.run (State.init C) = .ok ⟨σ,⟨σ.H,rfl⟩⟩ ∧
    ∃ (middle : Machine) (selected : Nat → Fin W), ∀ tail,
      (Compilation.memory allocationStage).Input 1 6 initialBase (State.init C)
        {initialMachine with stack := tail} ∧
      run allocationStage.code {initialMachine with stack := tail} = .ok {middle with stack := tail} 0 ∧
      MappedOutput (.memory allocationStage) 1 6 initialBase (State.init C)
        {initialMachine with stack := tail} σ {middle with stack := tail} selected ∧
      {middle with stack := tail}.stack = tail ∧
      {initialMachine with stack := tail}.mem 0 = w[16] ∧
      {middle with stack := tail}.mem 0 = w[21] := by
  obtain ⟨middle,selected,tails⟩ := reached_budget
  refine ⟨prefix_public,ReachabilityControls.fresh_state_reaches_fixture,middle,selected,?_⟩
  intro tail
  obtain ⟨executed,mapped,cursor,_,_⟩ := tails tail
  exact ⟨compilation_input_stack (.memory allocationStage) prefix_input tail,
    executed,mapped,rfl,rfl,cursor⟩

/-- For every target block, the actual allocating IR is outside this scalar
interface. No always-revert, malformed fault or empty-acceptance witness. -/
theorem allocation_refused (block : Backend.Block) :
    ¬ Nonempty (FramedLoweringCertificate allocationStage.code block) := by
  obtain ⟨_,_,middle,_,tails⟩ := allocation_witness
  obtain ⟨_,executed,_,_,initialCursor,finalCursor⟩ := tails []
  apply changed_memory_refutes (ir := allocationStage.code) block [] {initialMachine with stack := []}
    {middle with stack := []} 0 0 rfl executed
  rw [initialCursor,finalCursor]
  decide

/-- info: 'Solidity.Backend.Passes.FramedMemoryBoundary.preserves_memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms preserves_memory
/-- info: 'Solidity.Backend.Passes.FramedMemoryBoundary.changed_memory_refutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms changed_memory_refutes
/-- info: 'Solidity.Backend.Passes.FramedMemoryBoundary.allocation_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms allocation_witness
/-- info: 'Solidity.Backend.Passes.FramedMemoryBoundary.allocation_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms allocation_refused
end Solidity.Backend.Passes.FramedMemoryBoundary
