import Solidity.Backend.Passes.MemoryJoinCostControls

/-! Execute the allocating suffix whose reached admission was proved by
MemoryJoinCost. Actual public selection, both maps, whole mapped output and
nine-cell allocator growth are retained over every saved stack tail. -/
namespace Solidity.Backend.Passes.MemoryJoinedAllocation
open Evm Evm.Memory Evm.Compiler
open Backend.Passes.Controls.Fixture
open AllocatingControls
open MemoryJoinCost.Controls

noncomputable def suffixOut (state : State C Γ) :
    Solidity.Out C state.H (.mem (.array (.prim .uint)) :: Γ) :=
  ⟨state.allocPush (defaultArray .uint ⟨3,by decide⟩),List.prefix_append _ _⟩

theorem suffix_source (state : State C Γ) : appendAllocation.run state = .ok (suffixOut state) := by
  have declaration : (Stmt.declMem (.array (.prim .uint)) (.user "more")
      (some (.newArr (.lit 3 rfl) rfl)) rfl rfl).run state = .ok (suffixOut state) := by
    exact newArray_decl state .uint (.lit 3 rfl) ⟨3,by decide⟩ rfl
  rw [appendAllocation,Prog.run_cons_ok declaration,Prog.run_nil]
  rfl

theorem joined_source : (ReachabilityControls.populatedBuilder.join appendAllocation).run (State.init C) =
    .ok ⟨(suffixOut σ).st,⟨(suffixOut σ).st.H,rfl⟩⟩ := by
  rw [DeferredSource.join_run]
  simp only [TRun.seq,ReachabilityControls.fresh_state_reaches_fixture,suffix_source,Except.map]

/-- No suffix execution or preservation is a premise: its actual source run
and the reached full Input provide both, through the existing certificate. -/
theorem execution :
    ∃ joined : CompiledProg 1 (Frag.init [])
      (ReachabilityControls.populatedBuilder.join appendAllocation),
      Memory.compileProg 1 (Frag.init [])
        (ReachabilityControls.populatedBuilder.join appendAllocation) = some joined ∧
      joined.cert.cost (State.init C) = 9 ∧
      ∃ (middle final : Machine) (middleBase finalBase : Nat → Fin W),
      final.stack = [] ∧
      finalBase CompileExamples.r0.id = middleBase CompileExamples.r0.id ∧
      finalBase CompileExamples.r1.id = middleBase CompileExamples.r1.id ∧ ∀ tail,
        run allocationStage.code {initialMachine with stack := tail} =
          .ok {middle with stack := tail} 0 ∧
        MappedOutput (.memory allocationStage) 1 6 initialBase (State.init C)
          {initialMachine with stack := tail} σ {middle with stack := tail} middleBase ∧
        (Compilation.memory suffixCode).Input 1 6 middleBase σ {middle with stack := tail} ∧
        run suffixCode.code {middle with stack := tail} = .ok {final with stack := tail} 0 ∧
        MappedOutput (.memory suffixCode) 1 6 middleBase σ {middle with stack := tail}
          (suffixOut σ).st {final with stack := tail} finalBase ∧
        run joined.code {initialMachine with stack := tail} = .ok {final with stack := tail} 0 ∧
        MappedOutput (.memory joined) 1 6 initialBase (State.init C)
          {initialMachine with stack := tail} (suffixOut σ).st {final with stack := tail} finalBase ∧
        {final with stack := tail}.mem 0 = w[25] := by
  obtain ⟨joined,accepted,frag,code,cost⟩ := joined_selection
  have joinedCost : joined.cert.cost (State.init C) = 9 := total_cost
  obtain ⟨middle,middleBase,prefixes⟩ := reached_budget
  have suffixInput := (prefixes []).2.2.2.1
  obtain ⟨final,finalBase,_,finalStack,suffixes⟩ := compilation_success_shared_mapped
    (.memory suffixCode) suffixInput (by rfl) (suffix_source σ)
  have suffixMapped := (suffixes []).2
  change MappedOutput _ 1 _ _ _ _ _ _ _ at suffixMapped
  refine ⟨joined,accepted,joinedCost,middle,final,middleBase,finalBase,finalStack,
    suffixMapped.2.1 CompileExamples.r0,suffixMapped.2.1 CompileExamples.r1,?_⟩
  intro tail
  rcases prefixes tail with ⟨prefixRun,prefixMapped,_,rightInput,_⟩
  obtain ⟨suffixRun,rightMapped⟩ := suffixes tail
  change MappedOutput _ 1 _ _ _ _ _ _ _ at rightMapped
  have growth := GrowsAllocator.comp prefixMapped.2.2 rightMapped.2.2
  have totalGrowth : GrowsAllocator 1 6 9 (State.init C) initialBase
      {initialMachine with stack := tail} (suffixOut σ).st finalBase {final with stack := tail} := by
    simpa only [reached_cost,suffix_cost] using growth
  have wholeMapped : MappedOutput (.memory joined) 1 6 initialBase (State.init C)
      {initialMachine with stack := tail} (suffixOut σ).st {final with stack := tail} finalBase := by
    refine ⟨?_,BaseExtends.trans ⟨σ.H,rfl⟩ prefixMapped.2.1 rightMapped.2.1,?_⟩
    · change StateRepr 1 1 6 joined.frag _ _ _
      rw [frag]
      exact rightMapped.1
    · change GrowsAllocator 1 6 (joined.cert.cost (State.init C)) _ _ _ _ _ _
      rw [joinedCost]
      exact totalGrowth
  have cursor := (totalGrowth ⟨16,by decide⟩ (by decide) (initial_repr.2.mem_eq rfl) (by decide)).arrays.free.cell
  refine ⟨prefixRun,prefixMapped,rightInput,suffixRun,rightMapped,?_,wholeMapped,cursor⟩
  simp only [Compilation.code] at suffixRun
  rw [code,run_append_ok prefixRun]
  exact suffixRun

#print axioms suffix_source
#print axioms execution
end Solidity.Backend.Passes.MemoryJoinedAllocation
