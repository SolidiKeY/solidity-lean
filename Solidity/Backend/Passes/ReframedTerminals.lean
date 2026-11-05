import Solidity.Backend.Passes.ReframedControls
import Solidity.Backend.Passes.TailDivergence
import Solidity.Backend.Passes.TripleControls

/-! Actual internal terminal clients of the frame-sensitive boundary.
Panic remains guarded; divergence uses the existing finite-iteration theorem.
No post-failure state, ABI payload or public session prefix is asserted. -/
namespace Solidity.Backend.Passes.ReframedTerminals
open Evm Evm.Compiler

namespace Panic
open MemoryCallControls MemoryCallReuse
def program : Prog C After After := .cons (.assert (.simple (.bool false))) .nil
def stage : Compilation 1 leading.frag program := .core leading.frag (by rfl)
theorem source : program.asserts = true ∧ program.run before.st = .error .panic := ⟨rfl,rfl⟩
theorem link : ReframedLink ReframedControls.left stage 1 128 5 base initial machine := by
  intro o mid selected _ _ output
  exact ⟨output.1.core,by decide +kernel⟩

theorem reached :
    ∃ (mid : Machine) (selected : Nat → Fin W), mid.stack = [] ∧ ∀ tail,
      run leading.code {machine with stack := tail} = .ok {mid with stack := tail} 0 ∧
      MappedOutput ReframedControls.left 1 128 base initial {machine with stack := tail}
        before.st {mid with stack := tail} selected ∧
      stage.Input 1 5 selected before.st {mid with stack := tail} ∧
      run stage.code {mid with stack := tail} = .revert ∧
      run (leading.code ++ stage.code) {machine with stack := tail} = .revert := by
  obtain ⟨mid,selected,ht,empty,hall⟩ := compilation_success_shared_mapped
    ReframedControls.left MemoryCallReuseApplication.input (by decide +kernel) prefix_source
  have hm : run leading.code machine = .ok mid 0 := ht
  have out : MappedOutput ReframedControls.left 1 128 base initial machine before.st mid selected := by
    simpa only [prefix_free,Nat.add_zero] using
      mapped_output_stack ReframedControls.left (hall []).2 machine.stack mid.stack
  have hi := link before mid selected prefix_source hm out
  refine ⟨mid,selected,empty,?_⟩
  intro tail
  have ib := compilation_input_stack stage hi tail
  have failed := (compilation_revert_iff stage ib (by decide +kernel)).mpr (.inr source)
  exact ⟨(hall tail).1,by simpa only [prefix_free,Nat.add_zero] using (hall tail).2,
    ib,failed,by
      change run (ReframedControls.left.code ++ stage.code) {machine with stack := tail} = .revert
      rw [run_append_ok (hall tail).1]
      exact failed⟩
end Panic

namespace Immediate
open MemoryCallControls
def program : Prog C [] [] := .cons (.require (.simple (.bool false))) .nil
def stage : Compilation 1 (Frag.init []) program := .core (Frag.init []) (by rfl)
theorem source : program.run initial = .error .revert := rfl
theorem input : stage.Input 1 128 base initial machine :=
  ⟨initial_repr.1.core,by decide⟩

/-- Real suffix code and resource failure, rather than an empty/untyped suffix. -/
theorem suffix_input_refused :
    ¬ (Compilation.memory allocation).Input 1 0 base initial machine := by
  intro h
  have cap := h.2.1
  have pos : 0 < 1 + Evm.Memory.frameNeedProg allocate := Nat.zero_lt_succ _
  exact (Nat.not_le_of_lt pos) cap

theorem link : ReframedLink stage (.memory allocation) 1 128 0 base initial machine := by
  intro o mid selected success _ _
  rw [source] at success
  cases success

theorem stops_before_unreachable_resource :
    run (stage.code ++ allocation.code) machine = .revert :=
  (compilation_reframed_revert_iff stage (.memory allocation) input link
    (by decide +kernel) (by decide +kernel)).mpr (.inl (.inl source))
end Immediate

namespace Spin
open Controls.Fixture AllocatingControls TripleControls
private theorem spin_fragment (F : Frag Γ) : inFragP F TailDivergence.spin = some F := by
  simp only [TailDivergence.spin,inFragP,inFrag,valIn,simpleIn,
    Evm.Prog.pushes,Evm.Prog.pays,Evm.Prog.shrinks,Frag.restrict,
    Nat.sub_self,List.drop_zero,Bool.and_true,Bool.not_false,
    beq_self_eq_true,ite_true]

def stage : Compilation 1 allocationStage.frag TailDivergence.spin :=
  .core allocationStage.frag (spin_fragment allocationStage.frag)

theorem link (tail : List Word) :
    ReframedLink (.memory allocationStage) stage 1 7 0 initialBase (State.init C)
      {initialMachine with stack := tail} := by
  intro o mid selected _ _ output
  exact ⟨output.1.core,by decide +kernel⟩

/-- The source loop's divergence is already independently proved by finite
iterations; its actual typed suffix Input gives fault at every saved tail. -/
theorem reached :
    ∃ (mid : Machine) (selected : Nat → Fin W), mid.stack = [] ∧ ∀ tail,
      run allocationStage.code {initialMachine with stack := tail} =
        .ok {mid with stack := tail} 0 ∧
      MappedOutput (.memory allocationStage) 1 7 initialBase (State.init C)
        {initialMachine with stack := tail} σ {mid with stack := tail} selected ∧
      stage.Input 1 0 selected σ {mid with stack := tail} ∧
      run stage.code {mid with stack := tail} = .fault ∧
      run (allocationStage.code ++ stage.code) {initialMachine with stack := tail} = .fault := by
  obtain ⟨mid,selected,ht,empty,hall⟩ := compilation_success_shared_mapped
    (.memory allocationStage) prefix_input7 (by decide +kernel)
      ReachabilityControls.fresh_state_reaches_fixture
  refine ⟨mid,selected,empty,?_⟩
  intro tail
  have ma : MappedOutput (.memory allocationStage) 1 7 initialBase (State.init C)
      {initialMachine with stack := tail} σ {mid with stack := tail} selected := by
    simpa only [show Evm.Prog.pushes ReachabilityControls.populatedBuilder = 0 by decide +kernel,
      Nat.add_zero] using (hall tail).2
  have ib : stage.Input 1 0 selected σ {mid with stack := tail} := by
    simpa only [show Evm.Prog.pushes ReachabilityControls.populatedBuilder = 0 by decide +kernel,
      Nat.add_zero] using
      link tail _ _ selected ReachabilityControls.fresh_state_reaches_fixture (hall tail).1 ma
  have failed := (compilation_fault_iff stage ib (by decide +kernel)).mpr TailDivergence.source_diverges
  exact ⟨(hall tail).1,ma,ib,failed,
    by
      change run ((Compilation.memory allocationStage).code ++ stage.code)
        {initialMachine with stack := tail} = .fault
      rw [run_append_ok (hall tail).1]
      exact failed⟩
end Spin
end Solidity.Backend.Passes.ReframedTerminals
