import Solidity.Backend.MemoryOps.SourceShortCircuit

/-! Actual conditional selection of effectful expressions. The selected Source
computation and word branch keep their real reached state. No pure ValueSim of
an effectful body, alternative evaluator or general compiler is introduced. -/
namespace Solidity.Backend.MemoryOps

/-- Read the initial guard and execute exactly the selected existing Source
computation. The equality covers success, timeout and failure states. -/
theorem source_cond_select {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (y : Source.EMState E Γ)
    (guard : Source.Idx Γ .bool) (yes no : Source.RExpr E Γ τ) (v : Bool)
    (hg : y.1.get guard=.bool v) :
    (Source.evalE G F (fuel+2) (.cond (.local guard) yes no)).run y=
      (Source.evalE G F (fuel+1) (if v then yes else no)).run y := by
  first
  | solve | rfl | simp only [] | omega
  | rw [Source.evalE,Source.Hoare.run_bind,source_local_value_run G F fuel y guard (.bool v) hg]
    cases v <;> rfl

/-- False jumps over the entire true program and its exit jump. The right
program may mutate memory or fail; the equation does not assume its result. -/
theorem word_cond_false (cond yes no : List Evm.Instr) (m : Evm.Machine)
    (hc : Evm.run cond m=.ok (m.push (.val (Evm.bword false))) 0) :
    Evm.run (Evm.Memory.conditionalCode cond yes no) m=Evm.run no m := by
  first
  | solve | rfl | simp only [] | omega
  | simp only [Evm.Memory.conditionalCode,List.append_assoc]
    rw [Evm.run_append_ok hc,Evm.run_append_skip (m' := m) (k := yes.length+1) rfl,
      Evm.exec_append,Evm.exec_skip]
    simp only [Evm.Out.ok_bind]
    rfl

/-- True executes the actual successful effectful branch and skips the entire
unselected branch. Its returned machine is the branch's actual machine. -/
theorem word_cond_true (cond yes no : List Evm.Instr) (m out : Evm.Machine)
    (hc : Evm.run cond m=.ok (m.push (.val (Evm.bword true))) 0)
    (hy : Evm.run yes m=.ok out 0) :
    Evm.run (Evm.Memory.conditionalCode cond yes no) m=.ok out 0 := by
  first
  | solve | rfl | simp only [] | omega
  | simp only [Evm.Memory.conditionalCode,List.append_assoc]
    rw [Evm.run_append_ok hc,Evm.run_append_skip (m' := m) (k := 0) rfl]
    change Evm.run (yes ++ ([.jump no.length] ++ no)) m=_
    rw [Evm.run_append_ok hy]
    exact Evm.exec_length no out

/-- A selected rejection stops before the exit jump or unselected branch.
Revert has no returned machine and asserts no panic bytes or outer rollback. -/
theorem word_cond_true_error (cond yes no : List Evm.Instr) (m : Evm.Machine)
    (hc : Evm.run cond m=.ok (m.push (.val (Evm.bword true))) 0)
    (hy : Evm.run yes m=.revert) :
    Evm.run (Evm.Memory.conditionalCode cond yes no) m=.revert := by
  first
  | solve | rfl | simp only [] | omega
  | simp only [Evm.Memory.conditionalCode,List.append_assoc]
    rw [Evm.run_append_ok hc,Evm.run_append_skip (m' := m) (k := 0) rfl]
    exact Evm.run_append_revert hy

/-- info: 'Solidity.Backend.MemoryOps.source_cond_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_cond_select
/-- info: 'Solidity.Backend.MemoryOps.word_cond_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_cond_false
/-- info: 'Solidity.Backend.MemoryOps.word_cond_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_cond_true
/-- info: 'Solidity.Backend.MemoryOps.word_cond_true_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_cond_true_error
end Solidity.Backend.MemoryOps
