import Solidity.Backend.StorageOps.LoopLawsControls

/-! Joint witnesses for the three frozen loop-adapter statements. Reuses the
existing populated machine and actual Evm.run programs. No Source, compiler,
physical gas, fork or world-adequacy claim is made. -/
namespace H62.StorageAudit.LoopWitnesses
open Solidity Solidity.Backend.StorageOps

/-- All three turn_step hypotheses hold on the same machine, flag and programs. -/
theorem step_joint :
    ∃ (cond body : List Evm.Instr) (machine result : Evm.Machine) (flag : Fin Evm.W),
      flag.val ≠ 0 ∧
      Evm.run cond machine = .ok { machine with stack := .val flag :: machine.stack } 0 ∧
      Evm.run body machine = .ok result 0 := by
  exact ⟨LoopLawsControls.yes, LoopLawsControls.body, LoopLawsControls.initial,
    LoopLawsControls.after, Evm.wmod 1, by decide, rfl, rfl⟩

/-- The zero condition is inhabited even when its skipped body really reverts. -/
theorem exit_joint :
    ∃ (cond body : List Evm.Instr) (machine : Evm.Machine),
      Evm.run cond machine = .ok { machine with stack := .val ⟨0, by decide⟩ :: machine.stack } 0 ∧
      Evm.run body machine = .revert := by
  exact ⟨LoopLawsControls.no, [.revert], LoopLawsControls.initial, rfl, rfl⟩

/-- The whole-loop success premise is derived from a real finite iteration. -/
theorem finished_joint :
    ∃ (cond body : List Evm.Instr) (machine result : Evm.Machine),
      Evm.loopRun (Evm.run cond) (Evm.run body) machine = .ok result 0 := by
  exact ⟨LoopLawsControls.no, LoopLawsControls.pending, LoopLawsControls.initial,
    LoopLawsControls.initial, Evm.loopRun_of_iterN (n := 1) rfl⟩

/-- The positive step is an observable mutation of an already populated stack. -/
theorem changed_stack :
    (LoopLawsControls.initial.stack.length, LoopLawsControls.after.stack.length) = (2, 3) := by
  rfl

/-- An actual reverting body is propagated when the condition is nonzero. -/
theorem body_revert :
    Evm.loopTurn (Evm.run LoopLawsControls.yes) (Evm.run [.revert])
      LoopLawsControls.initial = .inr .revert := by
  rfl

/-- A nonzero control index and a direct fault are different boundaries. -/
theorem pending_index_boundary :
    Evm.run LoopLawsControls.pending LoopLawsControls.initial = .ok LoopLawsControls.initial 1 ∧
    Evm.loopTurn (Evm.run LoopLawsControls.yes) (Evm.run LoopLawsControls.pending)
      LoopLawsControls.initial = .inr .fault := by
  exact ⟨rfl, rfl⟩

/-- A zero flag cannot satisfy the positive-step premise. -/
theorem zero_is_not_nonzero : ¬ (Evm.wmod 0).val ≠ 0 := by
  decide

def positive_condition : List Evm.Instr := [.push (.slot (.root 0)), .sload]
def positive_body : List Evm.Instr := [.push (.val (Evm.wmod 0)), .push (.slot (.root 0)), .sstore]
def positive_after : Evm.Machine := { LoopLawsControls.initial with
  store := Evm.WordStore.write LoopLawsControls.initial.store (.root 0) 0 }

theorem positive_condition_before :
    Evm.run positive_condition LoopLawsControls.initial =
      .ok { LoopLawsControls.initial with stack := .val (Evm.wmod 11) :: LoopLawsControls.initial.stack } 0 := by
  rfl

theorem positive_body_run :
    Evm.run positive_body LoopLawsControls.initial = .ok positive_after 0 := by
  rfl

theorem positive_condition_after :
    Evm.run positive_condition positive_after =
      .ok { positive_after with stack := .val (Evm.wmod 0) :: positive_after.stack } 0 := by
  rfl

/-- One positive iteration changes header 11 to zero, then the next condition exits. -/
theorem positive_finished :
    Evm.loopRun (Evm.run positive_condition) (Evm.run positive_body)
      LoopLawsControls.initial = .ok positive_after 0 := by
  have step : Evm.loopTurn (Evm.run positive_condition) (Evm.run positive_body)
      LoopLawsControls.initial = .inl positive_after :=
    LoopLaws.turn_step _ _ _ _ (Evm.wmod 11) (by decide)
      positive_condition_before positive_body_run
  have done : Evm.loopTurn (Evm.run positive_condition) (Evm.run positive_body)
      positive_after = .inr (.ok positive_after 0) :=
    LoopLaws.turn_exit _ _ _ positive_condition_after
  exact Evm.loopRun_of_iterN (n := 2) (by simp only [Evm.loopIterN, step, done])

theorem positive_program :
    Evm.run [.loop positive_condition positive_body] LoopLawsControls.initial =
      .ok positive_after 0 :=
  LoopLaws.run_single_loop _ _ _ _ positive_finished

theorem positive_store_change :
    (LoopLawsControls.initial.store (.root 0), positive_after.store (.root 0)) = (11, 0) := by
  rfl

/-- info: 'H62.StorageAudit.LoopWitnesses.step_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_joint
/-- info: 'H62.StorageAudit.LoopWitnesses.exit_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exit_joint
/-- info: 'H62.StorageAudit.LoopWitnesses.finished_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms finished_joint
/-- info: 'H62.StorageAudit.LoopWitnesses.changed_stack' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms changed_stack
/-- info: 'H62.StorageAudit.LoopWitnesses.body_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms body_revert
/-- info: 'H62.StorageAudit.LoopWitnesses.pending_index_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pending_index_boundary
/-- info: 'H62.StorageAudit.LoopWitnesses.zero_is_not_nonzero' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms zero_is_not_nonzero
/-- info: 'H62.StorageAudit.LoopWitnesses.positive_condition_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms positive_condition_before
/-- info: 'H62.StorageAudit.LoopWitnesses.positive_body_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms positive_body_run
/-- info: 'H62.StorageAudit.LoopWitnesses.positive_condition_after' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms positive_condition_after
/-- info: 'H62.StorageAudit.LoopWitnesses.positive_finished' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms positive_finished
/-- info: 'H62.StorageAudit.LoopWitnesses.positive_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms positive_program
/-- info: 'H62.StorageAudit.LoopWitnesses.positive_store_change' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms positive_store_change
end H62.StorageAudit.LoopWitnesses
