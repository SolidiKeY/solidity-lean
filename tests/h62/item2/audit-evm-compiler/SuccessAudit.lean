import Solidity.Evm.Examples

/-! Nonempty public-compiler success and explicit trivial-compiler controls.
The observation is a write to alice.age in the intrinsic EVM model. This model
has no gas/fork parameter, so this file makes no full-EVM gas/fork claim. -/
namespace Solidity.H62.EvmCompilerAudit
open Evm Evm.Examples

/-- An observable write must come from successful admission and execution. -/
def WritesAge (candidate : Option (List Instr)) : Prop :=
  ∃ code, candidate = some code ∧ ∃ final,
    run code fresh = .ok final 0 ∧ final.store (.root 13) = 10

theorem supported_setAge : (inFragP (Frag.init []) setAge).isSome = true := by
  decide +kernel

/-- The selected execution succeeds without a pending forward jump. -/
theorem setAge_zero_pending :
    (match run (compileProg 0 setAge) fresh with
      | .ok _ pending => pending = 0
      | _ => False) := by
  rfl

/-- The unchanged public compiler succeeds and actually changes storage. -/
theorem compiled_setAge_writes : WritesAge (some (compileProg 0 setAge)) := by
  have observation : storeAt (run (compileProg 0 setAge) fresh) (.root 13) = some 10 :=
    setAge_run
  have zero := setAge_zero_pending
  cases execution : run (compileProg 0 setAge) fresh with
  | ok final pending =>
    rw [execution] at observation zero
    subst pending
    exact ⟨_, rfl, final, execution, Option.some.inj observation⟩
  | revert => rw [execution] at observation; cases observation
  | fault => rw [execution] at observation; cases observation

theorem reject_all_fails : ¬ WritesAge none := by
  rintro ⟨code, admission, _⟩
  cases admission

theorem always_revert_fails : ¬ WritesAge (some [.revert]) := by
  rintro ⟨code, admission, final, execution, _⟩
  cases Option.some.inj admission
  cases execution

/-- An empty implementation cannot satisfy the observable nonempty program. -/
theorem emit_nothing_fails : ¬ WritesAge (some []) := by
  rintro ⟨code, admission, final, execution, observation⟩
  cases Option.some.inj admission
  cases execution
  change (0 : Nat) = 10 at observation
  cases observation


/-- Writing the right value then jumping beyond the code is not normal success. -/
theorem trailing_jump_fails :
    ¬ WritesAge (some (compileProg 0 setAge ++ [.jump 1])) := by
  obtain ⟨code, admission, actual, executed, _⟩ := compiled_setAge_writes
  cases Option.some.inj admission
  have jumped : run (compileProg 0 setAge ++ [.jump 1]) fresh = .ok actual 1 := by
    rw [run_append_ok executed]
    rfl
  rintro ⟨wrongCode, wrongAdmission, final, wrongRun, _⟩
  cases Option.some.inj wrongAdmission
  rw [jumped] at wrongRun
  cases wrongRun

/-- Overflow is an observable failure, rather than an admitted success. -/
theorem overflow_reverts : run (compileProg 0 overflow) fresh = .revert :=
  reverted_eq overflow_run

#print axioms supported_setAge
#print axioms setAge_zero_pending
#print axioms compiled_setAge_writes
#print axioms reject_all_fails
#print axioms always_revert_fails
#print axioms emit_nothing_fails
#print axioms trailing_jump_fails
#print axioms overflow_reverts
end Solidity.H62.EvmCompilerAudit
