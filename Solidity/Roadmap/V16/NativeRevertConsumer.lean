import Solidity.Roadmap.V16.NativeParentConsumer
import Solidity.Semantics.CtxEquiv.RevertFml

/-! Actual compiled first-turn failure consumed by the published revert-data
modality. Exact bytes below belong to the INTRINSIC typed run; Evm.Out.revert
records only a target failure class, not a byte payload. No independent Source,
pinned EVM, gas/ABI/frame-origin or full recursive/profile adequacy is supplied.
Arbitrary continuation frames are skipped because the actual body reverts.
-/
namespace Solidity.Roadmap.V16.NativeRevertConsumer
open Solidity.Backend.InternalFlow.RuntimeFrame
open Evm Evm.Memory RecursiveSource RecursiveActivation

abbrev Model := CountdownWitness.P.C
abbrev Context := Parameters CountdownWitness.A
abbrev initial := MutatingActivation.Checks.bad
abbrev machine := MutatingActivation.Checks.badMachine
abbrev condition := (guardCompiled (C := Model) 2 CountdownWitness.F).code
abbrev action := MutatingActivation.code (C := Model) 2 CountdownWitness.F 8
def program (depth : Nat) : Prog Model Context Context :=
  MutatingActivation.body (depth+1)

/-- The actual intrinsic body reverts before ANY continuation frames run. -/
theorem frames_run :
    ∀ (depth : Nat) {Γ₀ : Ctx} (frames : Frames Model Context Γ₀), Prog.runFrames initial (program depth) frames = .error .revert := by
  intro depth Γ₀ frames
  unfold Prog.runFrames
  rw [show Prog.run initial (program depth) = .error .revert from (NativeParentConsumer.bare_revert_spec depth).1]
  rfl

/-- Every positive finite turn bound observes the actual compiled guard/body failure; no gas or unbounded-recursion adequacy is inferred. -/
theorem target_positive :
    ∀ (depth : Nat), Evm.loopIterN (Evm.run condition) (Evm.run action) (depth+1) machine = .inr .revert := by
  intro depth
  rw [Evm.loopIterN, MutatingActivation.Checks.bad_turn]

/-- Zero target turns retain the initial running state, not a revert. -/
theorem target_zero :
    Evm.loopIterN (Evm.run condition) (Evm.run action) 0 machine = .inl machine := by
  rfl

/-- Exact intrinsic revert bytes determine the new modality after every typed continuation, from the actual run rather than a supplied simulation. -/
theorem data_iff :
    ∀ (depth : Nat) {Γ₀ : Ctx} (frames : Frames Model Context Γ₀) (m : Modality) (post : Fml Model Γ₀) (data : DataPred), RFml.holds initial (.revModal m (program depth) frames post data) ↔ data.eval [] = true := by
  intro depth Γ₀ frames m post data
  exact revModal_of_revert (d := []) m post data (frames_run depth frames)

/-- Actual intrinsic failure, finite compiled target failure and exact data-sensitive specification in one witness. -/
theorem certificate :
    ∀ (depth : Nat) {Γ₀ : Ctx} (frames : Frames Model Context Γ₀) (m : Modality) (post : Fml Model Γ₀) (data : DataPred), Prog.runFrames initial (program depth) frames = .error .revert ∧ Evm.loopIterN (Evm.run condition) (Evm.run action) (depth+1) machine = .inr .revert ∧ (RFml.holds initial (.revModal m (program depth) frames post data) ↔ data.eval [] = true) := by
  intro depth Γ₀ frames m post data
  exact ⟨frames_run depth frames, target_positive depth, data_iff depth frames m post data⟩

/-- Inhabited diamond witness with FALSE normal postcondition: the actual run reverts with empty intrinsic data. -/
theorem empty_revert_witness :
    ∀ (depth : Nat),
RFml.holds initial (.revModal .diamond (program depth) .nil (.not .tt) (.bytes [])) := by
  intro depth
  rw [data_iff]
  rfl

/-- The actual empty intrinsic data cannot satisfy a nonempty byte postcondition. -/
theorem wrong_bytes :
    ∀ (depth : Nat),
¬ RFml.holds initial (.revModal .diamond (program depth) .nil (.not .tt) (.bytes [1])) := by
  intro depth
  rw [data_iff]
  decide

/-- This intrinsic bare revert is not encoded Panic(0x41); no independent Source panic or target byte correspondence is inferred. -/
theorem wrong_panic_data :
    ∀ (depth : Nat),
¬ RFml.holds initial (.revModal .diamond (program depth) .nil (.not .tt) (.panic 65)) := by
  intro depth
  rw [data_iff]
  decide

/-- Conservativity retains the old diamond rejection of this actual reverting run. -/
theorem ordinary_diamond_rejected :
    ∀ (depth : Nat),
¬ Solidity.holds initial (.modal .diamond (program depth) .nil .tt) := by
  intro depth
  rw [← revModal_diamond_none initial (program depth) .nil .tt, data_iff]
  decide

/-- The approved diamond also accepts exhaustion even when its data predicate accepts nothing; formula truth alone does not prove a revert. -/
theorem exhaustion_control :
    RFml.holds initial (.revModal .diamond (Prog.recBase (C := Model) (Γ := Context)) .nil (.not .tt) DataPred.none) ∧ Prog.runFrames initial (Prog.recBase (C := Model) (Γ := Context)) .nil = .error .exhausted := by
  constructor
  · rw [RFml.holds]
    unfold Modality.afterRunRev
    rw [show Prog.runFrames initial (Prog.recBase (C := Model) (Γ := Context)) .nil = .error .exhausted from rfl]
    exact ⟨rfl, fun impossible => by cases impossible⟩
  · rfl

/-- A zero-turn running observation cannot be relabelled as the proved positive-bound revert. -/
theorem zero_bound_not_revert :
    Evm.loopIterN (Evm.run condition) (Evm.run action) 0 machine ≠ .inr .revert := by
  rw [target_zero]
  intro impossible
  cases impossible

end Solidity.Roadmap.V16.NativeRevertConsumer

/-- info: 'Solidity.Roadmap.V16.NativeRevertConsumer.frames_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.NativeRevertConsumer.frames_run

/-- info: 'Solidity.Roadmap.V16.NativeRevertConsumer.target_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.NativeRevertConsumer.target_positive

/-- info: 'Solidity.Roadmap.V16.NativeRevertConsumer.target_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.NativeRevertConsumer.target_zero

/-- info: 'Solidity.Roadmap.V16.NativeRevertConsumer.data_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.NativeRevertConsumer.data_iff

/-- info: 'Solidity.Roadmap.V16.NativeRevertConsumer.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.NativeRevertConsumer.certificate

/-- info: 'Solidity.Roadmap.V16.NativeRevertConsumer.empty_revert_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.NativeRevertConsumer.empty_revert_witness

/-- info: 'Solidity.Roadmap.V16.NativeRevertConsumer.wrong_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.NativeRevertConsumer.wrong_bytes

/-- info: 'Solidity.Roadmap.V16.NativeRevertConsumer.wrong_panic_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.NativeRevertConsumer.wrong_panic_data

/-- info: 'Solidity.Roadmap.V16.NativeRevertConsumer.ordinary_diamond_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.NativeRevertConsumer.ordinary_diamond_rejected

/-- info: 'Solidity.Roadmap.V16.NativeRevertConsumer.exhaustion_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.NativeRevertConsumer.exhaustion_control

/-- info: 'Solidity.Roadmap.V16.NativeRevertConsumer.zero_bound_not_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.NativeRevertConsumer.zero_bound_not_revert
