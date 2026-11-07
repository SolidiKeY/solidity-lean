import Solidity.Backend.Failure.Correct
import tests.h62.item2.«audit-calculus».KernelCensus

/-! Joint witnesses for every source theorem in Failure/Correct. Bounds,
stack capacity and continuation safety are proved on the SAME machine and
nonempty bytes. These are component witnesses; this slice has no gas meter,
world state or selectable historical fork. No full compiler result follows. -/
namespace H62.AuditCalculus.Failure
open Solidity.Backend Solidity.Backend.Failure Solidity.Backend.Failure.Slice

private def emptyMachine : Machine := ⟨[], fun _ => 0⟩

#joint_premises Solidity.Backend.Failure.pushed_digits as pushed_digits_premises
/-- Closed joint input to the unchanged `pushed_digits` theorem. -/
theorem pushed_digits_joint : pushed_digits_premises := ⟨7, by decide, True.intro⟩

#joint_premises Solidity.Backend.Failure.byte_lt_word as byte_lt_word_premises
/-- Closed joint input to the unchanged `byte_lt_word` theorem. -/
theorem byte_lt_word_joint : byte_lt_word_premises := ⟨0x2a, True.intro⟩

#joint_premises Solidity.Backend.Failure.pushed_byte as pushed_byte_premises
/-- Closed joint input to the unchanged `pushed_byte` theorem. -/
theorem pushed_byte_joint : pushed_byte_premises := ⟨0x2a, True.intro⟩

#joint_premises Solidity.Backend.Failure.run_pushNat as run_pushNat_premises
/-- Closed joint input to the unchanged `run_pushNat` theorem. -/
theorem run_pushNat_joint : run_pushNat_premises := ⟨7, by decide, [], emptyMachine, True.intro⟩

#joint_premises Solidity.Backend.Failure.run_pushByte as run_pushByte_premises
/-- Closed joint input to the unchanged `run_pushByte` theorem. -/
theorem run_pushByte_joint : run_pushByte_premises := ⟨0x2a, [], emptyMachine, True.intro⟩

#joint_premises Solidity.Backend.Failure.run_writes as run_writes_premises
/-- Closed joint input to the unchanged `run_writes` theorem. -/
theorem run_writes_joint : run_writes_premises := ⟨0, [0x2a], [], emptyMachine, by decide, True.intro⟩

#joint_premises Solidity.Backend.Failure.run_emit_suffix as run_emit_suffix_premises
/-- Closed joint input to the unchanged `run_emit_suffix` theorem. -/
theorem run_emit_suffix_joint : run_emit_suffix_premises := ⟨0, .returned [0x2a], [], emptyMachine, by unfold Fits; decide, True.intro⟩

#joint_premises Solidity.Backend.Failure.run_emit as run_emit_premises
/-- Closed joint input to the unchanged `run_emit` theorem. -/
theorem run_emit_joint : run_emit_premises := ⟨0, .returned [0x2a], emptyMachine, by unfold Fits; decide, True.intro⟩

#joint_premises Solidity.Backend.Failure.stackSafe_pushNat as stackSafe_pushNat_premises
/-- Closed joint input to the unchanged `stackSafe_pushNat` theorem. -/
theorem stackSafe_pushNat_joint : stackSafe_pushNat_premises := ⟨7, by decide, [], emptyMachine, True.intro⟩

#joint_premises Solidity.Backend.Failure.stackSafe_pushByte as stackSafe_pushByte_premises
/-- Closed joint input to the unchanged `stackSafe_pushByte` theorem. -/
theorem stackSafe_pushByte_joint : stackSafe_pushByte_premises := ⟨0x2a, [], emptyMachine, True.intro⟩

#joint_premises Solidity.Backend.Failure.stackSafe_writes as stackSafe_writes_premises
/-- Closed joint input to the unchanged `stackSafe_writes` theorem. -/
theorem stackSafe_writes_joint : stackSafe_writes_premises := ⟨0, [0x2a], [], emptyMachine, by decide, by decide, by decide, True.intro⟩

#joint_premises Solidity.Backend.Failure.stackSafe_emit_suffix as stackSafe_emit_suffix_premises
/-- Closed joint input to the unchanged `stackSafe_emit_suffix` theorem. -/
theorem stackSafe_emit_suffix_joint : stackSafe_emit_suffix_premises := ⟨0, .returned [0x2a], [], emptyMachine, by unfold Fits; decide, by decide, True.intro⟩

#joint_premises Solidity.Backend.Failure.empty_stack_boundary as empty_stack_boundary_premises
/-- Closed joint input to the unchanged `empty_stack_boundary` theorem. -/
theorem empty_stack_boundary_joint : empty_stack_boundary_premises := ⟨0, by decide, emptyMachine, True.intro⟩

#joint_premises Solidity.Backend.Failure.checkedRun_emit_suffix as checkedRun_emit_suffix_premises
/-- Closed joint input to the unchanged `checkedRun_emit_suffix` theorem. -/
theorem checkedRun_emit_suffix_joint : checkedRun_emit_suffix_premises := ⟨0, .returned [0x2a], [], emptyMachine, by unfold Fits; decide, by decide, True.intro⟩

#joint_premises Solidity.Backend.Failure.emitted_memory_frame as emitted_memory_frame_premises
/-- Closed joint input to the unchanged `emitted_memory_frame` theorem. -/
theorem emitted_memory_frame_joint : emitted_memory_frame_premises := ⟨0, 2, .returned [0x2a], emptyMachine, by decide, True.intro⟩

#joint_premises Solidity.Backend.Failure.address_in_bounds as address_in_bounds_premises
/-- Closed joint input to the unchanged `address_in_bounds` theorem. -/
theorem address_in_bounds_joint : address_in_bounds_premises := ⟨0, [0x2a], by unfold Fits; decide, 0, by decide, True.intro⟩

#joint_premises Solidity.Backend.Failure.tail_untouched as tail_untouched_premises
/-- Closed joint input to the unchanged `tail_untouched` theorem. -/
theorem tail_untouched_joint : tail_untouched_premises := ⟨0, 0, [0x2a], (fun _ => 0), True.intro⟩

#joint_premises Solidity.Backend.Failure.chunkWrites_eq as chunkWrites_eq_premises
/-- Closed joint input to the unchanged `chunkWrites_eq` theorem. -/
theorem chunkWrites_eq_joint : chunkWrites_eq_premises := ⟨0, [[0x2a], [], [0x2b]], True.intro⟩

#joint_premises Solidity.Backend.Failure.run_chunkWrites as run_chunkWrites_premises
/-- Closed joint input to the unchanged `run_chunkWrites` theorem. -/
theorem run_chunkWrites_joint : run_chunkWrites_premises := ⟨0, [[0x2a], [], [0x2b]], [], emptyMachine, by decide, True.intro⟩

/-- Successful compilation and the exact observable terminal result for every
supported payload and machine. Failure payloads retain their revert result. -/
def SliceContract (compile : Input → Option Program) : Prop :=
  ∀ (i : Input) (s : Machine), Fits 0 i.bytes → s.stack.length + 2 ≤ 1024 →
    ∃ code, compile i = some code ∧
      checkedRun code s =
        some ({ s with memory := putBytes s.memory 0 i.bytes }, some i.observation)

/-- Totality plus observable execution for the actual unchanged emitter. -/
theorem emitter_total : SliceContract (fun i => some (emit 0 i)) := by
  intro i s fits stack
  refine ⟨emit 0 i, rfl, ?_⟩
  simpa only [List.append_nil] using checkedRun_emit_suffix 0 i [] s fits stack

/-- Reject-all cannot meet successful compilation on an admitted return input. -/
theorem reject_all_refused : ¬ SliceContract (fun _ => none) := by
  intro contract
  obtain ⟨code, admitted, _⟩ := contract (.returned [0x2a]) emptyMachine (by unfold Fits; decide) (by decide)
  cases admitted

/-- An always-reverting emitter cannot fake the RETURN observation. -/
theorem always_revert_refused : ¬ SliceContract (fun _ => some (emit 0 .empty)) := by
  intro contract
  obtain ⟨code, admitted, result⟩ := contract (.returned [0x2a]) emptyMachine (by unfold Fits; decide) (by decide)
  cases admitted
  have actual := checkedRun_emit_suffix 0 .empty [] emptyMachine (by unfold Fits; decide) (by decide)
  simp only [List.append_nil] at actual
  rw [actual] at result
  have observation := congrArg
    (fun r : Option (Machine × Option Solidity.Roadmap.Outcome) => r.map Prod.snd) result
  change some (some (.revert [] : Solidity.Roadmap.Outcome)) = some (some (.success [0x2a])) at observation
  cases observation

/-- Revert payloads are observable and differ from normal returned bytes. -/
theorem revert_observation :
    checkedRun (emit 0 (.custom [0x2a])) emptyMachine =
      some ({ emptyMachine with memory := putBytes emptyMachine.memory 0 [0x2a] },
        some (.revert [0x2a])) := by
  simpa only [List.append_nil] using
    checkedRun_emit_suffix 0 (.custom [0x2a]) [] emptyMachine (by unfold Fits; decide) (by decide)

/-- The published stack boundary is reached: 1023 initial words refuse even
an empty emitter, because its two PUSHes exceed 1024. -/
theorem oversized_stack_refused :
    checkedRun (emit 0 .empty) ⟨List.replicate 1023 ⟨0, by decide⟩, fun _ => 0⟩ = none := by
  unfold checkedRun
  have refused : stackSafe (emit 0 .empty)
      ⟨List.replicate 1023 ⟨0, by decide⟩, fun _ => 0⟩ ≠ true := by
    intro accepted
    have bound := (empty_stack_boundary 0 (by decide)
      ⟨List.replicate 1023 ⟨0, by decide⟩, fun _ => 0⟩).mp accepted
    simp only [List.length_replicate] at bound
    omega
  simp only [refused, Bool.false_eq_true, ↓reduceIte]

#verify_joint Solidity.Backend.Failure.pushed_digits with pushed_digits_joint
#verify_joint Solidity.Backend.Failure.byte_lt_word with byte_lt_word_joint
#verify_joint Solidity.Backend.Failure.pushed_byte with pushed_byte_joint
#verify_joint Solidity.Backend.Failure.run_pushNat with run_pushNat_joint
#verify_joint Solidity.Backend.Failure.run_pushByte with run_pushByte_joint
#verify_joint Solidity.Backend.Failure.run_writes with run_writes_joint
#verify_joint Solidity.Backend.Failure.run_emit_suffix with run_emit_suffix_joint
#verify_joint Solidity.Backend.Failure.run_emit with run_emit_joint
#verify_joint Solidity.Backend.Failure.stackSafe_pushNat with stackSafe_pushNat_joint
#verify_joint Solidity.Backend.Failure.stackSafe_pushByte with stackSafe_pushByte_joint
#verify_joint Solidity.Backend.Failure.stackSafe_writes with stackSafe_writes_joint
#verify_joint Solidity.Backend.Failure.stackSafe_emit_suffix with stackSafe_emit_suffix_joint
#verify_joint Solidity.Backend.Failure.empty_stack_boundary with empty_stack_boundary_joint
#verify_joint Solidity.Backend.Failure.checkedRun_emit_suffix with checkedRun_emit_suffix_joint
#verify_joint Solidity.Backend.Failure.emitted_memory_frame with emitted_memory_frame_joint
#verify_joint Solidity.Backend.Failure.address_in_bounds with address_in_bounds_joint
#verify_joint Solidity.Backend.Failure.tail_untouched with tail_untouched_joint
#verify_joint Solidity.Backend.Failure.chunkWrites_eq with chunkWrites_eq_joint
#verify_joint Solidity.Backend.Failure.run_chunkWrites with run_chunkWrites_joint

#audit_module "Solidity.Backend.Failure.Correct"
#print axioms emitter_total
#print axioms reject_all_refused
#print axioms always_revert_refused
end H62.AuditCalculus.Failure
