import Solidity.Backend.Executable.PaymentArtifact

/-! Nontrivial actual constructor/runtime composition controls. No source-level
constructor lowering, account CREATE or runtime-jump execution follows from the
copy/terminal slice. Raw byte/code inspection is internal artifact validation,
not a new admitted source observation. -/
namespace Solidity.Backend.Executable.PaymentArtifactChecks
open Creation PaymentArtifact

def args : List UInt8 := [0xaa,0xbb]
def tail : List StackWord := [⟨17,by decide⟩,⟨29,by decide⟩]

theorem both_terminals :
    Exec (image true args) (image true args) tail [] (.returned runtime) ∧
    Exec (image false args) (image false args) tail [] (.reverted runtime) :=
  ⟨constructor_exec true args tail,constructor_exec false args tail⟩

theorem separate_arguments :
    ((image true args).drop 18).take 321 = runtime ∧
    (image true args).drop (18+321) = args := by
  rw [← runtime_length_exact]
  exact ⟨runtime_slice true args,arguments_slice true args⟩

theorem wrong_terminal : ¬ Exec (image false args) (image false args) tail [] (.returned runtime) := by
  intro wrong
  have impossible := Exec.deterministic both_terminals.2 wrong
  cases impossible

theorem arguments_not_runtime :
    ¬ Exec (image true args) (image true args) tail [] (.returned (runtime ++ args)) := by
  intro wrong
  have same := Exec.deterministic both_terminals.1 wrong
  have bytes := Outcome.returned.inj same
  have lengths := congrArg List.length bytes
  simp only [List.length_append, args, List.length_cons, List.length_nil] at lengths
  omega

theorem nonempty_runtime : ¬ Exec (image true args) (image true args) tail [] (.returned []) := by
  intro wrong
  have same := Exec.deterministic both_terminals.1 wrong
  have lengths := congrArg List.length (Outcome.returned.inj same)
  rw [runtime_length_exact] at lengths
  cases lengths

/-- Standalone fromAssembly header is12bytes; the real nonempty prefix adds6.
Neither origin is the runtime's own branch coordinate system. -/
theorem distinct_origins :
    (artifact args).runtimeStart = 12 ∧ (front true).length = 18 ∧
    (front false).length = 18 ∧ runtime.length = 321 ∧
    (artifact args).linkBase = 0 := by
  refine ⟨?_,front_length true,front_length false,runtime_length_exact,rfl⟩
  change 2*byteWidth runtime.length+8 = 12
  rw [runtime_width]

theorem actual_links_resolved : (artifact args).runtimeLinks = [] := by
  change TransferCallChecks.output.linkRefs = []
  rw [(assemble_eq TransferCallChecks.assembled).2.2]
  rfl
/-- The actual constructor run and actual selected runtime operand inhabit
all three coordinate claims together, with the populated creation stack tail. -/
theorem coordinate_client :
    ∃ imm, TransferCallChecks.output.code[TransferCallChecks.payment.length+1]? =
        some (.push (asmWidths 0 (TransferCall.items TransferCallChecks.payment) 0) imm) ∧
      Exec (image true args) (image true args) tail [] (.returned runtime) ∧
      validJumpdest runtime (ofBytesBE imm.toList) = true ∧
      validJumpdest (image true args) (18+ofBytesBE imm.toList) = true ∧
      validJumpdest runtime (18+ofBytesBE imm.toList) = false := by
  obtain ⟨imm,push,good,embedded,bad⟩ := constructor_runtime_coordinates true args
  exact ⟨imm,push,both_terminals.1,good,embedded,bad⟩

/-- The continuing constructor prefix exposes the actual unchanged tail at
wrapper entry, before Exec hides terminal stack/memory in its outcome. -/
theorem prefix_tail_boundary :
    let code := image true args
    let rest := Backend.encode (exitWrapper true placement.lengthWord placement.offsetWord) ++ runtime ++ args
    Prefix code code tail [] rest tail (writeBytes [] 32 (readBytes code 0 1)) := by
  let code := image true args
  let rest := Backend.encode (exitWrapper true placement.lengthWord placement.offsetWord) ++ runtime ++ args
  change Prefix code (Backend.encode copyPrefix ++ rest) tail [] rest tail (writeBytes [] 32 (readBytes code 0 1))
  exact prefix_stack_tail (prefix_trans (PrefixChecks.first_segment code rest) (PrefixChecks.second_segment code rest)) tail

/-- info: 'Solidity.Backend.Executable.PaymentArtifactChecks.prefix_tail_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_tail_boundary

/-- info: 'Solidity.Backend.Executable.PaymentArtifactChecks.both_terminals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms both_terminals

/-- info: 'Solidity.Backend.Executable.PaymentArtifactChecks.separate_arguments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms separate_arguments

/-- info: 'Solidity.Backend.Executable.PaymentArtifactChecks.wrong_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_terminal

/-- info: 'Solidity.Backend.Executable.PaymentArtifactChecks.arguments_not_runtime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms arguments_not_runtime

/-- info: 'Solidity.Backend.Executable.PaymentArtifactChecks.nonempty_runtime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonempty_runtime

/-- info: 'Solidity.Backend.Executable.PaymentArtifactChecks.distinct_origins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms distinct_origins

/-- info: 'Solidity.Backend.Executable.PaymentArtifactChecks.actual_links_resolved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_links_resolved

/-- info: 'Solidity.Backend.Executable.PaymentArtifactChecks.coordinate_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms coordinate_client

end Solidity.Backend.Executable.PaymentArtifactChecks
