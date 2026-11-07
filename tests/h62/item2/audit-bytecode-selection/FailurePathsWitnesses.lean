import Solidity.Backend.FailurePaths.Controls
import tests.h62.item2.«audit-bytecode-selection».HypothesisDomains

/-! Closed joint source/encoding/emission cases for the unchanged failure interfaces.
The target is the published checked terminal slice, not a charged native EVM.
Predicate evidence is accompanied by actual fit/room inputs and actual execution.
-/
namespace Solidity.H62.BytecodeSelection.FailureFixture
open Source Backend Backend.FailurePaths
open Lowering.V08.SourceCustomErrorControls
open Lowering.V08.LiteralFailureLowering

/-- All frozen literal-statement binders, including successful recognition. -/
theorem literal_statement_domain :
    hypotheses_of% Solidity.Backend.FailurePaths.literal_statement := by
  exact ⟨E, [.bool], .tuple [], global .legacy, frame, 0, 5,
    requireFalse FailurePaths.Controls.message,
    .custom (errorData FailurePaths.Controls.message), rfl, locals, populated, True.intro⟩

/-- The actual Boolean encoder, reached/caller states, fit and room coexist. -/
theorem encoded_return_domain :
    hypotheses_of% Solidity.Backend.FailurePaths.encoded_return := by
  exact ⟨E, [.bool, .bool], frame, 0, 5,
    (Lowering.V08.BoolErrorLowering.values (E := E) [true, false]).toR,
    populated, populated, empty, Lowering.V08.BoolErrorLowering.encoded [true, false],
    FailurePaths.Controls.return_encoding_inhabited,
    FailurePaths.Controls.machine, FailurePaths.Controls.machine,
    by unfold Failure.Fits; decide +kernel, by decide +kernel, True.intro⟩

/-- Both source pipelines select the SAME program whose admitted slice runs.
No Fits-only implication substitutes for the displayed actual machine case. -/
theorem compiled_failure_supported (pipeline : Roadmap.Pipeline) :
    ∃ code : Backend.Program,
      compileStatement (global pipeline) 5 FailurePaths.Controls.statement = some code ∧
      Emits code 5 (.custom (errorData FailurePaths.Controls.message)) ∧
      Failure.Fits 5 (errorData FailurePaths.Controls.message) ∧
      FailurePaths.Controls.machine.stack.length + 2 ≤ 1024 ∧
      StatementReverts (global pipeline) frame 7 FailurePaths.Controls.statement locals
        populated populated (errorData FailurePaths.Controls.message) ∧
      Failure.Slice.checkedRun (code ++ FailurePaths.Controls.tail) FailurePaths.Controls.machine =
        some ({FailurePaths.Controls.machine with memory := (Failure.Slice.putBytes
          FailurePaths.Controls.machine.memory 5 (errorData FailurePaths.Controls.message))},
          some (.revert (errorData FailurePaths.Controls.message))) := by
  obtain ⟨compiled, source, _, emitted⟩ := literal_statement (global pipeline) frame 0 5
    (requireFalse FailurePaths.Controls.message)
    (.custom (errorData FailurePaths.Controls.message)) rfl locals populated
  exact ⟨FailurePaths.Controls.program, compiled, emitted,
    Lowering.V08.LiteralFailureControls.reason_fits FailurePaths.Controls.message (by decide +kernel),
    by decide +kernel, source, (FailurePaths.Controls.statement_agreement pipeline).2.2⟩

#print axioms literal_statement_domain
#print axioms encoded_return_domain
#print axioms compiled_failure_supported
end Solidity.H62.BytecodeSelection.FailureFixture
