import Solidity.Backend.CompilerEndpointV2
import Solidity.Backend.Passes.TupleReturnConsumer

/-!
# The tuple-return consumer through the v2 endpoint

The v1 entry refuses `TupleReturnConsumer.program` (`endpoint_refusal`, kept).
The v2 entry `CompilerV2.compile` accepts it automatically, and its result is
the certificate `TupleReturnConsumer.compiled` that the legacy tests built by
hand (`accepted`). `endpoint_agrees` takes the agreement branch of
`compiler_endpoint_v2_correct` at the consumer's worlds `L = 1`, `frame = 64`;
`endpoint_success` and `endpoint_revert` read the reached success and the
reached revert off that agreement, with no manual certificate.
-/
namespace Solidity.Backend.Passes.TupleReturnConsumer.V2

open Evm Evm.Memory Evm.Compiler Passes.WholeProgram
open Backend.InternalFlow.RuntimeFrame
open Backend.InternalFlow.RuntimeFrame.V3CallProducerRef
open Backend.InternalFlow.RuntimeFrame.V3CallProducerRef.Tuple.Controls

/-- The automatic selection finds the published tuple statement. -/
theorem statement_selected : CompilerV2.statement 1 F call = some Tuple.Controls.statement := by
  have structural : Composition.compileStatement 1 F call = none := rfl
  have tuple : CompilerV2.tupleStatement 1 F call = some Tuple.Controls.statement := by
    change (Composition.compileProgram 1 F (Tuple.expand ArrayControls.args binders body)).map
      (Tuple.emit "tupleAlias" ArrayControls.args binders body) = some Tuple.Controls.statement
    rw [expanded_public]
    rfl
  simp only [CompilerV2.statement, structural, tuple]

/-- The automatic program selection is the published `selected`. -/
theorem program_selected : CompilerV2.program 1 F program = some selected := by
  change (do
    let first ← CompilerV2.statement 1 F call
    let rest ← CompilerV2.program 1 first.checked.frag .nil
    pure (Composition.cons first rest)) = some selected
  rw [statement_selected]
  rfl

/-- **Automatic acceptance.** The v2 entry returns the certificate the legacy
tests supplied by hand. -/
theorem accepted : CompilerV2.compile 1 F program = some compiled :=
  CompilerV2.compile_of_selected endpoint_refusal rfl program_selected

/-- The consumer's worlds pass the static check. -/
theorem passes : staticRefused compiled 1 64 = false :=
  staticRefused_of_input compiled (input (wmod 0))

/-- `compiler_endpoint_v2_correct` at the consumer: the v2 entry accepts, the
static check passes at `L = 1`, `frame = 64`, and every consumer world agrees
exactly with `Evm.run`. -/
theorem endpoint_agrees :
    ∃ r : Compilation 1 F program, CompilerV2.compile 1 F program = some r ∧
      staticRefused r 1 64 = false ∧
      ∀ n : Fin W, r.AgreesExact 1 64 ArrayControls.bases (ArrayControls.caller n)
        (ArrayControls.machine n) := by
  rcases compiler_endpoint_v2_correct 1 F program with refused | ⟨r, chosen, worlds⟩
  · exact absurd (accepted.symm.trans refused) (by simp)
  · have same : compiled = r := Option.some.inj (accepted.symm.trans chosen)
    subst same
    rcases worlds 1 64 with ⟨check, -⟩ | ⟨check, agree⟩
    · exact absurd (passes.symm.trans check) Bool.false_ne_true
    · exact ⟨compiled, accepted, check, fun n => agree _ _ _ (input n)⟩

/-- The reached success, read off the endpoint: `Evm.run` of the accepted code
succeeds with the stack unchanged, in the state `Rep` relates to the typed
result. -/
theorem endpoint_success :
    ∃ r : Compilation 1 F program, CompilerV2.compile 1 F program = some r ∧
      ∃ m', run r.code (ArrayControls.machine (wmod 0)) = .ok m' 0 ∧
        m'.stack = (ArrayControls.machine (wmod 0)).stack ∧
        r.Rep (1 + Evm.Prog.pushes program) 64 ArrayControls.bases
          (ArrayControls.caller (wmod 0)) (ArrayControls.machine (wmod 0)) result.st m' := by
  obtain ⟨r, chosen, -, agree⟩ := endpoint_agrees
  refine ⟨r, chosen, ?_⟩
  rcases agree (wmod 0) with ⟨o, m', ok, ran, stack, rep⟩ |
    ⟨reverted | ⟨-, panicked⟩, -⟩ | ⟨diverged, -⟩
  · have same : o = result := Except.ok.inj (ok.symm.trans program_source)
    subst same
    exact ⟨m', ran, stack, rep⟩
  · rw [program_source] at reverted; cases reverted
  · rw [program_source] at panicked; cases panicked
  · rw [program_source] at diverged; cases diverged

/-- The reached revert, read off the endpoint. -/
theorem endpoint_revert :
    ∃ r : Compilation 1 F program, CompilerV2.compile 1 F program = some r ∧
      run r.code (ArrayControls.machine (wmod 2)) = .revert := by
  obtain ⟨r, chosen, -, agree⟩ := endpoint_agrees
  refine ⟨r, chosen, ?_⟩
  have failed : program.run (ArrayControls.caller (wmod 2)) = .error .revert :=
    Prog.run_cons_error source_revert
  rcases agree (wmod 2) with ⟨o, -, ok, -⟩ | ⟨-, ran⟩ | ⟨diverged, -⟩
  · rw [failed] at ok; cases ok
  · exact ran
  · rw [failed] at diverged; cases diverged

/-- Both entries on the same program: v1 refuses (R1), v2 accepts. -/
theorem v1_refuses_v2_accepts :
    Compiler.compile 1 F program = none ∧ CompilerV2.compile 1 F program = some compiled :=
  ⟨endpoint_refusal, accepted⟩

/-- The v2 entry still refuses a body the structural selector does not take:
a literal `revert` in the tuple callee. -/
theorem literal_revert_refused :
    (CompilerV2.compile 1 F (.cons (.call "tupleAlias" ArrayControls.args (.rets binders)
      (.cons .revert .nil : Prog C (rs ++ [.mem A, .val .uint]) (rs ++ [.mem A, .val .uint])))
      .nil : Prog C Γ (rs ++ Γ))).isNone = true := by decide +kernel

end Solidity.Backend.Passes.TupleReturnConsumer.V2

#print axioms Solidity.Backend.Passes.TupleReturnConsumer.V2.accepted
#print axioms Solidity.Backend.Passes.TupleReturnConsumer.V2.endpoint_agrees
#print axioms Solidity.Backend.Passes.TupleReturnConsumer.V2.endpoint_success
#print axioms Solidity.Backend.Passes.TupleReturnConsumer.V2.endpoint_revert
#print axioms Solidity.Backend.Passes.TupleReturnConsumer.V2.literal_revert_refused
