import Solidity.Backend.CompilerEndpointV2
import Solidity.Backend.InternalFlow.CallsProgramBridgeFixture

/-!
# The scalar source selector in endpoint shape, and its exhaustion boundary

`selector_endpoint` states the scalar selector `ScalarSourceCompiler.compile`
in the shape of the compiler endpoint: it refuses, or it selects a plan and
every entered world returns in the related state, reverts bare with the
machine, or halts with any other typed error, about which nothing is claimed
(the residual: exhaustion, panic, divergence, revert with data). It only
packages `Selected.returns` and `Selected.bare_revert`.

This consumer is not behind `compiler_endpoint_correct` or its v2. The
selected image does not depend on the quotation depth, so at depth 0 the typed
run is exhausted while the machine returns (`Controls.exhausted_boundary`).
`AgreesExact` has no exhaustion case, hence `no_compilation_world`: any
`Compilation` of that program, from any entry, has no `Input` at the fixture
state (no such `Compilation` is exhibited). At sufficient depth the bridge `CallsProgramBridge.program` supplies the
`Calls.Program`, so `compiled depth` is a `Compilation` of the fixture for
every depth, with no certificate built here. `scalar_agrees` takes the
agreement branch of `compiler_endpoint_result` at the fixture world `L = 1`,
`frame = 16`, and `scalar_success` reads the reached success off it; at depth
0 the same result has no `Input` there (`scalar_exhausted_no_input`).

The universal entries still refuse the fixture: v1 at every depth
(`Controls.endpoint_refused`) and v2 (`v2_refused`). The bridge is one
`Calls.Program` family at the fixture's contract, context and fragment, not a
recognizer over arbitrary programs, so no entry selects it from syntax.
-/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler.Endpoint
open Evm Evm.Memory ScalarRecursiveSource
open DisjointScalarReturn.Client (Γ F caller before reference)

/-- The selector as an endpoint: refusal, or a selected plan whose entered
worlds return, revert bare with the machine, or halt with another typed error
(exhaustion, panic, divergence, revert with data), where no machine outcome is
claimed. -/
theorem selector_endpoint {C : Contract} {Γ : Ctx} (b c frame pointer bottom : Nat)
    (F : Frag Γ) (below : bottom < pointer) (source : Stmt C Γ Γ) :
    compile b c frame pointer bottom F source = none ∨
    ∃ selected : Selected b c frame pointer bottom F source,
      compile b c frame pointer bottom F source = some selected ∧
      ∀ (L fr : Nat) (caller : State C Γ) (base : Nat → Fin W) (machine : Machine) (start : Nat),
        InterfaceV1.Entry selected.plan L b fr F caller base machine start →
        (∃ out, source.run caller = .ok out ∧
          InterfaceV1.Returned selected.plan L b fr caller base machine start out) ∨
        (source.run caller = .error .revert ∧ run selected.plan.code machine = .revert) ∨
        (∃ halt, source.run caller = .error halt ∧ halt ≠ .revert) := by
  cases chosen : compile b c frame pointer bottom F source with
  | none => exact .inl rfl
  | some selected =>
    refine .inr ⟨selected, rfl, fun L fr caller base machine start entry => ?_⟩
    cases actual : source.run caller with
    | ok out => exact .inl ⟨out, rfl, selected.returns below L fr caller base machine start entry out actual⟩
    | error halt =>
      cases halt with
      | revert =>
        exact .inr (.inl ⟨rfl, selected.bare_revert below L fr caller base machine start entry actual⟩)
      | _ => exact .inr (.inr ⟨_, rfl, fun wrong => by cases wrong⟩)

/-- No `Compilation` of the depth-0 fixture has an `Input` at the fixture
state, whatever entry produced it: its typed run is exhausted. -/
theorem no_compilation_world
    (r : Evm.Compiler.Compilation 1 F (.cons (Client.input 0) .nil)) (L frame : Nat)
    (base : Nat → Fin W) (m : Machine) : ¬ r.Input L frame base ScalarContinuation.final m :=
  not_input_of_exhausted r (Prog.run_cons_error Controls.exhausted_boundary.1)

/-- The v2 entry refuses the scalar fixture at every depth, as v1 does
(`Controls.endpoint_refused`). -/
theorem v2_refused (depth : Nat) :
    Passes.CompilerV2.compile 1 F (.cons (Client.input depth) .nil) = none := rfl

/-- The fixture's `Compilation` at every depth, from the bridge's producer. -/
def compiled (depth : Nat) : Evm.Compiler.Compilation 1 F (.cons (Client.input depth) .nil) :=
  .memoryCalls (CallsProgramBridge.program depth) rfl

/-- At sufficient depth the fixture world is an `Input` of the bridged result. -/
theorem scalar_input (depth : Nat) (enough : 3 < depth) :
    (compiled depth).Input 1 16 ScalarContinuation.finalBase ScalarContinuation.final
      ScalarContinuation.target :=
  CallsProgramBridge.fixture_input depth enough

/-- The endpoint at the bridged result: the static check passes at `L = 1`,
`frame = 16`, and the fixture world agrees exactly with `Evm.run`. -/
theorem scalar_agrees (depth : Nat) (enough : 3 < depth) :
    Passes.WholeProgram.staticRefused (compiled depth) 1 16 = false ∧
    (compiled depth).AgreesExact 1 16 ScalarContinuation.finalBase ScalarContinuation.final
      ScalarContinuation.target := by
  rcases compiler_endpoint_result (compiled depth) 1 16 with ⟨-, none⟩ | ⟨check, agree⟩
  · exact absurd (scalar_input depth enough) (none _ _ _)
  · exact ⟨check, agree _ _ _ (scalar_input depth enough)⟩

/-- The reached success, read off the endpoint: `Evm.run` of the bridged code
succeeds with the stack unchanged, in a state `Rep` relates to a typed result. -/
theorem scalar_success (depth : Nat) (enough : 3 < depth) :
    ∃ o m', (Prog.cons (Client.input depth) .nil).run ScalarContinuation.final = .ok o ∧
      run (compiled depth).code ScalarContinuation.target = .ok m' 0 ∧
      m'.stack = ScalarContinuation.target.stack ∧
      (compiled depth).Rep (1 + Evm.Prog.pushes (Prog.cons (Client.input depth) .nil)) 16
        ScalarContinuation.finalBase ScalarContinuation.final ScalarContinuation.target o.st m' := by
  have source : (Prog.cons (Client.input depth) .nil).run ScalarContinuation.final =
      .ok ⟨ScalarReentry.Endpoint.resultState, List.prefix_refl _⟩ := by
    rw [Prog.run_cons_ok (Client.actual_source depth enough), Prog.run_nil]
    rfl
  rcases (scalar_agrees depth enough).2 with ⟨o, m', ok, ran, stack, rep⟩ |
    ⟨reverted | ⟨-, panicked⟩, -⟩ | ⟨diverged, -⟩
  · exact ⟨o, m', ok, ran, stack, rep⟩
  · rw [source] at reverted; cases reverted
  · rw [source] at panicked; cases panicked
  · rw [source] at diverged; cases diverged

/-- At depth 0 the bridged result has no `Input` at the fixture state. -/
theorem scalar_exhausted_no_input (L frame : Nat) (base : Nat → Fin W) (m : Machine) :
    ¬ (compiled 0).Input L frame base ScalarContinuation.final m :=
  no_compilation_world (compiled 0) L frame base m

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler.Endpoint

#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler.Endpoint.selector_endpoint
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler.Endpoint.no_compilation_world
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler.Endpoint.v2_refused
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler.Endpoint.scalar_agrees
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler.Endpoint.scalar_success
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler.Endpoint.scalar_exhausted_no_input
