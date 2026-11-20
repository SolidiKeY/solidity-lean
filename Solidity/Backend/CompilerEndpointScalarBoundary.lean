import Solidity.Backend.CompilerEndpointV2
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarSourceCompilerClient

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
state.

The v3 entry `CompilerV3.compile` accepts the fixture automatically at every
depth (`accepted`): the selector recognises it and `CompilerScalarBridge`
supplies the `Calls.Program`; no certificate is built here. For depth above 3
`endpoint_agrees` takes the agreement branch of `compiler_endpoint_v3_correct`
at the fixture world `L = 1`, `frame = 16`, and `endpoint_success` reads the
reached success off it. At depth 0 the accepted result has no `Input` at the
fixture state (`exhausted_no_input`): acceptance does not carry the exhausted
run to the machine. v1 and v2 still refuse the fixture at every depth
(`Controls.endpoint_refused`, `v2_refused`). Depths 1 to 3 are accepted too;
no world is exhibited for them here.
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

/-- The fixed parameters of the v3 entry fit the fixture's context. -/
theorem shape : Passes.CompilerScalarBridge.Shape 1 5 16 9 8 Γ := by decide

/-- The fixture's bridged result at every depth. -/
def compiled (depth : Nat) : Evm.Compiler.Compilation 1 F (.cons (Client.input depth) .nil) :=
  .memoryCalls (Passes.CompilerScalarBridge.selectedProgram (Client.selected depth) shape) rfl

/-- **Automatic acceptance.** The v3 entry accepts the fixture at every depth. -/
theorem accepted (depth : Nat) :
    Passes.CompilerV3.compile 1 F (.cons (Client.input depth) .nil) = some (compiled depth) :=
  Passes.CompilerV3.compile_of_selected (v2_refused depth) rfl shape (Client.root depth)

/-- At sufficient depth the fixture world is an `Input` of the accepted result. -/
theorem fixture_input (depth : Nat) (enough : 3 < depth) :
    (compiled depth).Input 1 16 ScalarContinuation.finalBase ScalarContinuation.final
      ScalarContinuation.target := by
  have arena : (Client.selected depth).plan.arenaWords ScalarContinuation.final = 6 :=
    ScalarReentry.arena depth
  have free : Passes.CompilerScalarBridge.cost (Client.selected depth) ScalarContinuation.final = 0 := by
    simp only [Passes.CompilerScalarBridge.cost, arena, Nat.le_refl, if_true,
      Client.actual_source depth enough]
  exact ⟨(Client.entered depth).represented, by change 1 + (16 - 1) ≤ 16; decide, .inl free⟩

/-- `compiler_endpoint_v3_correct` at the fixture: the v3 entry accepts, the
static check passes at `L = 1`, `frame = 16`, and the fixture world agrees
exactly with `Evm.run`. -/
theorem endpoint_agrees (depth : Nat) (enough : 3 < depth) :
    ∃ r, Passes.CompilerV3.compile 1 F (.cons (Client.input depth) .nil) = some r ∧
      Passes.WholeProgram.staticRefused r 1 16 = false ∧
      r.AgreesExact 1 16 ScalarContinuation.finalBase ScalarContinuation.final
        ScalarContinuation.target := by
  rcases compiler_endpoint_v3_correct 1 F (.cons (Client.input depth) .nil) with
    refused | ⟨r, chosen, worlds⟩
  · exact absurd ((accepted depth).symm.trans refused) (by simp)
  · have same : compiled depth = r := Option.some.inj ((accepted depth).symm.trans chosen)
    subst same
    rcases worlds 1 16 with ⟨-, none⟩ | ⟨check, agree⟩
    · exact absurd (fixture_input depth enough) (none _ _ _)
    · exact ⟨_, accepted depth, check, agree _ _ _ (fixture_input depth enough)⟩

/-- The reached success, read off the endpoint: `Evm.run` of the accepted code
succeeds with the stack unchanged, in a state `Rep` relates to the typed result. -/
theorem endpoint_success (depth : Nat) (enough : 3 < depth) :
    ∃ r, Passes.CompilerV3.compile 1 F (.cons (Client.input depth) .nil) = some r ∧
      ∃ o m', (Prog.cons (Client.input depth) .nil).run ScalarContinuation.final = .ok o ∧
        run r.code ScalarContinuation.target = .ok m' 0 ∧
        m'.stack = ScalarContinuation.target.stack ∧
        r.Rep (1 + Evm.Prog.pushes (Prog.cons (Client.input depth) .nil)) 16
          ScalarContinuation.finalBase ScalarContinuation.final ScalarContinuation.target o.st m' := by
  obtain ⟨r, chosen, -, agree⟩ := endpoint_agrees depth enough
  refine ⟨r, chosen, ?_⟩
  have source : (Prog.cons (Client.input depth) .nil).run ScalarContinuation.final =
      .ok ⟨ScalarReentry.Endpoint.resultState, List.prefix_refl _⟩ := by
    rw [Prog.run_cons_ok (Client.actual_source depth enough), Prog.run_nil]
    rfl
  rcases agree with ⟨o, m', ok, ran, stack, rep⟩ |
    ⟨reverted | ⟨-, panicked⟩, -⟩ | ⟨diverged, -⟩
  · exact ⟨o, m', ok, ran, stack, rep⟩
  · rw [source] at reverted; cases reverted
  · rw [source] at panicked; cases panicked
  · rw [source] at diverged; cases diverged

/-- At depth 0 the v3 entry accepts, and the accepted result has no `Input` at
the fixture state: the exhausted run is not carried to the machine. -/
theorem exhausted_no_input (L frame : Nat) (base : Nat → Fin W) (m : Machine) :
    Passes.CompilerV3.compile 1 F (.cons (Client.input 0) .nil) = some (compiled 0) ∧
    ¬ (compiled 0).Input L frame base ScalarContinuation.final m :=
  ⟨accepted 0, no_compilation_world (compiled 0) L frame base m⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler.Endpoint

#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler.Endpoint.selector_endpoint
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler.Endpoint.no_compilation_world
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler.Endpoint.v2_refused
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler.Endpoint.accepted
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler.Endpoint.endpoint_agrees
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler.Endpoint.endpoint_success
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler.Endpoint.exhausted_no_input
