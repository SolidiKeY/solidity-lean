import Solidity.Backend.CompilerEndpointV2
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarSourceCompilerClient

/-!
# The scalar source selector in endpoint shape, and its exhaustion boundary

`selector_endpoint` states the scalar selector `ScalarSourceCompiler.compile`
in the shape of the compiler endpoint: it refuses, or it selects a plan and
every entered world returns in the related state, reverts with the machine, or
halts with another typed error about which nothing is claimed (the residual).
It only packages `Selected.returns` and `Selected.bare_revert`.

The residual is why this consumer is not behind `compiler_endpoint_correct` or
its v2: the selected image does not depend on the quotation depth, so at depth
0 the typed run is exhausted while the machine returns (`exhausted_boundary`).
`AgreesExact` has no exhaustion case, hence `no_compilation_world`: no
`Compilation` of that program, from any entry, has an `Input` at the fixture
state. Both entries refuse the fixture at every depth (`v2_refused`).
-/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler.Endpoint
open Evm Evm.Memory ScalarRecursiveSource
open DisjointScalarReturn.Client (Γ F caller before reference)

/-- The selector as an endpoint: refusal, or a selected plan whose entered
worlds return, revert with the machine, or halt with a non-revert typed error
(exhaustion, panic, divergence), where no machine outcome is claimed. -/
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

/-- The fixture at a sufficient depth takes the returning case. -/
theorem fixture_returns (depth : Nat) (enough : 3 < depth) :
    ∃ selected, compile 1 5 16 9 8 F (Client.input depth) = some selected ∧
      InterfaceV1.Returned selected.plan 1 1 16 ScalarContinuation.final ScalarContinuation.finalBase
        ScalarContinuation.target 10 ⟨ScalarReentry.Endpoint.resultState, List.prefix_refl _⟩ :=
  ⟨Client.selected depth, Client.root depth, Client.returned depth enough⟩

/-- The fixture at depth 0 takes the residual case, and the halt is exhaustion. -/
theorem fixture_residual :
    ∃ selected, compile 1 5 16 9 8 F (Client.input 0) = some selected ∧
      InterfaceV1.Entry selected.plan 1 1 16 F ScalarContinuation.final ScalarContinuation.finalBase
        ScalarContinuation.target 10 ∧
      (Client.input 0).run ScalarContinuation.final = .error .exhausted ∧
      run selected.plan.code ScalarContinuation.target = .ok ScalarReentry.Endpoint.machine 0 :=
  ⟨Client.selected 0, Client.root 0, Client.entered 0, Controls.exhausted_boundary.1,
    Controls.exhausted_boundary.2⟩

/-- No `Compilation` of the depth-0 fixture has an `Input` at the fixture
state, whatever entry produced it: its typed run is exhausted. -/
theorem no_compilation_world
    (r : Evm.Compiler.Compilation 1 F (.cons (Client.input 0) .nil)) (L frame : Nat)
    (base : Nat → Fin W) (m : Machine) : ¬ r.Input L frame base ScalarContinuation.final m :=
  not_input_of_exhausted r (Prog.run_cons_error Controls.exhausted_boundary.1)

/-- The v2 entry refuses the scalar fixture at every depth, as v1 does. -/
theorem v2_refused (depth : Nat) :
    Passes.CompilerV2.compile 1 F (.cons (Client.input depth) .nil) = none := rfl

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler.Endpoint

#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler.Endpoint.selector_endpoint
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler.Endpoint.fixture_residual
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler.Endpoint.no_compilation_world
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler.Endpoint.v2_refused
