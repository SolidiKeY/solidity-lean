import Solidity.Backend.CompilerEndpoint
import Solidity.Backend.Passes.CompilerWholeScope

/-!
# Witnesses for the compiler endpoint

Kernel-checked instances of each case of `CompilerEndpoint`:

* accepted and agreeing with `Evm.run`: the scoped-call fixture
  `CompilerWholeScope.program` (memory-calls branch, non-empty code) in its
  world `L = 1`, `frame = 128`: the static check passes, the world is an
  `Input`, and the compiled code runs to success in the related state;
* R1: `revertData []`, which no checked branch accepts;
* R2: the same fixture at the source frame `1 + frameNeedProg program`, below
  its call-frame need, and the empty program at `L = Lmax + 1` (core bound).
-/
namespace Solidity.Backend.CompilerEndpointWitnesses

open Evm Evm.Compiler Endpoint
open Passes.MemoryCallControls (C)
open Passes.CompilerWholeScope (program actual accepted initial_input source_run)

/-! ## Accepted, agreeing with `Evm.run` -/

/-- The fixture's compiled code is not empty. -/
theorem scope_code_nonempty : actual.code.isEmpty = false := by
  with_unfolding_all decide +kernel

/-- The fixture's world passes the static check. -/
theorem scope_passes : frameRefused actual 1 128 = false :=
  frameRefused_of_input actual initial_input

/-- The endpoint's agreement clause at the fixture's world. -/
theorem scope_agrees :
    ∃ r : Compilation 1 (Frag.init []) program, Compiler.compile 1 (Frag.init []) program = some r ∧
      frameRefused r 1 128 = false ∧
      r.AgreesExact 1 128 Passes.MemoryCallControls.base Passes.MemoryCallControls.initial
        Passes.MemoryCallControls.machine :=
  ⟨actual, accepted, scope_passes, actual.correct_exact initial_input⟩

/-- The typed run succeeds, and so does `Evm.run` of the non-empty compiled
code, its stack unchanged, in the state `Rep` relates. -/
theorem scope_runs : ∃ m', run actual.code Passes.MemoryCallControls.machine = .ok m' 0 ∧
    m'.stack = Passes.MemoryCallControls.machine.stack ∧
    actual.Rep (1 + Evm.Prog.pushes program) 128 Passes.MemoryCallControls.base
      Passes.MemoryCallControls.initial Passes.MemoryCallControls.machine
      Passes.CompilerWholeScope.result.st m' :=
  actual.compile_success initial_input source_run

/-! ## R1: the checked entry refuses -/

/-- A program no checked branch accepts. -/
def unsupported : Solidity.Prog C [] [] := .cons (.revertData []) .nil

theorem unsupported_refused : Compiler.compile 0 (Frag.init []) unsupported = none :=
  Option.isNone_iff_eq_none.mp (by decide +kernel)

/-! ## R2: a static bound fails -/

/-- The fixture at the source frame, below its call-frame need. -/
theorem scope_frame_refused :
    frameRefused actual 1 (1 + Memory.frameNeedProg program) = true := by
  with_unfolding_all decide +kernel

theorem scope_frame_no_world (base : Nat → Fin W) (σ : State C []) (m : Machine) :
    ¬ actual.Input 1 (1 + Memory.frameNeedProg program) base σ m :=
  frame_stage actual 1 _ base σ m scope_frame_refused

/-- The empty program. -/
def empty : Solidity.Prog C [] [] := .nil

/-- The core branch's bound: the empty program at `L = Lmax + 1`. -/
theorem empty_lmax_refused :
    (Compiler.compile 0 (Frag.init []) empty).map (fun r => frameRefused r (Lmax + 1) 0) =
      some true := by
  decide +kernel

end Solidity.Backend.CompilerEndpointWitnesses

#print axioms Solidity.Backend.CompilerEndpointWitnesses.scope_code_nonempty
#print axioms Solidity.Backend.CompilerEndpointWitnesses.scope_agrees
#print axioms Solidity.Backend.CompilerEndpointWitnesses.scope_runs
#print axioms Solidity.Backend.CompilerEndpointWitnesses.unsupported_refused
#print axioms Solidity.Backend.CompilerEndpointWitnesses.scope_frame_no_world
#print axioms Solidity.Backend.CompilerEndpointWitnesses.empty_lmax_refused
