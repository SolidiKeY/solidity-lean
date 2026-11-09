import Solidity.Backend.CompilerEndpoint
import Solidity.Backend.Passes.CompilerWholeScope

/-!
# Witnesses for the compiler endpoint

Kernel-checked instances of each case of `CompilerEndpoint`:

* accepted through bytes: the empty program (core branch, empty code, empty
  byte selection, a zero-step safe trace);
* R1: `revertData []`, which no checked branch accepts;
* R2: the scoped-call fixture `CompilerWholeScope.program` at the source frame
  `1 + frameNeedProg program`, below its call-frame need;
* R3: the same fixture's memory code, and the core code of `revert`;
* R4: the empty program's bytes from an entry stack of 1025 words.

Today only empty code is selected to bytes: every emitted local, storage,
branch and revert instruction is refused at R3.
-/
namespace Solidity.Backend.CompilerEndpointWitnesses

open Evm Evm.Compiler Selection Endpoint
open Passes.MemoryCallControls (C)

/-- The empty program. -/
def empty : Solidity.Prog C [] [] := .nil

/-- A program no checked branch accepts. -/
def unsupported : Solidity.Prog C [] [] := .cons (.revertData []) .nil

/-- A program accepted by the core branch whose code has no byte selection. -/
def reverting : Solidity.Prog C [] [] := .cons .revert .nil

/-! ## Accepted through bytes -/

theorem empty_accepted : (Compiler.compile 0 (Frag.init []) empty).isSome = true := by
  decide +kernel

theorem empty_code : (Compiler.compile 0 (Frag.init []) empty).map (·.code.length) = some 0 := by
  decide +kernel

theorem empty_selected :
    ((Compiler.compile 0 (Frag.init []) empty).map (·.code)).bind compileScalar = some [] := by
  decide +kernel

theorem empty_capacity : Scalar.stackBound [] (([] : Scalar.Stack).length : Int) = true := by
  decide +kernel

/-- The accepted empty program runs through bytes: the IR succeeds unchanged and
the bytes take a capacity-safe zero-step trace to the end of the code. -/
theorem empty_through_bytes (m : Machine) (stack : m.stack = irStack []) :
    ∃ r : Compilation 0 (Frag.init []) empty, Compiler.compile 0 (Frag.init []) empty = some r ∧
      compileScalar r.code = some [] ∧ ByteAgree r.code [] [] m := by
  cases accepted : Compiler.compile 0 (Frag.init []) empty with
  | none =>
    have := empty_accepted
    rw [accepted] at this
    cases this
  | some r =>
    have code : r.code = [] := by
      have length := empty_code
      rw [accepted] at length
      exact List.eq_nil_of_length_eq_zero (Option.some.inj length)
    have selected : compileScalar r.code = some [] := by rw [code]; rfl
    exact ⟨r, rfl, selected, byte_agree r.code [] selected [] empty_capacity m stack⟩

/-! ## R1: the checked entry refuses -/

theorem unsupported_refused : Compiler.compile 0 (Frag.init []) unsupported = none :=
  Option.isNone_iff_eq_none.mp (by decide +kernel)

/-! ## R2: a static frame bound fails -/

open Passes.CompilerWholeScope (program actual branch) in
theorem scope_static_refused :
    staticBound actual 1 (1 + Memory.frameNeedProg program) = false := by
  with_unfolding_all decide +kernel

open Passes.CompilerWholeScope (program actual) in
theorem scope_static_holds : staticBound actual 1 128 = true := by
  with_unfolding_all decide +kernel

/-! ## R3: no byte selection -/

open Passes.CompilerWholeScope (actual) in
theorem scope_bytes_refused : compileScalar actual.code = none := by
  with_unfolding_all decide +kernel

theorem reverting_accepted : (Compiler.compile 0 (Frag.init []) reverting).isSome = true := by
  decide +kernel

theorem reverting_bytes_refused :
    ((Compiler.compile 0 (Frag.init []) reverting).map (·.code)).bind compileScalar = none := by
  decide +kernel

/-! ## R4: the byte stack bound fails -/

theorem empty_capacity_refused :
    Scalar.stackBound [] ((List.replicate 1025 (0 : Scalar.Word)).length : Int) = false := by
  decide +kernel

end Solidity.Backend.CompilerEndpointWitnesses

#print axioms Solidity.Backend.CompilerEndpointWitnesses.empty_through_bytes
#print axioms Solidity.Backend.CompilerEndpointWitnesses.unsupported_refused
#print axioms Solidity.Backend.CompilerEndpointWitnesses.scope_static_refused
#print axioms Solidity.Backend.CompilerEndpointWitnesses.scope_bytes_refused
#print axioms Solidity.Backend.CompilerEndpointWitnesses.reverting_bytes_refused
#print axioms Solidity.Backend.CompilerEndpointWitnesses.empty_capacity_refused
