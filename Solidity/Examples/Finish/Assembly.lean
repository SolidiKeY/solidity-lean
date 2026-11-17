import Solidity.Finish.Assembly

/-! Checks for `Solidity.Finish.project_finished_of_open` and the audit of the
finish contract (H798). Not a finish claim: `Solidity.Finish.project_finished`
stays undeclared until fl-project-finished. -/

namespace Solidity.Finish.Examples

/-- info: 'Solidity.Finish.project_finished_of_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Finish.project_finished_of_open

-- Not the finish claim.
open Lean in
run_cmd do
  if (← getEnv).contains `Solidity.Finish.project_finished then
    throwError "project_finished must not be declared by the assembly"

-- The two open components enter as hypotheses, exactly the goal constants.
example : Solidity.Goals.lowerLoopsCorrect → Solidity.Goals.runCarriesPanicCodes →
    Solidity.Goals.projectFinished := project_finished_of_open

/-! Audit: `compilerTotal` covers exactly the accepted `ProgOk []` domain, at
every bound `L ≤ Lmax`, from the fresh frame `Frag.init`. -/
example (C : Solidity.Contract) (Γ Δ : Solidity.Ctx) (P : Solidity.Prog C Γ Δ)
    (hP : Solidity.Backend.AbiWorld.PublicCompilerTotal.ProgOk [] P)
    (b L frame : Nat) (hL : L ≤ Solidity.Evm.Lmax) :
    ∃ r : Solidity.Evm.Compiler.Compilation b (Solidity.Evm.Frag.init Γ) P,
      Solidity.Evm.Compiler.compile b (Solidity.Evm.Frag.init Γ) P = some r ∧
      Solidity.Backend.Passes.WholeProgram.staticRefused r L frame = false :=
  Solidity.Backend.compiler_total C Γ Δ P hP b L frame hL

/-! Audit: the endpoint's refusals are R1 (`compile = none`) and R2
(`staticRefused`, under which no world satisfies `Input`); past them, every
dynamic world premise `r.Input L frame base σ m` yields `AgreesExact`, the
statement about `Evm.run` (no bytes, no external EVM). -/
example : Solidity.Goals.compilerEndpointCorrect =
    Solidity.Backend.CompilerEndpointWith
      Solidity.Backend.Passes.WholeProgram.staticRefused := rfl

example {C : Solidity.Contract} {Γ Δ : Solidity.Ctx} (b : Nat)
    (F : Solidity.Evm.Frag Γ) (P : Solidity.Prog C Γ Δ) :
    Solidity.Evm.Compiler.compile b F P = none ∨
    ∃ r : Solidity.Evm.Compiler.Compilation b F P,
      Solidity.Evm.Compiler.compile b F P = some r ∧ ∀ L frame : Nat,
        (Solidity.Backend.Passes.WholeProgram.staticRefused r L frame = true ∧
          ∀ base σ m, ¬ r.Input L frame base σ m) ∨
        (Solidity.Backend.Passes.WholeProgram.staticRefused r L frame = false ∧
          ∀ base σ m, r.Input L frame base σ m → r.AgreesExact L frame base σ m) :=
  Solidity.Backend.compiler_endpoint_correct b F P

end Solidity.Finish.Examples
