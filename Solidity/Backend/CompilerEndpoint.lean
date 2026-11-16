import Solidity.Backend.Payments.CompilerExact
import Solidity.Backend.Passes.WholeProgram.Refusal

/-!
# The compiler endpoint: typed program and world to `Evm.run`

`compiler_endpoint_correct` composes the checked entry `Evm.Compiler.compile`
with its exact agreement `Compilation.correct_exact` into one statement,
`CompilerEndpoint`. The endpoint stops at `Evm.run` on the compiled
`List Evm.Instr` (user decision H389); bytes are a separate later goal.
It names two refusals, both decidable:

* **R1** `compile b F P = none`: no checked branch accepts the program.
* **R2** `refused r L frame = true`: a static resource check of the accepted
  result fails for the world's bounds `L` and `frame` (no state, no machine);
  then no world with those bounds is an `Input`, which the stage
  `StaticStage refused` proves rather than assumes.

Past the refusals every accepted world agrees exactly with `Evm.run r.code m`
(`AgreesExact`: both succeed in related states, both revert, or the typed run
diverges and the machine faults; no payment disjunct).

R2 is sound, not complete: a world that passes the static check may still fail
the dynamic part of `Input` (state and heap representation, allocation room,
the copy bound), and then the agreement clause holds vacuously for it. The
dynamic part is the endpoint's world premise, not a refusal.

`CompilerEndpointWith refused` is the statement for any static check, and
`compiler_endpoint_of_stages` proves it from `StaticStage refused`.
`CompilerEndpoint` instantiates it with `Passes.WholeProgram.staticRefused`
(b1-intrinsic-stage: the array bound `L` against `Lmax`, the locals and the
reserved frame on every branch), whose stage is `staticRefused_input`.
-/
namespace Solidity.Backend

open Evm Evm.Compiler

/-- A static check of an accepted result over the world's bounds `L frame`;
`true` refuses. -/
abbrev StaticCheck : Type :=
  ∀ {C : Contract} {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Solidity.Prog C Γ Δ},
    Compilation b F P → Nat → Nat → Bool

/-- The R2 stage: a refused result has no accepted world with those bounds. -/
def StaticStage (refused : StaticCheck) : Prop :=
  ∀ {C : Contract} {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Solidity.Prog C Γ Δ}
    (r : Compilation b F P) (L frame : Nat) (base : Nat → Fin W) (σ : State C Γ) (m : Machine),
    refused r L frame = true → ¬ r.Input L frame base σ m

/-- The endpoint over a static check: the checked entry refuses (R1), or it
accepts `r` and, for every world bound `L frame`, the static check refuses
and no world with those bounds is accepted (R2), or the check passes and
every accepted world agrees exactly with `Evm.run r.code m`. -/
def CompilerEndpointWith (refused : StaticCheck) : Prop :=
  ∀ {C : Contract} {Γ Δ : Ctx} (b : Nat) (F : Frag Γ) (P : Solidity.Prog C Γ Δ),
    Compiler.compile b F P = none ∨
    ∃ r : Compilation b F P, Compiler.compile b F P = some r ∧
      ∀ L frame : Nat,
        (refused r L frame = true ∧
          ∀ (base : Nat → Fin W) (σ : State C Γ) (m : Machine), ¬ r.Input L frame base σ m) ∨
        (refused r L frame = false ∧
          ∀ (base : Nat → Fin W) (σ : State C Γ) (m : Machine),
            r.Input L frame base σ m → r.AgreesExact L frame base σ m)

/-- The endpoint from its static stage; the agreement is `correct_exact`. -/
theorem compiler_endpoint_of_stages (refused : StaticCheck) (stage : StaticStage refused) :
    CompilerEndpointWith refused := by
  intro C Γ Δ b F P
  cases Compiler.compile b F P with
  | none => exact .inl rfl
  | some r =>
    refine .inr ⟨r, rfl, fun L frame => ?_⟩
    cases check : refused r L frame
    · exact .inr ⟨check, fun base σ m h => r.correct_exact h⟩
    · exact .inl ⟨check, fun base σ m => stage r L frame base σ m check⟩

/-- The R2 stage of b1-intrinsic-stage's static check. -/
theorem static_stage : StaticStage Passes.WholeProgram.staticRefused :=
  fun r _ _ _ _ _ h => Passes.WholeProgram.staticRefused_input r h

/-- **The compiler endpoint**, typed program and world to `Evm.run`, with the
refusals R1 (the checked entry refuses) and R2 (`WholeProgram.staticRefused`). -/
def CompilerEndpoint : Prop := CompilerEndpointWith Passes.WholeProgram.staticRefused

/-- `CompilerEndpoint` holds: `correct_exact` past the refusals, and
`staticRefused_input` for R2. No stage is assumed. -/
theorem compiler_endpoint_correct : CompilerEndpoint :=
  compiler_endpoint_of_stages Passes.WholeProgram.staticRefused static_stage

end Solidity.Backend

#print axioms Solidity.Backend.compiler_endpoint_correct
#print axioms Solidity.Backend.compiler_endpoint_of_stages
#print axioms Solidity.Backend.static_stage
