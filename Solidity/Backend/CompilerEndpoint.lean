import Solidity.Backend.Payments.CompilerExact

/-!
# The compiler endpoint: typed program and world to `Evm.run`

`compiler_endpoint_correct` composes the checked entry `Evm.Compiler.compile`
with its exact agreement `Compilation.correct_exact` into one statement,
`CompilerEndpoint`. The endpoint stops at `Evm.run` on the compiled
`List Evm.Instr` (user decision H389); bytes are a separate later goal.
Every place where the chain stops is a named, decidable refusal:

* **R1** `compile b F P = none`: no checked branch accepts the program.
* **R2** `refused r L frame = true`: a static resource check of the accepted
  result fails for the world's bounds `L` and `frame` (no state, no machine);
  then no world with those bounds is an `Input`, which the stage
  `StaticStage refused` proves rather than assumes.

Past the refusals every accepted world agrees exactly with `Evm.run r.code m`
(`AgreesExact`: both succeed in related states, both revert, or the typed run
diverges and the machine faults; no payment disjunct).

`CompilerEndpointWith refused` is the statement for any static check;
`compiler_endpoint_of_stages` proves it from `StaticStage refused`.
`CompilerEndpoint` instantiates it with `Endpoint.frameRefused`, the bound that
`Input` states literally per branch. The b1-intrinsic-stage check
`Passes.WholeProgram.staticRefused` (also the locals bound) has the same type
and, with its `staticRefused_input`, instantiates the same theorem.
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

namespace Endpoint

/-- The static bound `Input` states literally in each branch (core:
`L + pushes P ≤ Lmax`; memory branches: `b + requiredFrame ≤ frame`); the
reference-array and fixed-memory branches state none. -/
def frameRefused : StaticCheck := fun {_ b _ _ _ P} r L frame =>
  match r with
  | .core _ _ => decide (Lmax < L + Evm.Prog.pushes P)
  | .referenceArrays _ | .fixedMemory _ => false
  | r => decide (frame < b + r.requiredFrame)

/-- Every accepted world passes `frameRefused`. -/
theorem frameRefused_of_input {C : Contract} {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ}
    {P : Solidity.Prog C Γ Δ} (r : Compilation b F P) {base : Nat → Fin W}
    {σ : State C Γ} {m : Machine} (h : r.Input L frame base σ m) :
    frameRefused r L frame = false := by
  cases r <;>
    simp only [frameRefused, Compilation.requiredFrame, decide_eq_false_iff_not, Nat.not_lt] <;>
    first | exact h.2 | exact h.2.1 | rfl

theorem frame_stage : StaticStage frameRefused := by
  intro C b Γ Δ F P r L frame base σ m check h
  have passes : frameRefused r L frame = false := frameRefused_of_input r h
  exact Bool.false_ne_true (passes.symm.trans check)

end Endpoint

/-- **The compiler endpoint**, typed program and world to `Evm.run`, with the
refusals R1 (the checked entry refuses) and R2 (`frameRefused`). -/
def CompilerEndpoint : Prop := CompilerEndpointWith Endpoint.frameRefused

theorem compiler_endpoint_correct : CompilerEndpoint :=
  compiler_endpoint_of_stages Endpoint.frameRefused Endpoint.frame_stage

end Solidity.Backend

#print axioms Solidity.Backend.compiler_endpoint_correct
#print axioms Solidity.Backend.compiler_endpoint_of_stages
#print axioms Solidity.Backend.Endpoint.frame_stage
