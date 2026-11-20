import Solidity.Backend.CompilerEndpoint
import Solidity.Backend.Passes.CompilerV3

/-!
# The compiler endpoint over the v2 and v3 entries

`CompilerEndpointFor entry refused` is the statement of `CompilerEndpointWith`
with the checked entry as a parameter: any function returning a `Compilation`.
The frozen v1 statement is its instance at `Evm.Compiler.compile`
(`endpoint_for_v1`). `CompilerEndpointV2` is the instance at
`Passes.CompilerV2.compile`, which also accepts tuple-return calls, and
`compiler_endpoint_v2_correct` proves it: the agreement is the same
`Compilation.correct_exact`, the R2 stage the same `static_stage`.

`CompilerEndpointV3` is the instance at `Passes.CompilerV3.compile`, which adds
selected scalar recursive calls through `CompilerScalarBridge`.

`compiler_endpoint_correct`, `CompilerEndpoint` and the v1 entry are unchanged
(H937); v2 is additive (H314), and `CompilerV2.compile_of_v1` gives a
v1-accepted program the same result at the v2 entry.

The endpoint statement holds for every entry, also one that refuses
everything: what an entry accepts is stated by its own lemmas
(`CompilerV2.compile_of_selected`) and by witnesses
(`Passes.TupleReturnConsumer.V2`), not by the endpoint theorem.

`not_input_of_exhausted` records what no `Compilation`-valued entry can do:
a world whose typed run is `exhausted` is never an `Input`, because
`AgreesExact` has no exhaustion case.
-/
namespace Solidity.Backend

open Evm Evm.Compiler

/-- A checked entry: an optional `Compilation` of every typed program. -/
abbrev CheckedEntry : Type :=
  ∀ {C : Contract} (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Solidity.Prog C Γ Δ),
    Option (Compilation b F P)

/-- `CompilerEndpointWith` over a checked entry `entry`: R1 is
`entry b F P = none`; R2 and the agreement clause are unchanged. -/
def CompilerEndpointFor (entry : CheckedEntry) (refused : StaticCheck) : Prop :=
  ∀ {C : Contract} {Γ Δ : Ctx} (b : Nat) (F : Frag Γ) (P : Solidity.Prog C Γ Δ),
    @entry C b Γ Δ F P = none ∨
    ∃ r : Compilation b F P, @entry C b Γ Δ F P = some r ∧
      ∀ L frame : Nat,
        (refused r L frame = true ∧
          ∀ (base : Nat → Fin W) (σ : State C Γ) (m : Machine), ¬ r.Input L frame base σ m) ∨
        (refused r L frame = false ∧
          ∀ (base : Nat → Fin W) (σ : State C Γ) (m : Machine),
            r.Input L frame base σ m → r.AgreesExact L frame base σ m)

/-- The frozen v1 statement is the instance at the v1 entry. -/
theorem endpoint_for_v1 (refused : StaticCheck) :
    CompilerEndpointFor Compiler.compile refused ↔ CompilerEndpointWith refused :=
  Iff.rfl

/-- The endpoint of any checked entry from the static stage: every result is
a `Compilation`, so the agreement is `correct_exact`. -/
theorem compiler_endpoint_for_stages (entry : CheckedEntry) (refused : StaticCheck)
    (stage : StaticStage refused) : CompilerEndpointFor entry refused := by
  intro C Γ Δ b F P
  cases selected : @entry C b Γ Δ F P with
  | none => exact .inl selected
  | some r =>
    refine .inr ⟨r, selected, fun L frame => ?_⟩
    cases check : refused r L frame
    · exact .inr ⟨check, fun base σ m h => r.correct_exact h⟩
    · exact .inl ⟨check, fun base σ m => stage r L frame base σ m check⟩

/-- The goal statement `CompilerEndpoint` is the v1 instance of the lemma for
any entry: the same proof serves the b1 goal and v2. -/
example : CompilerEndpoint :=
  (endpoint_for_v1 Passes.WholeProgram.staticRefused).mp
    (compiler_endpoint_for_stages Compiler.compile Passes.WholeProgram.staticRefused static_stage)

/-- **The v2 compiler endpoint**: the endpoint over `CompilerV2.compile`, with
the same static check as v1. -/
def CompilerEndpointV2 : Prop :=
  CompilerEndpointFor Passes.CompilerV2.compile Passes.WholeProgram.staticRefused

/-- `CompilerEndpointV2` holds. No stage is assumed. -/
theorem compiler_endpoint_v2_correct : CompilerEndpointV2 :=
  compiler_endpoint_for_stages Passes.CompilerV2.compile Passes.WholeProgram.staticRefused
    static_stage

/-- **The v3 compiler endpoint**: the endpoint over `CompilerV3.compile`,
which also accepts selected scalar recursive calls. -/
def CompilerEndpointV3 : Prop :=
  CompilerEndpointFor Passes.CompilerV3.compile Passes.WholeProgram.staticRefused

/-- `CompilerEndpointV3` holds. No stage is assumed. -/
theorem compiler_endpoint_v3_correct : CompilerEndpointV3 :=
  compiler_endpoint_for_stages Passes.CompilerV3.compile Passes.WholeProgram.staticRefused
    static_stage

/-- The endpoint's accepted branch at one result, whatever produced it: for
every world bound the static check refuses and no world is accepted, or it
passes and every accepted world agrees exactly with `Evm.run`. -/
theorem compiler_endpoint_result {C : Contract} {Γ Δ : Ctx} {b : Nat} {F : Frag Γ}
    {P : Solidity.Prog C Γ Δ} (r : Compilation b F P) (L frame : Nat) :
    (Passes.WholeProgram.staticRefused r L frame = true ∧
      ∀ (base : Nat → Fin W) (σ : State C Γ) (m : Machine), ¬ r.Input L frame base σ m) ∨
    (Passes.WholeProgram.staticRefused r L frame = false ∧
      ∀ (base : Nat → Fin W) (σ : State C Γ) (m : Machine),
        r.Input L frame base σ m → r.AgreesExact L frame base σ m) := by
  cases check : Passes.WholeProgram.staticRefused r L frame
  · exact .inr ⟨rfl, fun base σ m h => r.correct_exact h⟩
  · exact .inl ⟨rfl, fun base σ m => static_stage r L frame base σ m check⟩

/-- No `Compilation` has an `Input` world whose typed run is exhausted:
`AgreesExact` has no exhaustion case. So no `Compilation`-valued entry, v1 or
v2, carries an exhausted source run to `Evm.run`. -/
theorem not_input_of_exhausted {C : Contract} {Γ Δ : Ctx} {b : Nat} {F : Frag Γ}
    {P : Solidity.Prog C Γ Δ} (r : Compilation b F P) {L frame : Nat}
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (exhausted : P.run σ = .error .exhausted) : ¬ r.Input L frame base σ m := by
  intro input
  rcases r.correct_exact input with ⟨o, _, ok, _⟩ | ⟨reverted | ⟨_, panicked⟩, _⟩ | ⟨diverged, _⟩
  · rw [exhausted] at ok; cases ok
  · rw [exhausted] at reverted; cases reverted
  · rw [exhausted] at panicked; cases panicked
  · rw [exhausted] at diverged; cases diverged

end Solidity.Backend

#print axioms Solidity.Backend.compiler_endpoint_v2_correct
#print axioms Solidity.Backend.compiler_endpoint_for_stages
#print axioms Solidity.Backend.not_input_of_exhausted
#print axioms Solidity.Backend.compiler_endpoint_result
#print axioms Solidity.Backend.compiler_endpoint_v3_correct
