import Solidity.Yul.LocalU8Horizon
import Solidity.Yul.Checks.LocalU8Representation

/-! Terminal stability controls over inhabited raw checked-u8 certificates.
The two timeout counterexamples make the non-timeout premise observable. -/
namespace Solidity.Yul.Checks.LocalU8Horizon

theorem legacyStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env) (extra : Nat), Solidity.Yul.LocalU8Expr.eval Solidity.Yul.Checks.LocalU8Representation.order .legacy (5+extra) (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) = Solidity.Yul.LocalU8Expr.eval Solidity.Yul.Checks.LocalU8Representation.order .legacy 5 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) := by
  intro world extra
  apply Solidity.Yul.LocalU8Horizon.extension
  intro timeout
  have observed := Solidity.Yul.Checks.LocalU8Representation.legacyOrder world
  rw [timeout] at observed
  cases observed

theorem viaStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env) (extra : Nat), Solidity.Yul.LocalU8Expr.eval Solidity.Yul.Checks.LocalU8Representation.order .viaIR (5+extra) (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) = Solidity.Yul.LocalU8Expr.eval Solidity.Yul.Checks.LocalU8Representation.order .viaIR 5 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) := by
  intro world extra
  apply Solidity.Yul.LocalU8Horizon.extension
  intro timeout
  have observed := Solidity.Yul.Checks.LocalU8Representation.viaOrder world
  rw [timeout] at observed
  cases observed

theorem panicStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env) (extra : Nat), Solidity.Yul.LocalU8Expr.eval Solidity.Yul.Checks.LocalU8Representation.sum pipeline (3+extra) (Solidity.Yul.Checks.LocalU8Representation.initial 511 1 Solidity.Yul.Checks.LocalU8Representation.rawBool world) = Solidity.Yul.LocalU8Expr.eval Solidity.Yul.Checks.LocalU8Representation.sum pipeline 3 (Solidity.Yul.Checks.LocalU8Representation.initial 511 1 Solidity.Yul.Checks.LocalU8Representation.rawBool world) := by
  intro pipeline world extra
  apply Solidity.Yul.LocalU8Horizon.extension
  rw [Solidity.Yul.Checks.LocalU8Representation.overflow]
  intro impossible
  cases impossible

theorem assignmentStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env) (extra : Nat), Solidity.Yul.LocalU8Expr.eval Solidity.Yul.Checks.LocalU8Representation.assign pipeline (2+extra) (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) = Solidity.Yul.LocalU8Expr.eval Solidity.Yul.Checks.LocalU8Representation.assign pipeline 2 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) := by
  intro pipeline world extra
  apply Solidity.Yul.LocalU8Horizon.extension
  intro impossible
  cases impossible

theorem timeoutMayChange : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), Solidity.Yul.LocalU8Expr.eval Solidity.Yul.Checks.LocalU8Representation.assign pipeline 1 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) ≠ Solidity.Yul.LocalU8Expr.eval Solidity.Yul.Checks.LocalU8Representation.assign pipeline 2 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) := by
  intro pipeline world same
  have results := congrArg (fun run => run.1) same
  cases results

theorem zeroMayChange : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), Solidity.Yul.LocalU8Expr.eval Solidity.Yul.Checks.LocalU8Representation.readX pipeline 0 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) ≠ Solidity.Yul.LocalU8Expr.eval Solidity.Yul.Checks.LocalU8Representation.readX pipeline 1 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) := by
  intro pipeline world same
  have results := congrArg (fun run => run.1) same
  cases results

theorem flagStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env) (extra : Nat), ((Solidity.Yul.LocalU8Expr.eval Solidity.Yul.Checks.LocalU8Representation.order pipeline (5+extra) (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world)).2.1.get Solidity.Yul.Checks.LocalU8Representation.flag) = Solidity.Yul.Checks.LocalU8Representation.rawBool := by
  intro pipeline world extra
  cases pipeline with
  | legacy =>
    rw [legacyStable world extra]
    exact Solidity.Yul.Checks.LocalU8Representation.flagRetained .legacy world
  | viaIR =>
    rw [viaStable world extra]
    exact Solidity.Yul.Checks.LocalU8Representation.flagRetained .viaIR world

theorem unsupportedMul : ¬ Nonempty (Solidity.Yul.LocalU8Expr.Supported Solidity.Yul.Checks.LocalU8Representation.env Solidity.Yul.Checks.LocalU8Representation.Ctx (.binary .mul (.local Solidity.Yul.Checks.LocalU8Representation.x) (.local Solidity.Yul.Checks.LocalU8Representation.arg))) := by
  intro witness
  rcases witness with ⟨proof⟩
  cases proof

#print axioms Solidity.Yul.LocalU8Horizon.successor
#print axioms Solidity.Yul.LocalU8Horizon.extension
#print axioms legacyStable
#print axioms viaStable
#print axioms panicStable
#print axioms assignmentStable
#print axioms timeoutMayChange
#print axioms zeroMayChange
#print axioms flagStable
#print axioms unsupportedMul

end Solidity.Yul.Checks.LocalU8Horizon
