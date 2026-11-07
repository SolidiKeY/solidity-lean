import Solidity.Yul.LocalU8CompareHorizon
import Solidity.Yul.Checks.LocalU8Representation

/-! Nontrivial side-effecting comparison horizon controls.
Timeout prefixes may retain different writes in the two pipelines. -/
namespace Solidity.Yul.Checks.LocalU8CompareHorizon

theorem legacyObserved : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), (Solidity.Yul.LocalU8Compare.compare .eq Solidity.Yul.Checks.LocalU8Representation.assign Solidity.Yul.Checks.LocalU8Representation.readX .legacy 4 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world)).1 = .ok Solidity.Yul.Checks.LocalU8Representation.cleanFalse := by
  intro world
  simp only [Solidity.Yul.LocalU8Compare.compare_legacy,Solidity.Yul.Checks.LocalU8Representation.assign,Solidity.Yul.Checks.LocalU8Representation.readX,Solidity.Yul.Checks.LocalU8Representation.readArg,
    Solidity.Yul.LocalU8Expr.assign_step,Solidity.Yul.LocalU8Expr.local_read,
    Solidity.Yul.Checks.LocalU8Representation.initial,Solidity.Yul.Checks.LocalU8Representation.x,Solidity.Yul.Checks.LocalU8Representation.arg,Solidity.Yul.LocalValues.get,Solidity.Yul.LocalValues.set]
  rfl

theorem viaObserved : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), (Solidity.Yul.LocalU8Compare.compare .eq Solidity.Yul.Checks.LocalU8Representation.assign Solidity.Yul.Checks.LocalU8Representation.readX .viaIR 4 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world)).1 = .ok Solidity.Yul.Checks.LocalU8Representation.cleanTrue := by
  intro world
  simp only [Solidity.Yul.LocalU8Compare.compare_viaIR,Solidity.Yul.Checks.LocalU8Representation.assign,Solidity.Yul.Checks.LocalU8Representation.readX,Solidity.Yul.Checks.LocalU8Representation.readArg,
    Solidity.Yul.LocalU8Expr.assign_step,Solidity.Yul.LocalU8Expr.local_read,
    Solidity.Yul.Checks.LocalU8Representation.initial,Solidity.Yul.Checks.LocalU8Representation.x,Solidity.Yul.Checks.LocalU8Representation.arg,Solidity.Yul.LocalValues.get,Solidity.Yul.LocalValues.set]
  rfl

theorem legacyStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env) (extra : Nat), Solidity.Yul.LocalU8Compare.compare .eq Solidity.Yul.Checks.LocalU8Representation.assign Solidity.Yul.Checks.LocalU8Representation.readX .legacy (4+extra) (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) = Solidity.Yul.LocalU8Compare.compare .eq Solidity.Yul.Checks.LocalU8Representation.assign Solidity.Yul.Checks.LocalU8Representation.readX .legacy 4 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) := by
  intro world extra
  apply Solidity.Yul.LocalU8CompareHorizon.extension
  rw [legacyObserved]
  intro impossible
  cases impossible

theorem viaStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env) (extra : Nat), Solidity.Yul.LocalU8Compare.compare .eq Solidity.Yul.Checks.LocalU8Representation.assign Solidity.Yul.Checks.LocalU8Representation.readX .viaIR (4+extra) (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) = Solidity.Yul.LocalU8Compare.compare .eq Solidity.Yul.Checks.LocalU8Representation.assign Solidity.Yul.Checks.LocalU8Representation.readX .viaIR 4 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) := by
  intro world extra
  apply Solidity.Yul.LocalU8CompareHorizon.extension
  rw [viaObserved]
  intro impossible
  cases impossible

theorem invalidObserved : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), (Solidity.Yul.LocalU8Compare.compare .add Solidity.Yul.Checks.LocalU8Representation.readX Solidity.Yul.Checks.LocalU8Representation.readArg pipeline 3 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world)).1 = .error (.stuck "not a comparison") := by
  intro pipeline world
  cases pipeline with
  | legacy =>
    simp only [Solidity.Yul.LocalU8Compare.compare_legacy,Solidity.Yul.Checks.LocalU8Representation.readX,Solidity.Yul.Checks.LocalU8Representation.readArg,
      Solidity.Yul.LocalU8Expr.local_read,
      Solidity.Yul.Checks.LocalU8Representation.initial,Solidity.Yul.Checks.LocalU8Representation.x,Solidity.Yul.Checks.LocalU8Representation.arg,Solidity.Yul.LocalValues.get]
    rfl
  | viaIR =>
    simp only [Solidity.Yul.LocalU8Compare.compare_viaIR,Solidity.Yul.Checks.LocalU8Representation.readX,Solidity.Yul.Checks.LocalU8Representation.readArg,
      Solidity.Yul.LocalU8Expr.local_read,
      Solidity.Yul.Checks.LocalU8Representation.initial,Solidity.Yul.Checks.LocalU8Representation.x,Solidity.Yul.Checks.LocalU8Representation.arg,Solidity.Yul.LocalValues.get]
    rfl

theorem invalidStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env) (extra : Nat), Solidity.Yul.LocalU8Compare.compare .add Solidity.Yul.Checks.LocalU8Representation.readX Solidity.Yul.Checks.LocalU8Representation.readArg pipeline (3+extra) (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) = Solidity.Yul.LocalU8Compare.compare .add Solidity.Yul.Checks.LocalU8Representation.readX Solidity.Yul.Checks.LocalU8Representation.readArg pipeline 3 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) := by
  intro pipeline world extra
  apply Solidity.Yul.LocalU8CompareHorizon.extension
  rw [invalidObserved]
  intro impossible
  cases impossible

theorem legacyPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), Solidity.Yul.LocalU8Compare.compare .eq Solidity.Yul.Checks.LocalU8Representation.assign Solidity.Yul.Checks.LocalU8Representation.deep .legacy 4 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) = (.error .timeout,(Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world)) := by
  intro world
  rfl

theorem viaPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), Solidity.Yul.LocalU8Compare.compare .eq Solidity.Yul.Checks.LocalU8Representation.assign Solidity.Yul.Checks.LocalU8Representation.deep .viaIR 4 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) = (.error .timeout,Solidity.Yul.Checks.LocalU8Representation.initial 2 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) := by
  intro world
  rfl

theorem timeoutMayChange : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), Solidity.Yul.LocalU8Compare.compare .add Solidity.Yul.Checks.LocalU8Representation.readX Solidity.Yul.Checks.LocalU8Representation.readArg pipeline 1 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) ≠ Solidity.Yul.LocalU8Compare.compare .add Solidity.Yul.Checks.LocalU8Representation.readX Solidity.Yul.Checks.LocalU8Representation.readArg pipeline 3 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) := by
  intro pipeline world same
  have results := congrArg (fun run => run.1) same
  have right := invalidObserved pipeline world
  have left : (Solidity.Yul.LocalU8Compare.compare .add Solidity.Yul.Checks.LocalU8Representation.readX Solidity.Yul.Checks.LocalU8Representation.readArg pipeline 1 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world)).1 = .error .timeout := rfl
  dsimp only at results
  rw [left,right] at results
  cases results

#print axioms Solidity.Yul.LocalU8CompareHorizon.successor
#print axioms Solidity.Yul.LocalU8CompareHorizon.extension
#print axioms legacyObserved
#print axioms viaObserved
#print axioms legacyStable
#print axioms viaStable
#print axioms invalidObserved
#print axioms invalidStable
#print axioms legacyPartial
#print axioms viaPartial
#print axioms timeoutMayChange

end Solidity.Yul.Checks.LocalU8CompareHorizon
