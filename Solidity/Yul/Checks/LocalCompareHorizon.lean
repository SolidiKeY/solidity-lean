import Solidity.Yul.LocalCompareHorizon
import Solidity.Yul.Checks.LocalU8Representation

/-! Concrete mixed checked-u8/Boolean horizon controls over inhabited certificates.
Per-pipeline dirty results and partial timeout writes remain observable. -/
namespace Solidity.Yul.Checks.LocalCompareHorizon

theorem legacyObserved : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), Solidity.Yul.Checks.LocalU8Representation.conditional .legacy 8 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) = (.ok Solidity.Yul.Checks.LocalU8Representation.cleanFalse,(Solidity.Yul.Checks.LocalU8Representation.initial 2 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world)) := by
  intro world
  simp only [Solidity.Yul.Checks.LocalU8Representation.conditional,Solidity.Yul.LocalCompareControl.step,Solidity.Yul.Checks.LocalU8Representation.assign,Solidity.Yul.Checks.LocalU8Representation.readX,Solidity.Yul.Checks.LocalU8Representation.readArg,
    Solidity.Yul.LocalU8Compare.compare_legacy,Solidity.Yul.LocalU8Expr.assign_step,
    Solidity.Yul.LocalU8Expr.local_read,Solidity.Yul.Checks.LocalU8Representation.initial,Solidity.Yul.Checks.LocalU8Representation.x,Solidity.Yul.Checks.LocalU8Representation.arg,
    Solidity.Yul.LocalValues.get,Solidity.Yul.LocalValues.set]
  rfl

theorem viaObserved : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), Solidity.Yul.Checks.LocalU8Representation.conditional .viaIR 8 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) = (.ok Solidity.Yul.Checks.LocalU8Representation.rawBool,(Solidity.Yul.Checks.LocalU8Representation.initial 2 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world)) := by
  intro world
  rfl

theorem legacyStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env) (extra : Nat), Solidity.Yul.Checks.LocalU8Representation.conditional .legacy (8+extra) (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) = (.ok Solidity.Yul.Checks.LocalU8Representation.cleanFalse,(Solidity.Yul.Checks.LocalU8Representation.initial 2 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world)) := by
  intro world extra
  have terminal : (Solidity.Yul.Checks.LocalU8Representation.conditional .legacy 8 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world)).1 ≠ .error .timeout := by
    rw [legacyObserved]
    intro impossible
    cases impossible
  exact (Solidity.Yul.LocalCompareHorizon.extension _ _ _ _ _ _ .eq Solidity.Yul.Checks.LocalU8Representation.assign Solidity.Yul.Checks.LocalU8Representation.readX Solidity.Yul.Checks.LocalU8Representation.yes Solidity.Yul.Checks.LocalU8Representation.no .legacy 8 extra _ terminal).trans (legacyObserved world)

theorem viaStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env) (extra : Nat), Solidity.Yul.Checks.LocalU8Representation.conditional .viaIR (8+extra) (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) = (.ok Solidity.Yul.Checks.LocalU8Representation.rawBool,(Solidity.Yul.Checks.LocalU8Representation.initial 2 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world)) := by
  intro world extra
  have terminal : (Solidity.Yul.Checks.LocalU8Representation.conditional .viaIR 8 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world)).1 ≠ .error .timeout := by
    rw [viaObserved]
    intro impossible
    cases impossible
  exact (Solidity.Yul.LocalCompareHorizon.extension _ _ _ _ _ _ .eq Solidity.Yul.Checks.LocalU8Representation.assign Solidity.Yul.Checks.LocalU8Representation.readX Solidity.Yul.Checks.LocalU8Representation.yes Solidity.Yul.Checks.LocalU8Representation.no .viaIR 8 extra _ terminal).trans (viaObserved world)

theorem panicObserved : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), Solidity.Yul.LocalCompareControl.eval .eq Solidity.Yul.Checks.LocalU8Representation.sum Solidity.Yul.Checks.LocalU8Representation.readX Solidity.Yul.Checks.LocalU8Representation.yes Solidity.Yul.Checks.LocalU8Representation.no pipeline 6 (Solidity.Yul.Checks.LocalU8Representation.initial 511 1 Solidity.Yul.Checks.LocalU8Representation.rawBool world) = (.error (.revert (Solidity.Source.panicData Solidity.Source.PanicCode.arithmetic)),(Solidity.Yul.Checks.LocalU8Representation.initial 511 1 Solidity.Yul.Checks.LocalU8Representation.rawBool world)) := by
  intro pipeline world
  have sumRun : Solidity.Yul.LocalU8Expr.eval Solidity.Yul.Checks.LocalU8Representation.sum pipeline 3 (Solidity.Yul.Checks.LocalU8Representation.initial 511 1 Solidity.Yul.Checks.LocalU8Representation.rawBool world) = (.error (.revert (Solidity.Source.panicData Solidity.Source.PanicCode.arithmetic)),(Solidity.Yul.Checks.LocalU8Representation.initial 511 1 Solidity.Yul.Checks.LocalU8Representation.rawBool world)) := by
    apply Prod.ext
    · exact Solidity.Yul.Checks.LocalU8Representation.overflow pipeline world
    · cases pipeline <;> rfl
  cases pipeline with
  | legacy =>
    simp only [Solidity.Yul.LocalCompareControl.step,Solidity.Yul.LocalU8Compare.compare_legacy,Solidity.Yul.Checks.LocalU8Representation.readX,Solidity.Yul.LocalU8Expr.local_read,sumRun,Except.bind]
  | viaIR =>
    simp only [Solidity.Yul.LocalCompareControl.step,Solidity.Yul.LocalU8Compare.compare_viaIR,sumRun]

theorem panicStable : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env) (extra : Nat), Solidity.Yul.LocalCompareControl.eval .eq Solidity.Yul.Checks.LocalU8Representation.sum Solidity.Yul.Checks.LocalU8Representation.readX Solidity.Yul.Checks.LocalU8Representation.yes Solidity.Yul.Checks.LocalU8Representation.no pipeline (6+extra) (Solidity.Yul.Checks.LocalU8Representation.initial 511 1 Solidity.Yul.Checks.LocalU8Representation.rawBool world) = (.error (.revert (Solidity.Source.panicData Solidity.Source.PanicCode.arithmetic)),(Solidity.Yul.Checks.LocalU8Representation.initial 511 1 Solidity.Yul.Checks.LocalU8Representation.rawBool world)) := by
  intro pipeline world extra
  have terminal : (Solidity.Yul.LocalCompareControl.eval .eq Solidity.Yul.Checks.LocalU8Representation.sum Solidity.Yul.Checks.LocalU8Representation.readX Solidity.Yul.Checks.LocalU8Representation.yes Solidity.Yul.Checks.LocalU8Representation.no pipeline 6 (Solidity.Yul.Checks.LocalU8Representation.initial 511 1 Solidity.Yul.Checks.LocalU8Representation.rawBool world)).1 ≠ .error .timeout := by
    rw [panicObserved]
    intro impossible
    cases impossible
  exact (Solidity.Yul.LocalCompareHorizon.extension _ _ _ _ _ _ .eq Solidity.Yul.Checks.LocalU8Representation.sum Solidity.Yul.Checks.LocalU8Representation.readX Solidity.Yul.Checks.LocalU8Representation.yes Solidity.Yul.Checks.LocalU8Representation.no pipeline 6 extra _ terminal).trans (panicObserved pipeline world)

theorem legacyPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), Solidity.Yul.LocalCompareControl.eval .eq Solidity.Yul.Checks.LocalU8Representation.assign Solidity.Yul.Checks.LocalU8Representation.deep Solidity.Yul.Checks.LocalU8Representation.yes Solidity.Yul.Checks.LocalU8Representation.no .legacy 5 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) = (.error .timeout,(Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world)) := by
  intro world
  rfl

theorem viaPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), Solidity.Yul.LocalCompareControl.eval .eq Solidity.Yul.Checks.LocalU8Representation.assign Solidity.Yul.Checks.LocalU8Representation.deep Solidity.Yul.Checks.LocalU8Representation.yes Solidity.Yul.Checks.LocalU8Representation.no .viaIR 5 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) = (.error .timeout,(Solidity.Yul.Checks.LocalU8Representation.initial 2 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world)) := by
  intro world
  rfl

theorem timeoutMayChange : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), Solidity.Yul.LocalCompareControl.eval .eq Solidity.Yul.Checks.LocalU8Representation.assign Solidity.Yul.Checks.LocalU8Representation.deep Solidity.Yul.Checks.LocalU8Representation.yes Solidity.Yul.Checks.LocalU8Representation.no pipeline 5 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) ≠ Solidity.Yul.LocalCompareControl.eval .eq Solidity.Yul.Checks.LocalU8Representation.assign Solidity.Yul.Checks.LocalU8Representation.deep Solidity.Yul.Checks.LocalU8Representation.yes Solidity.Yul.Checks.LocalU8Representation.no pipeline 6 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) := by
  intro pipeline world same
  have final : Solidity.Yul.LocalCompareControl.eval .eq Solidity.Yul.Checks.LocalU8Representation.assign Solidity.Yul.Checks.LocalU8Representation.deep Solidity.Yul.Checks.LocalU8Representation.yes Solidity.Yul.Checks.LocalU8Representation.no pipeline 6 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) = (.ok Solidity.Yul.Checks.LocalU8Representation.rawBool,(Solidity.Yul.Checks.LocalU8Representation.initial 2 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world)) := by
    cases pipeline <;> rfl
  have terminal : (Solidity.Yul.LocalCompareControl.eval .eq Solidity.Yul.Checks.LocalU8Representation.assign Solidity.Yul.Checks.LocalU8Representation.deep Solidity.Yul.Checks.LocalU8Representation.yes Solidity.Yul.Checks.LocalU8Representation.no pipeline 6 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world)).1 ≠ .error .timeout := by
    rw [final]
    intro impossible
    cases impossible
  apply terminal
  rw [← same]
  cases pipeline <;> rfl

theorem dirtyProjection : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env) (extra : Nat), (Solidity.Yul.Checks.LocalU8Representation.conditional .viaIR (8+extra) (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world)).1.map Solidity.Yul.LocalValue.clean? = .ok none := by
  intro world extra
  rw [viaStable]
  rfl

#print axioms Solidity.Yul.LocalCompareHorizon.successor
#print axioms Solidity.Yul.LocalCompareHorizon.extension
#print axioms legacyObserved
#print axioms viaObserved
#print axioms legacyStable
#print axioms viaStable
#print axioms panicObserved
#print axioms panicStable
#print axioms legacyPartial
#print axioms viaPartial
#print axioms timeoutMayChange
#print axioms dirtyProjection

end Solidity.Yul.Checks.LocalCompareHorizon
