import SolidityBridge.RoadmapV15.P10.NegationSourceConsumer
import SolidityBridge.RoadmapV15.P10.NegationBodyControls

/-! Inhabited typed source clients of the actual fetched body. The minimum
counterexample retains native wrapping and source failure simultaneously. -/
namespace SolidityBridge.RoadmapV15.P10.NegationSourceControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open NegationBodyControls

theorem source_values :
    (negationSourceResult positive (by decide)).val = -7 ∧
    (negationSourceResult negative (by decide)).val = 7 ∧
    (negationSourceResult zero (by decide)).val = 0 ∧
    (negationSourceResult maximum (by decide)).val = -((2^255 : Nat)-1 : Int) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem fetched_source_clients (valid : Array UInt256) :
    UnOp.evalT .neg (p := .int) rfl negative = some (negationSourceResult negative (by decide)) ∧
    Assembly.driverSteps 2 3 valid
      (negationBodyInput (WordPushFixtures.seed 6 true) WordPushFixtures.before
        WordPushFixtures.after negative [258,513]) = .ok (observed true negative [258,513]) ∧
    (observed true negative [258,513]).stack = [WordPushFixtures.u 7,
      WordPushFixtures.u 258,WordPushFixtures.u 513] ∧
    (observed true negative [258,513]).stack ≠ [WordPushFixtures.u 513,
      WordPushFixtures.u 258,WordPushFixtures.u 7] := by
  have h := negation_source_execution valid (WordPushFixtures.seed 6 true)
    WordPushFixtures.before WordPushFixtures.after negative [258,513] (by decide)
    NegationBodyControls.fits (by decide) (by change 6 ≤ 6;decide) 0
  have same : negationBodyOutput (WordPushFixtures.seed 6 true)
      WordPushFixtures.before WordPushFixtures.after negative [258,513] =
      observed true negative [258,513] := by
    first | rfl | decide | omega
  exact ⟨h.1,h.2.1.trans (congrArg Except.ok same),by decide,by decide⟩

theorem minimum_is_not_a_success (valid : Array UInt256) :
    UnOp.evalT .neg (p := .int) rfl Scalar.minimumInt = none ∧
    Assembly.driverSteps 2 3 valid
      (negationBodyInput (WordPushFixtures.seed 6 false) WordPushFixtures.before
        WordPushFixtures.after Scalar.minimumInt [258,513]) =
      .ok (observed false Scalar.minimumInt [258,513]) ∧
    ¬ Scalar.minimumInt ≠ Scalar.minimumInt := by
  exact ⟨negation_source_minimum,
    exact_budget valid false Scalar.minimumInt [258,513] (by decide),by decide⟩

#print axioms source_values
#print axioms fetched_source_clients
#print axioms minimum_is_not_a_success
end SolidityBridge.RoadmapV15.P10.NegationSourceControls
