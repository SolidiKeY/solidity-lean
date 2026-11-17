import Solidity.Docs.ProseCalibrated.Allowance
import Solidity.Docs.ProseCalibrated.Classification
import Solidity.Docs.ProseCalibrated.Policy

/-! The calibrated prose laws, assembled from the allowance, classification and
policy modules. They are model arithmetic only: checker correspondence
(`ImplementationCorrespondence`) remains a separate, unproved obligation. -/
namespace Solidity.Docs

open Solidity.Goals.ProseCalibrated in
theorem prose_calibrated_ratio_rule_sound : Solidity.Goals.proseCalibratedRatioRuleSound where
  exact := ProseCalibrated.exact
  floorSum := ProseCalibrated.floorSum
  boundary := ProseCalibrated.boundary
  byValue := ProseCalibrated.byValue
  decides := ProseCalibrated.decides
  rejects := ProseCalibrated.rejects
  zeroEvaluation := ProseCalibrated.zeroEvaluation
  zeroAnchor := ProseCalibrated.zeroAnchor
  zeroNumerator := ProseCalibrated.zeroNumerator
  unseen := ProseCalibrated.unseen
  unavailable := ProseCalibrated.unavailable
  shrinkValues := ProseCalibrated.shrinkValues
  shrinkFrozen := ProseCalibrated.shrinkFrozen
  shrinkExact := ProseCalibrated.shrinkExact
  tighten := ProseCalibrated.tighten
  noReplacement := ProseCalibrated.noReplacement
  codeFreePadding := Classification.codeFreePadding
  generatedPadding := Classification.generatedPadding
  symmetricExclusion := Classification.symmetricExclusion
  headerInert := Classification.headerInert
  unverifiedCounted := Classification.unverifiedCounted
  identityMismatch := Classification.identityMismatch
  docstringSubset := Classification.docstringSubset
  sourceLocal := Classification.sourceLocal
  docsRepository := Classification.docsRepository

end Solidity.Docs
