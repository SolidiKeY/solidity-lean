import Solidity.Docs.ProseRatio.Policy

/-! The frozen code-relative prose laws. This proves the classified-line model;
lexer correspondence, policy provenance and merged-head CI remain external. -/
namespace Solidity.Docs

theorem prose_ratio_rule_sound : Solidity.Goals.proseRatioRuleSound := by
  intro A inst
  exact {
    decides := ProseRatio.decides
    rejects := ProseRatio.rejects
    rounding := ProseRatio.rounding
    byValue := ProseRatio.byValue
    zeroCode := ProseRatio.zeroCode
    unlisted := ProseRatio.unlisted
    growth := ProseRatio.growth
    uncounted := ProseRatio.uncounted
    generatedPadding := ProseRatio.generatedPadding
    auditsPadding := ProseRatio.auditsPadding
    codeFreePadding := ProseRatio.codeFreePadding
    segmentInert := ProseRatio.segmentInert
    shrinkFrozen := fun pol p key => (ProseRatio.shrinkValues pol p key).1
    shrinkProposed := fun pol p key => (ProseRatio.shrinkValues pol p key).2
    shrinkExact := ProseRatio.shrinkExact
    shrinkKeeps := ProseRatio.shrinkKeeps
    tighten := ProseRatio.tighten
    noReplacement := ProseRatio.noReplacement }

end Solidity.Docs
