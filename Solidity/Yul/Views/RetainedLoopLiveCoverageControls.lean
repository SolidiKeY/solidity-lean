import Solidity.Yul.Views.RetainedLoopLiveCoverage
import Solidity.Yul.Views.RetainedLoopSequenceControls
import Solidity.Yul.Views.RetainedAliasReadControls

/-! Actual refreshed traversal reads three cells after growth and one after
shrink, for both existing loop-control fixtures. Coverage is obtained from the
published live traversal, without assuming the desired payload memberships. -/
namespace Solidity.Yul.Views.Controls

theorem rfll_present (G : Source.Glob agEnv) (flag : Bool) :
    rhFirst.val ∈ (rfliImage G flag).elements := by
  change rhFirst.val ∈ rhImage.elements
  rw [← rh_next_elements]
  exact rhFirst.property

theorem rfll_growth_length (G : Source.Glob agEnv) (flag : Bool) :
    aggregateSourceLengths packedStepFrame (rflswRun G flag).2 (rhHeader.registration account)=some 3 := by
  have root := RetainedCallerHeaders.element_registration (rfliImage G flag) rhFirst.val
    (rfll_present G flag) _ (rhFirst.val.2.header_member rhHeaderEntry)
  have member := RetainedLocalAliasImage.registration_mem_snapshot (rfliImage G flag) rhNextRaw _ root
  have view := RetainedLoopRefresh.source_view packedStepFrame (rfliImage G flag) rhNextRaw
    (rflswState G flag) rhOp rfl (rflw_checked G flag) (rflw_prepared G flag) _ member
  have reached : scalarPathView (rhHeader.registration account).path (rhHeader.registration account).codec
      (rhHeader.registration account).slot ((rflswRun G flag).2.2.ex.world.accounts account).storage rhNextRaw := by
    exact view
  have read := PathPrimitiveHeader.readLen_view (rhFirst.val.2.header rhHeaderEntry)
    packedStepFrame (rflswRun G flag).2 rhNextRaw (by rfl) reached
  change (Source.readLen packedStepFrame (agInner 0)).run (rflswRun G flag).2=
    (.ok 3,(rflswRun G flag).2) at read
  unfold aggregateSourceLengths
  have path : (rhHeader.registration account).path=agInner 0 := rfl
  rw [path,read]
  rfl

theorem rfll_shrink_length (G : Source.Glob agEnv) (flag : Bool) :
    aggregateSourceLengths packedStepFrame (rflqRun G flag).2 (rhHeader.registration account)=some 1 := by
  have root := RetainedCallerHeaders.element_registration (rfliImage G flag) rhFirst.val
    (rfll_present G flag) _ (rhFirst.val.2.header_member rhHeaderEntry)
  have member := RetainedLocalAliasImage.registration_mem_snapshot (rfliImage G flag) rflqRaw _ root
  have view := finiteAccountWrite_view account ((rfliImage G flag).snapshot rflqRaw) rflqRaw
    ((rflswState G flag).2.ex.apply rhOp) rflqOp
    ((packedSeparationCheck_iff _).mp rflq_checked) (rflq_prepared G flag) _ member
  have reached : scalarPathView (rhHeader.registration account).path (rhHeader.registration account).codec
      (rhHeader.registration account).slot ((rflqRun G flag).2.2.ex.world.accounts account).storage rflqRaw := by
    rw [rflq_result]
    exact view
  have read := PathPrimitiveHeader.readLen_view (rhFirst.val.2.header rhHeaderEntry)
    packedStepFrame (rflqRun G flag).2 rflqRaw (by rfl) reached
  change (Source.readLen packedStepFrame (agInner 0)).run (rflqRun G flag).2=
    (.ok 1,(rflqRun G flag).2) at read
  unfold aggregateSourceLengths
  have path : (rhHeader.registration account).path=agInner 0 := rfl
  rw [path,read]
  rfl

theorem rfll_growth_coverage (G : Source.Glob agEnv) (flag : Bool) :
    ∀ c∈rhHeader.elements agFixed account 3,c∈(rfliImage G flag).snapshot rhNextRaw := by
  have covered := RetainedLoopLiveCoverage.source_live packedStepFrame (rfliImage G flag) rhNextRaw
    (rflswState G flag) rhOp rfl (rflw_checked G flag) (rflw_prepared G flag) rhFirst.val (rfll_present G flag) rhHeaderEntry
  obtain ⟨length,read,members⟩ := covered
  change aggregateSourceLengths packedStepFrame (rflswRun G flag).2 (rhHeader.registration account)=some length at read
  have same : length=3 := Option.some.inj (read.symm.trans (rfll_growth_length G flag))
  subst length
  exact members

theorem rfll_shrink_coverage (G : Source.Glob agEnv) (flag : Bool) :
    ∀ c∈rhHeader.elements agFixed account 1,c∈(rfliImage G flag).snapshot rflqRaw := by
  have covered := RetainedLoopLiveCoverage.sequence_live packedStepFrame (rfliImage G flag) rflqRaw
    (rflswState G flag) rhOp rflqOp .timeout rfl rflq_checked (rflq_prepared G flag) rhFirst.val (rfll_present G flag) rhHeaderEntry
  obtain ⟨length,read,members⟩ := covered
  change aggregateSourceLengths packedStepFrame (rflqRun G flag).2 (rhHeader.registration account)=some length at read
  have same : length=1 := Option.some.inj (read.symm.trans (rfll_shrink_length G flag))
  subst length
  exact members

end Solidity.Yul.Views.Controls
