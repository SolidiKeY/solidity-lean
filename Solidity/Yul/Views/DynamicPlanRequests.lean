import Solidity.Yul.Views.DynamicFrameLaws

namespace Solidity.Yul.Views

/-- Provenance of every plan in a successfully prepared finite request list;
no computation of source updates or assumed final-state law is needed. -/
theorem packedPlanRequests {D L T ps ts} (qs : List PackedSlotRequest)
    (plans : List (@PackedSlotPlan D L T ps ts))
    (prepared : qs.mapM (preparePackedSlot ps ts) = some plans) :
    plans.map PackedSlotPlan.request = qs := by
  induction qs generalizing plans with
  | nil =>
    change some [] = some plans at prepared
    cases prepared
    rfl
  | cons q qs ih =>
    rw [List.mapM_cons] at prepared
    obtain ⟨head,hh,rest⟩ := Option.bind_eq_some_iff.mp prepared
    obtain ⟨tail,ht,result⟩ := Option.bind_eq_some_iff.mp rest
    change some (head::tail) = some plans at result
    cases result
    rw [List.map_cons,preparePackedSlot_request q head hh,ih tail ht]

end Solidity.Yul.Views
