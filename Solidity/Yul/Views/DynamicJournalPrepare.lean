import Solidity.Yul.Views.DynamicNegativeControls
import Solidity.Yul.Views.DynamicPlanRequests

-- Serialize concrete proof elaboration to bound pending computed-state memory.
set_option Elab.async false

namespace Solidity.Yul.Views.Controls

/-- This companion scalar's declared transient bank is checked below. No
claim of dynamic-array transient declaration layout follows from reuse. -/
def dynTempRegistry (a : Roadmap.Address) : List (ScalarPath dynEnv.layout (dynEnv.lay a)) :=
  [⟨dynPath "temp",0,intField unsigned16 0 (by decide),intCodec _ unsigned16 0 (by decide),.int unsigned16⟩]

theorem dyn_temp_actual_bank : dynEnv.transientRoot (dynPath "temp") = true := rfl

def dynResidual := initialPackedComplement dynRegistry dynTempRegistry (fun k => dynSnapshot k.slot)
def dynCore : ResidualCompanion dynEnv.layout dynEnv.lay dynEnv.lay complementCarrierOwnership := ⟨dynStorageState.2.ex,dynResidual⟩
def dynRequests : List PackedSlotRequest := [⟨false,account,43,2⟩,⟨false,account,1000,12⟩,
  ⟨false,account,1001,dynMax⟩,⟨false,account,45,1⟩,⟨false,account,2000,33⟩]

theorem dyn_plans_ready : (dynRequests.mapM (preparePackedSlot dynRegistry dynTempRegistry)).isSome := by decide

def dynPlans := (dynRequests.mapM (preparePackedSlot dynRegistry dynTempRegistry)).get dyn_plans_ready

theorem dyn_plan_requests : dynPlans.map PackedSlotPlan.request = dynRequests :=
  packedPlanRequests dynRequests dynPlans (Option.get_mem dyn_plans_ready)

theorem dyn_caller_other_address : ∀ p ∈ dynPlans, (⟨2,by decide⟩ : Roadmap.Address) ≠ p.request.address := by
  intro p member
  have requested : p.request ∈ dynRequests := by
    rw [← dyn_plan_requests]; exact List.mem_map.mpr ⟨p,member,rfl⟩
  exact (by decide : ∀ q ∈ dynRequests, (⟨2,by decide⟩ : Roadmap.Address) ≠ q.address) p.request requested

theorem dyn_caller_other_slot (q : Roadmap.Word) (notUsed : ∀ r ∈ dynRequests, q ≠ r.slot) :
    ∀ p ∈ dynPlans, q ≠ p.request.slot := by
  intro p member
  apply notUsed p.request
  rw [← dyn_plan_requests]
  exact List.mem_map.mpr ⟨p,member,rfl⟩

theorem dyn_registry_no_temp : ∀ c ∈ dynRegistry account, dynPath "temp" ≠ c.path := by
  intro c member same
  have bank : dynEnv.transientRoot c.path = false := by
    rcases List.mem_append.mp member with rootMember | element
    · exact dynComputed.bank_agreement c rootMember
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at element
      rcases element with rfl | rfl | rfl <;> rfl
  rw [← same] at bank
  have yes : dynEnv.transientRoot (dynPath "temp") = true := rfl
  rw [yes] at bank
  cases bank

theorem dyn_temp_registry_no_xs : ∀ c ∈ dynTempRegistry account, dynPath "xs" ≠ c.path := by
  intro c member
  have same := List.mem_singleton.mp member
  subst c
  decide

end Solidity.Yul.Views.Controls
