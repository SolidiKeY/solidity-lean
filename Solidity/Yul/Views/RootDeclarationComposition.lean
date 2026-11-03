import Solidity.Yul.Views.RootDeclarationStore

namespace Solidity.Yul.Views.Controls

def rootInitialCore : ResidualCompanion rootEnv.layout rootEnv.lay rootEnv.lay complementCarrierOwnership := ⟨rootState.2.ex,rootResidual⟩
def rootCallerCore : ResidualCompanion rootEnv.layout rootEnv.lay rootEnv.lay complementCarrierOwnership := ⟨rootFrame6.1.2.2.ex,rootFrame6.2⟩
def rootCore0 : ResidualCompanion rootEnv.layout rootEnv.lay rootEnv.lay complementCarrierOwnership := ⟨rootFrame0.1.2.2.ex,rootFrame0.2⟩
theorem rootCore0_step : rootCore0 = applyPackedSlot rootInitialCore rootPlan0 :=
  (packedSourceStep_companion packedStepFrame rootPlan0 rootState rootResidual rfl).2.2.2.2.2
def rootCore1 : ResidualCompanion rootEnv.layout rootEnv.lay rootEnv.lay complementCarrierOwnership := ⟨rootFrame1.1.2.2.ex,rootFrame1.2⟩
theorem rootCore1_step : rootCore1 = applyPackedSlot rootCore0 rootPlan1 :=
  (packedSourceStep_companion packedStepFrame rootPlan1 rootFrame0.1.2 rootFrame0.2 rfl).2.2.2.2.2
def rootCore2 : ResidualCompanion rootEnv.layout rootEnv.lay rootEnv.lay complementCarrierOwnership := ⟨rootFrame2.1.2.2.ex,rootFrame2.2⟩
theorem rootCore2_step : rootCore2 = applyPackedSlot rootCore1 rootPlan2 :=
  (packedSourceStep_companion packedStepFrame rootPlan2 rootFrame1.1.2 rootFrame1.2 rfl).2.2.2.2.2
def rootCore3 : ResidualCompanion rootEnv.layout rootEnv.lay rootEnv.lay complementCarrierOwnership := ⟨rootFrame3.1.2.2.ex,rootFrame3.2⟩
theorem rootCore3_step : rootCore3 = applyPackedSlot rootCore2 rootPlan3 :=
  (packedSourceStep_companion packedStepFrame rootPlan3 rootFrame2.1.2 rootFrame2.2 rfl).2.2.2.2.2
def rootCore4 : ResidualCompanion rootEnv.layout rootEnv.lay rootEnv.lay complementCarrierOwnership := ⟨rootFrame4.1.2.2.ex,rootFrame4.2⟩
theorem rootCore4_step : rootCore4 = applyPackedSlot rootCore3 rootPlan4 :=
  (packedSourceStep_companion packedStepFrame rootPlan4 rootFrame3.1.2 rootFrame3.2 rfl).2.2.2.2.2
def rootCore5 : ResidualCompanion rootEnv.layout rootEnv.lay rootEnv.lay complementCarrierOwnership := ⟨rootFrame5.1.2.2.ex,rootFrame5.2⟩
theorem rootCore5_step : rootCore5 = applyPackedSlot rootCore4 rootPlan5 :=
  (packedSourceStep_companion packedStepFrame rootPlan5 rootFrame4.1.2 rootFrame4.2 rfl).2.2.2.2.2
def rootCore6 : ResidualCompanion rootEnv.layout rootEnv.lay rootEnv.lay complementCarrierOwnership := ⟨rootFrame6.1.2.2.ex,rootFrame6.2⟩
theorem rootCore6_step : rootCore6 = applyPackedSlot rootCore5 rootPlan6 :=
  (packedSourceStep_companion packedStepFrame rootPlan6 rootFrame5.1.2 rootFrame5.2 rfl).2.2.2.2.2
theorem root_actual_sequence : rootCallerCore = runPackedSlots rootInitialCore [rootPlan0,rootPlan1,rootPlan2,rootPlan3,rootPlan4,rootPlan5,rootPlan6] := by
  change rootCore6 = _
  simp only [runPackedSlots]
  rw [rootCore6_step,rootCore5_step,rootCore4_step,rootCore3_step,rootCore2_step,rootCore1_step,rootCore0_step]

theorem root_slot_partition : rootRegistry account =
    selectedSlotPaths (rootRegistry account) 0 ++ (selectedSlotPaths (rootRegistry account) 1 ++ (selectedSlotPaths (rootRegistry account) 2 ++ (selectedSlotPaths (rootRegistry account) 3 ++ (selectedSlotPaths (rootRegistry account) 4 ++ (selectedSlotPaths (rootRegistry account) 5 ++ (selectedSlotPaths (rootRegistry account) 6)))))) := rfl

theorem root_actual_store_decode : finiteWriteback (rootRegistry account) rootSnapshot rootInitialStore =
    some (rootFrame6.1.2.2.ex.world.accounts account).storage := by
  have step0 := packedPersistent_writeback_exact rootInitialCore rootPlan0 rfl
  have req0 : rootPlan0.request = ⟨false,account,0,rootRaw0⟩ := preparePackedSlot_request _ _ (Option.get_mem root_ready0)
  simp only [req0] at step0
  change finiteWriteback (selectedSlotPaths (rootRegistry account) 0) (fun _ => rootRaw0) rootInitialStore =
    some (rootFrame0.1.2.2.ex.world.accounts account).storage at step0
  have step1 := packedPersistent_writeback_exact (⟨rootFrame0.1.2.2.ex,rootFrame0.2⟩ : ResidualCompanion rootEnv.layout rootEnv.lay rootEnv.lay complementCarrierOwnership) rootPlan1 rfl
  have req1 : rootPlan1.request = ⟨false,account,1,rootRaw1⟩ := preparePackedSlot_request _ _ (Option.get_mem root_ready1)
  simp only [req1] at step1
  change finiteWriteback (selectedSlotPaths (rootRegistry account) 1) (fun _ => rootRaw1) (rootFrame0.1.2.2.ex.world.accounts account).storage =
    some (rootFrame1.1.2.2.ex.world.accounts account).storage at step1
  have step2 := packedPersistent_writeback_exact (⟨rootFrame1.1.2.2.ex,rootFrame1.2⟩ : ResidualCompanion rootEnv.layout rootEnv.lay rootEnv.lay complementCarrierOwnership) rootPlan2 rfl
  have req2 : rootPlan2.request = ⟨false,account,2,rootRaw2⟩ := preparePackedSlot_request _ _ (Option.get_mem root_ready2)
  simp only [req2] at step2
  change finiteWriteback (selectedSlotPaths (rootRegistry account) 2) (fun _ => rootRaw2) (rootFrame1.1.2.2.ex.world.accounts account).storage =
    some (rootFrame2.1.2.2.ex.world.accounts account).storage at step2
  have step3 := packedPersistent_writeback_exact (⟨rootFrame2.1.2.2.ex,rootFrame2.2⟩ : ResidualCompanion rootEnv.layout rootEnv.lay rootEnv.lay complementCarrierOwnership) rootPlan3 rfl
  have req3 : rootPlan3.request = ⟨false,account,3,rootRaw3⟩ := preparePackedSlot_request _ _ (Option.get_mem root_ready3)
  simp only [req3] at step3
  change finiteWriteback (selectedSlotPaths (rootRegistry account) 3) (fun _ => rootRaw3) (rootFrame2.1.2.2.ex.world.accounts account).storage =
    some (rootFrame3.1.2.2.ex.world.accounts account).storage at step3
  have step4 := packedPersistent_writeback_exact (⟨rootFrame3.1.2.2.ex,rootFrame3.2⟩ : ResidualCompanion rootEnv.layout rootEnv.lay rootEnv.lay complementCarrierOwnership) rootPlan4 rfl
  have req4 : rootPlan4.request = ⟨false,account,4,rootRaw4⟩ := preparePackedSlot_request _ _ (Option.get_mem root_ready4)
  simp only [req4] at step4
  change finiteWriteback (selectedSlotPaths (rootRegistry account) 4) (fun _ => rootRaw4) (rootFrame3.1.2.2.ex.world.accounts account).storage =
    some (rootFrame4.1.2.2.ex.world.accounts account).storage at step4
  have step5 := packedPersistent_writeback_exact (⟨rootFrame4.1.2.2.ex,rootFrame4.2⟩ : ResidualCompanion rootEnv.layout rootEnv.lay rootEnv.lay complementCarrierOwnership) rootPlan5 rfl
  have req5 : rootPlan5.request = ⟨false,account,5,rootRaw5⟩ := preparePackedSlot_request _ _ (Option.get_mem root_ready5)
  simp only [req5] at step5
  change finiteWriteback (selectedSlotPaths (rootRegistry account) 5) (fun _ => rootRaw5) (rootFrame4.1.2.2.ex.world.accounts account).storage =
    some (rootFrame5.1.2.2.ex.world.accounts account).storage at step5
  have step6 := packedPersistent_writeback_exact (⟨rootFrame5.1.2.2.ex,rootFrame5.2⟩ : ResidualCompanion rootEnv.layout rootEnv.lay rootEnv.lay complementCarrierOwnership) rootPlan6 rfl
  have req6 : rootPlan6.request = ⟨false,account,6,rootRaw6⟩ := preparePackedSlot_request _ _ (Option.get_mem root_ready6)
  simp only [req6] at step6
  change finiteWriteback (selectedSlotPaths (rootRegistry account) 6) (fun _ => rootRaw6) (rootFrame5.1.2.2.ex.world.accounts account).storage =
    some (rootFrame6.1.2.2.ex.world.accounts account).storage at step6
  have input (q : Roadmap.Word) : ∀ c ∈ selectedSlotPaths (rootRegistry account) q, rootSnapshot c.slot = rootSnapshot q := by
    intro c member
    rw [((selectedSlotPaths_mem _ _ c).mp member).2]
  rw [root_slot_partition,
    finiteWriteback_append,
    finiteWriteback_inputs (selectedSlotPaths (rootRegistry account) 0) rootSnapshot (fun _ => rootRaw0) (by intro c member; rw [input 0 c member]; rfl),step0,Option.bind_some,
    finiteWriteback_append,
    finiteWriteback_inputs (selectedSlotPaths (rootRegistry account) 1) rootSnapshot (fun _ => rootRaw1) (by intro c member; rw [input 1 c member]; rfl),step1,Option.bind_some,
    finiteWriteback_append,
    finiteWriteback_inputs (selectedSlotPaths (rootRegistry account) 2) rootSnapshot (fun _ => rootRaw2) (by intro c member; rw [input 2 c member]; rfl),step2,Option.bind_some,
    finiteWriteback_append,
    finiteWriteback_inputs (selectedSlotPaths (rootRegistry account) 3) rootSnapshot (fun _ => rootRaw3) (by intro c member; rw [input 3 c member]; rfl),step3,Option.bind_some,
    finiteWriteback_append,
    finiteWriteback_inputs (selectedSlotPaths (rootRegistry account) 4) rootSnapshot (fun _ => rootRaw4) (by intro c member; rw [input 4 c member]; rfl),step4,Option.bind_some,
    finiteWriteback_append,
    finiteWriteback_inputs (selectedSlotPaths (rootRegistry account) 5) rootSnapshot (fun _ => rootRaw5) (by intro c member; rw [input 5 c member]; rfl),step5,Option.bind_some,
    finiteWriteback_inputs (selectedSlotPaths (rootRegistry account) 6) rootSnapshot (fun _ => rootRaw6) (by intro c member; rw [input 6 c member]; rfl),step6]

theorem root_pure_equals_actual_store : rootStore.1 = (rootFrame6.1.2.2.ex.world.accounts account).storage := by
  have step : rootChecked.storeWriteback rootSnapshot rootInitialStore = some rootStore := Option.get_mem root_store_ready
  unfold CheckedRootDeclarations.storeWriteback packedStoreWriteback at step
  obtain ⟨out,decoded,same⟩ := Option.map_eq_some_iff.mp step
  have cells := congrArg Prod.fst same
  change out = rootStore.1 at cells
  rw [cells] at decoded
  change finiteWriteback (rootRegistry account) rootSnapshot rootInitialStore = some rootStore.1 at decoded
  rw [root_actual_store_decode] at decoded
  exact (Option.some.inj decoded).symm

theorem root_actual_full_reencode : finiteEncode rootChecked.registrations
    (rootFrame6.1.2.2.ex.world.accounts account).storage rootStore.2 = some rootSnapshot := by
  rw [← root_pure_equals_actual_store]
  exact root_store_full_reencode

end Solidity.Yul.Views.Controls
