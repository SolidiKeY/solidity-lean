import Solidity.Yul.Views.LayoutOriginStore

namespace Solidity.Yul.Views.Controls

def originInitialCore : ResidualCompanion originEnv.layout originEnv.lay originEnv.lay complementCarrierOwnership := ⟨originState.2.ex,originResidual⟩
def originCallerCore : ResidualCompanion originEnv.layout originEnv.lay originEnv.lay complementCarrierOwnership := ⟨originFrame6.1.2.2.ex,originFrame6.2⟩
def originCore0 : ResidualCompanion originEnv.layout originEnv.lay originEnv.lay complementCarrierOwnership := ⟨originFrame0.1.2.2.ex,originFrame0.2⟩
theorem originCore0_step : originCore0 = applyPackedSlot originInitialCore originPlan0 :=
  (packedSourceStep_companion packedStepFrame originPlan0 originState originResidual rfl).2.2.2.2.2
def originCore1 : ResidualCompanion originEnv.layout originEnv.lay originEnv.lay complementCarrierOwnership := ⟨originFrame1.1.2.2.ex,originFrame1.2⟩
theorem originCore1_step : originCore1 = applyPackedSlot originCore0 originPlan1 :=
  (packedSourceStep_companion packedStepFrame originPlan1 originFrame0.1.2 originFrame0.2 rfl).2.2.2.2.2
def originCore2 : ResidualCompanion originEnv.layout originEnv.lay originEnv.lay complementCarrierOwnership := ⟨originFrame2.1.2.2.ex,originFrame2.2⟩
theorem originCore2_step : originCore2 = applyPackedSlot originCore1 originPlan2 :=
  (packedSourceStep_companion packedStepFrame originPlan2 originFrame1.1.2 originFrame1.2 rfl).2.2.2.2.2
def originCore3 : ResidualCompanion originEnv.layout originEnv.lay originEnv.lay complementCarrierOwnership := ⟨originFrame3.1.2.2.ex,originFrame3.2⟩
theorem originCore3_step : originCore3 = applyPackedSlot originCore2 originPlan3 :=
  (packedSourceStep_companion packedStepFrame originPlan3 originFrame2.1.2 originFrame2.2 rfl).2.2.2.2.2
def originCore4 : ResidualCompanion originEnv.layout originEnv.lay originEnv.lay complementCarrierOwnership := ⟨originFrame4.1.2.2.ex,originFrame4.2⟩
theorem originCore4_step : originCore4 = applyPackedSlot originCore3 originPlan4 :=
  (packedSourceStep_companion packedStepFrame originPlan4 originFrame3.1.2 originFrame3.2 rfl).2.2.2.2.2
def originCore5 : ResidualCompanion originEnv.layout originEnv.lay originEnv.lay complementCarrierOwnership := ⟨originFrame5.1.2.2.ex,originFrame5.2⟩
theorem originCore5_step : originCore5 = applyPackedSlot originCore4 originPlan5 :=
  (packedSourceStep_companion packedStepFrame originPlan5 originFrame4.1.2 originFrame4.2 rfl).2.2.2.2.2
def originCore6 : ResidualCompanion originEnv.layout originEnv.lay originEnv.lay complementCarrierOwnership := ⟨originFrame6.1.2.2.ex,originFrame6.2⟩
theorem originCore6_step : originCore6 = applyPackedSlot originCore5 originPlan6 :=
  (packedSourceStep_companion packedStepFrame originPlan6 originFrame5.1.2 originFrame5.2 rfl).2.2.2.2.2
theorem origin_actual_sequence : originCallerCore = runPackedSlots originInitialCore [originPlan0,originPlan1,originPlan2,originPlan3,originPlan4,originPlan5,originPlan6] := by
  change originCore6 = _
  simp only [runPackedSlots]
  rw [originCore6_step,originCore5_step,originCore4_step,originCore3_step,originCore2_step,originCore1_step,originCore0_step]

theorem origin_slot_partition : originRegistry account =
    selectedSlotPaths (originRegistry account) 42 ++ (selectedSlotPaths (originRegistry account) 43 ++ (selectedSlotPaths (originRegistry account) 44 ++ (selectedSlotPaths (originRegistry account) 45 ++ (selectedSlotPaths (originRegistry account) 46 ++ (selectedSlotPaths (originRegistry account) 47 ++ (selectedSlotPaths (originRegistry account) 48)))))) := rfl

theorem origin_actual_store_decode : finiteWriteback (originRegistry account) originSnapshot originInitialStore =
    some (originFrame6.1.2.2.ex.world.accounts account).storage := by
  have step0 := packedPersistent_writeback_exact originInitialCore originPlan0 rfl
  have req0 : originPlan0.request = ⟨false,account,42,originRaw0⟩ := preparePackedSlot_request _ _ (Option.get_mem origin_ready0)
  simp only [req0] at step0
  change finiteWriteback (selectedSlotPaths (originRegistry account) 42) (fun _ => originRaw0) originInitialStore =
    some (originFrame0.1.2.2.ex.world.accounts account).storage at step0
  have step1 := packedPersistent_writeback_exact (⟨originFrame0.1.2.2.ex,originFrame0.2⟩ : ResidualCompanion originEnv.layout originEnv.lay originEnv.lay complementCarrierOwnership) originPlan1 rfl
  have req1 : originPlan1.request = ⟨false,account,43,originRaw1⟩ := preparePackedSlot_request _ _ (Option.get_mem origin_ready1)
  simp only [req1] at step1
  change finiteWriteback (selectedSlotPaths (originRegistry account) 43) (fun _ => originRaw1) (originFrame0.1.2.2.ex.world.accounts account).storage =
    some (originFrame1.1.2.2.ex.world.accounts account).storage at step1
  have step2 := packedPersistent_writeback_exact (⟨originFrame1.1.2.2.ex,originFrame1.2⟩ : ResidualCompanion originEnv.layout originEnv.lay originEnv.lay complementCarrierOwnership) originPlan2 rfl
  have req2 : originPlan2.request = ⟨false,account,44,originRaw2⟩ := preparePackedSlot_request _ _ (Option.get_mem origin_ready2)
  simp only [req2] at step2
  change finiteWriteback (selectedSlotPaths (originRegistry account) 44) (fun _ => originRaw2) (originFrame1.1.2.2.ex.world.accounts account).storage =
    some (originFrame2.1.2.2.ex.world.accounts account).storage at step2
  have step3 := packedPersistent_writeback_exact (⟨originFrame2.1.2.2.ex,originFrame2.2⟩ : ResidualCompanion originEnv.layout originEnv.lay originEnv.lay complementCarrierOwnership) originPlan3 rfl
  have req3 : originPlan3.request = ⟨false,account,45,originRaw3⟩ := preparePackedSlot_request _ _ (Option.get_mem origin_ready3)
  simp only [req3] at step3
  change finiteWriteback (selectedSlotPaths (originRegistry account) 45) (fun _ => originRaw3) (originFrame2.1.2.2.ex.world.accounts account).storage =
    some (originFrame3.1.2.2.ex.world.accounts account).storage at step3
  have step4 := packedPersistent_writeback_exact (⟨originFrame3.1.2.2.ex,originFrame3.2⟩ : ResidualCompanion originEnv.layout originEnv.lay originEnv.lay complementCarrierOwnership) originPlan4 rfl
  have req4 : originPlan4.request = ⟨false,account,46,originRaw4⟩ := preparePackedSlot_request _ _ (Option.get_mem origin_ready4)
  simp only [req4] at step4
  change finiteWriteback (selectedSlotPaths (originRegistry account) 46) (fun _ => originRaw4) (originFrame3.1.2.2.ex.world.accounts account).storage =
    some (originFrame4.1.2.2.ex.world.accounts account).storage at step4
  have step5 := packedPersistent_writeback_exact (⟨originFrame4.1.2.2.ex,originFrame4.2⟩ : ResidualCompanion originEnv.layout originEnv.lay originEnv.lay complementCarrierOwnership) originPlan5 rfl
  have req5 : originPlan5.request = ⟨false,account,47,originRaw5⟩ := preparePackedSlot_request _ _ (Option.get_mem origin_ready5)
  simp only [req5] at step5
  change finiteWriteback (selectedSlotPaths (originRegistry account) 47) (fun _ => originRaw5) (originFrame4.1.2.2.ex.world.accounts account).storage =
    some (originFrame5.1.2.2.ex.world.accounts account).storage at step5
  have step6 := packedPersistent_writeback_exact (⟨originFrame5.1.2.2.ex,originFrame5.2⟩ : ResidualCompanion originEnv.layout originEnv.lay originEnv.lay complementCarrierOwnership) originPlan6 rfl
  have req6 : originPlan6.request = ⟨false,account,48,originRaw6⟩ := preparePackedSlot_request _ _ (Option.get_mem origin_ready6)
  simp only [req6] at step6
  change finiteWriteback (selectedSlotPaths (originRegistry account) 48) (fun _ => originRaw6) (originFrame5.1.2.2.ex.world.accounts account).storage =
    some (originFrame6.1.2.2.ex.world.accounts account).storage at step6
  have input (q : Roadmap.Word) : ∀ c ∈ selectedSlotPaths (originRegistry account) q, originSnapshot c.slot = originSnapshot q := by
    intro c member
    rw [((selectedSlotPaths_mem _ _ c).mp member).2]
  rw [origin_slot_partition,
    finiteWriteback_append,
    finiteWriteback_inputs (selectedSlotPaths (originRegistry account) 42) originSnapshot (fun _ => originRaw0) (by intro c member; rw [input 42 c member]; rfl),step0,Option.bind_some,
    finiteWriteback_append,
    finiteWriteback_inputs (selectedSlotPaths (originRegistry account) 43) originSnapshot (fun _ => originRaw1) (by intro c member; rw [input 43 c member]; rfl),step1,Option.bind_some,
    finiteWriteback_append,
    finiteWriteback_inputs (selectedSlotPaths (originRegistry account) 44) originSnapshot (fun _ => originRaw2) (by intro c member; rw [input 44 c member]; rfl),step2,Option.bind_some,
    finiteWriteback_append,
    finiteWriteback_inputs (selectedSlotPaths (originRegistry account) 45) originSnapshot (fun _ => originRaw3) (by intro c member; rw [input 45 c member]; rfl),step3,Option.bind_some,
    finiteWriteback_append,
    finiteWriteback_inputs (selectedSlotPaths (originRegistry account) 46) originSnapshot (fun _ => originRaw4) (by intro c member; rw [input 46 c member]; rfl),step4,Option.bind_some,
    finiteWriteback_append,
    finiteWriteback_inputs (selectedSlotPaths (originRegistry account) 47) originSnapshot (fun _ => originRaw5) (by intro c member; rw [input 47 c member]; rfl),step5,Option.bind_some,
    finiteWriteback_inputs (selectedSlotPaths (originRegistry account) 48) originSnapshot (fun _ => originRaw6) (by intro c member; rw [input 48 c member]; rfl),step6]

theorem origin_pure_equals_actual_store : originStore.1 = (originFrame6.1.2.2.ex.world.accounts account).storage := by
  have step : originChecked.storeWriteback originSnapshot originInitialStore = some originStore := Option.get_mem origin_store_ready
  unfold CheckedInheritedDeclarations.storeWriteback packedStoreWriteback at step
  obtain ⟨out,decoded,same⟩ := Option.map_eq_some_iff.mp step
  have cells := congrArg Prod.fst same
  change out = originStore.1 at cells
  rw [cells] at decoded
  change finiteWriteback (originRegistry account) originSnapshot originInitialStore = some originStore.1 at decoded
  rw [origin_actual_store_decode] at decoded
  exact (Option.some.inj decoded).symm

theorem origin_actual_full_reencode : finiteEncode originChecked.registrations
    (originFrame6.1.2.2.ex.world.accounts account).storage originStore.2 = some originSnapshot := by
  rw [← origin_pure_equals_actual_store]
  exact origin_store_full_reencode

end Solidity.Yul.Views.Controls
