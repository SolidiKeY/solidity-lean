import Solidity.Yul.Views.InheritedDeclarationStore

namespace Solidity.Yul.Views.Controls

def diamondInitialCore : ResidualCompanion diamondEnv.layout diamondEnv.lay diamondEnv.lay complementCarrierOwnership := ⟨diamondState.2.ex,diamondResidual⟩
def diamondCallerCore : ResidualCompanion diamondEnv.layout diamondEnv.lay diamondEnv.lay complementCarrierOwnership := ⟨diamondFrame6.1.2.2.ex,diamondFrame6.2⟩
def diamondCore0 : ResidualCompanion diamondEnv.layout diamondEnv.lay diamondEnv.lay complementCarrierOwnership := ⟨diamondFrame0.1.2.2.ex,diamondFrame0.2⟩
theorem diamondCore0_step : diamondCore0 = applyPackedSlot diamondInitialCore diamondPlan0 :=
  (packedSourceStep_companion packedStepFrame diamondPlan0 diamondState diamondResidual rfl).2.2.2.2.2
def diamondCore1 : ResidualCompanion diamondEnv.layout diamondEnv.lay diamondEnv.lay complementCarrierOwnership := ⟨diamondFrame1.1.2.2.ex,diamondFrame1.2⟩
theorem diamondCore1_step : diamondCore1 = applyPackedSlot diamondCore0 diamondPlan1 :=
  (packedSourceStep_companion packedStepFrame diamondPlan1 diamondFrame0.1.2 diamondFrame0.2 rfl).2.2.2.2.2
def diamondCore2 : ResidualCompanion diamondEnv.layout diamondEnv.lay diamondEnv.lay complementCarrierOwnership := ⟨diamondFrame2.1.2.2.ex,diamondFrame2.2⟩
theorem diamondCore2_step : diamondCore2 = applyPackedSlot diamondCore1 diamondPlan2 :=
  (packedSourceStep_companion packedStepFrame diamondPlan2 diamondFrame1.1.2 diamondFrame1.2 rfl).2.2.2.2.2
def diamondCore3 : ResidualCompanion diamondEnv.layout diamondEnv.lay diamondEnv.lay complementCarrierOwnership := ⟨diamondFrame3.1.2.2.ex,diamondFrame3.2⟩
theorem diamondCore3_step : diamondCore3 = applyPackedSlot diamondCore2 diamondPlan3 :=
  (packedSourceStep_companion packedStepFrame diamondPlan3 diamondFrame2.1.2 diamondFrame2.2 rfl).2.2.2.2.2
def diamondCore4 : ResidualCompanion diamondEnv.layout diamondEnv.lay diamondEnv.lay complementCarrierOwnership := ⟨diamondFrame4.1.2.2.ex,diamondFrame4.2⟩
theorem diamondCore4_step : diamondCore4 = applyPackedSlot diamondCore3 diamondPlan4 :=
  (packedSourceStep_companion packedStepFrame diamondPlan4 diamondFrame3.1.2 diamondFrame3.2 rfl).2.2.2.2.2
def diamondCore5 : ResidualCompanion diamondEnv.layout diamondEnv.lay diamondEnv.lay complementCarrierOwnership := ⟨diamondFrame5.1.2.2.ex,diamondFrame5.2⟩
theorem diamondCore5_step : diamondCore5 = applyPackedSlot diamondCore4 diamondPlan5 :=
  (packedSourceStep_companion packedStepFrame diamondPlan5 diamondFrame4.1.2 diamondFrame4.2 rfl).2.2.2.2.2
def diamondCore6 : ResidualCompanion diamondEnv.layout diamondEnv.lay diamondEnv.lay complementCarrierOwnership := ⟨diamondFrame6.1.2.2.ex,diamondFrame6.2⟩
theorem diamondCore6_step : diamondCore6 = applyPackedSlot diamondCore5 diamondPlan6 :=
  (packedSourceStep_companion packedStepFrame diamondPlan6 diamondFrame5.1.2 diamondFrame5.2 rfl).2.2.2.2.2
theorem diamond_actual_sequence : diamondCallerCore = runPackedSlots diamondInitialCore [diamondPlan0,diamondPlan1,diamondPlan2,diamondPlan3,diamondPlan4,diamondPlan5,diamondPlan6] := by
  change diamondCore6 = _
  simp only [runPackedSlots]
  rw [diamondCore6_step,diamondCore5_step,diamondCore4_step,diamondCore3_step,diamondCore2_step,diamondCore1_step,diamondCore0_step]

theorem diamond_slot_partition : diamondRegistry account =
    selectedSlotPaths (diamondRegistry account) 0 ++ (selectedSlotPaths (diamondRegistry account) 1 ++ (selectedSlotPaths (diamondRegistry account) 2 ++ (selectedSlotPaths (diamondRegistry account) 3 ++ (selectedSlotPaths (diamondRegistry account) 4 ++ (selectedSlotPaths (diamondRegistry account) 5 ++ (selectedSlotPaths (diamondRegistry account) 6)))))) := rfl

theorem diamond_actual_store_decode : finiteWriteback (diamondRegistry account) diamondSnapshot diamondInitialStore =
    some (diamondFrame6.1.2.2.ex.world.accounts account).storage := by
  have step0 := packedPersistent_writeback_exact diamondInitialCore diamondPlan0 rfl
  have req0 : diamondPlan0.request = ⟨false,account,0,diamondRaw0⟩ := preparePackedSlot_request _ _ (Option.get_mem diamond_ready0)
  simp only [req0] at step0
  change finiteWriteback (selectedSlotPaths (diamondRegistry account) 0) (fun _ => diamondRaw0) diamondInitialStore =
    some (diamondFrame0.1.2.2.ex.world.accounts account).storage at step0
  have step1 := packedPersistent_writeback_exact (⟨diamondFrame0.1.2.2.ex,diamondFrame0.2⟩ : ResidualCompanion diamondEnv.layout diamondEnv.lay diamondEnv.lay complementCarrierOwnership) diamondPlan1 rfl
  have req1 : diamondPlan1.request = ⟨false,account,1,diamondRaw1⟩ := preparePackedSlot_request _ _ (Option.get_mem diamond_ready1)
  simp only [req1] at step1
  change finiteWriteback (selectedSlotPaths (diamondRegistry account) 1) (fun _ => diamondRaw1) (diamondFrame0.1.2.2.ex.world.accounts account).storage =
    some (diamondFrame1.1.2.2.ex.world.accounts account).storage at step1
  have step2 := packedPersistent_writeback_exact (⟨diamondFrame1.1.2.2.ex,diamondFrame1.2⟩ : ResidualCompanion diamondEnv.layout diamondEnv.lay diamondEnv.lay complementCarrierOwnership) diamondPlan2 rfl
  have req2 : diamondPlan2.request = ⟨false,account,2,diamondRaw2⟩ := preparePackedSlot_request _ _ (Option.get_mem diamond_ready2)
  simp only [req2] at step2
  change finiteWriteback (selectedSlotPaths (diamondRegistry account) 2) (fun _ => diamondRaw2) (diamondFrame1.1.2.2.ex.world.accounts account).storage =
    some (diamondFrame2.1.2.2.ex.world.accounts account).storage at step2
  have step3 := packedPersistent_writeback_exact (⟨diamondFrame2.1.2.2.ex,diamondFrame2.2⟩ : ResidualCompanion diamondEnv.layout diamondEnv.lay diamondEnv.lay complementCarrierOwnership) diamondPlan3 rfl
  have req3 : diamondPlan3.request = ⟨false,account,3,diamondRaw3⟩ := preparePackedSlot_request _ _ (Option.get_mem diamond_ready3)
  simp only [req3] at step3
  change finiteWriteback (selectedSlotPaths (diamondRegistry account) 3) (fun _ => diamondRaw3) (diamondFrame2.1.2.2.ex.world.accounts account).storage =
    some (diamondFrame3.1.2.2.ex.world.accounts account).storage at step3
  have step4 := packedPersistent_writeback_exact (⟨diamondFrame3.1.2.2.ex,diamondFrame3.2⟩ : ResidualCompanion diamondEnv.layout diamondEnv.lay diamondEnv.lay complementCarrierOwnership) diamondPlan4 rfl
  have req4 : diamondPlan4.request = ⟨false,account,4,diamondRaw4⟩ := preparePackedSlot_request _ _ (Option.get_mem diamond_ready4)
  simp only [req4] at step4
  change finiteWriteback (selectedSlotPaths (diamondRegistry account) 4) (fun _ => diamondRaw4) (diamondFrame3.1.2.2.ex.world.accounts account).storage =
    some (diamondFrame4.1.2.2.ex.world.accounts account).storage at step4
  have step5 := packedPersistent_writeback_exact (⟨diamondFrame4.1.2.2.ex,diamondFrame4.2⟩ : ResidualCompanion diamondEnv.layout diamondEnv.lay diamondEnv.lay complementCarrierOwnership) diamondPlan5 rfl
  have req5 : diamondPlan5.request = ⟨false,account,5,diamondRaw5⟩ := preparePackedSlot_request _ _ (Option.get_mem diamond_ready5)
  simp only [req5] at step5
  change finiteWriteback (selectedSlotPaths (diamondRegistry account) 5) (fun _ => diamondRaw5) (diamondFrame4.1.2.2.ex.world.accounts account).storage =
    some (diamondFrame5.1.2.2.ex.world.accounts account).storage at step5
  have step6 := packedPersistent_writeback_exact (⟨diamondFrame5.1.2.2.ex,diamondFrame5.2⟩ : ResidualCompanion diamondEnv.layout diamondEnv.lay diamondEnv.lay complementCarrierOwnership) diamondPlan6 rfl
  have req6 : diamondPlan6.request = ⟨false,account,6,diamondRaw6⟩ := preparePackedSlot_request _ _ (Option.get_mem diamond_ready6)
  simp only [req6] at step6
  change finiteWriteback (selectedSlotPaths (diamondRegistry account) 6) (fun _ => diamondRaw6) (diamondFrame5.1.2.2.ex.world.accounts account).storage =
    some (diamondFrame6.1.2.2.ex.world.accounts account).storage at step6
  have input (q : Roadmap.Word) : ∀ c ∈ selectedSlotPaths (diamondRegistry account) q, diamondSnapshot c.slot = diamondSnapshot q := by
    intro c member
    rw [((selectedSlotPaths_mem _ _ c).mp member).2]
  rw [diamond_slot_partition,
    finiteWriteback_append,
    finiteWriteback_inputs (selectedSlotPaths (diamondRegistry account) 0) diamondSnapshot (fun _ => diamondRaw0) (by intro c member; rw [input 0 c member]; rfl),step0,Option.bind_some,
    finiteWriteback_append,
    finiteWriteback_inputs (selectedSlotPaths (diamondRegistry account) 1) diamondSnapshot (fun _ => diamondRaw1) (by intro c member; rw [input 1 c member]; rfl),step1,Option.bind_some,
    finiteWriteback_append,
    finiteWriteback_inputs (selectedSlotPaths (diamondRegistry account) 2) diamondSnapshot (fun _ => diamondRaw2) (by intro c member; rw [input 2 c member]; rfl),step2,Option.bind_some,
    finiteWriteback_append,
    finiteWriteback_inputs (selectedSlotPaths (diamondRegistry account) 3) diamondSnapshot (fun _ => diamondRaw3) (by intro c member; rw [input 3 c member]; rfl),step3,Option.bind_some,
    finiteWriteback_append,
    finiteWriteback_inputs (selectedSlotPaths (diamondRegistry account) 4) diamondSnapshot (fun _ => diamondRaw4) (by intro c member; rw [input 4 c member]; rfl),step4,Option.bind_some,
    finiteWriteback_append,
    finiteWriteback_inputs (selectedSlotPaths (diamondRegistry account) 5) diamondSnapshot (fun _ => diamondRaw5) (by intro c member; rw [input 5 c member]; rfl),step5,Option.bind_some,
    finiteWriteback_inputs (selectedSlotPaths (diamondRegistry account) 6) diamondSnapshot (fun _ => diamondRaw6) (by intro c member; rw [input 6 c member]; rfl),step6]

theorem diamond_pure_equals_actual_store : diamondStore.1 = (diamondFrame6.1.2.2.ex.world.accounts account).storage := by
  have step : diamondChecked.storeWriteback diamondSnapshot diamondInitialStore = some diamondStore := Option.get_mem diamond_store_ready
  unfold CheckedInheritedDeclarations.storeWriteback packedStoreWriteback at step
  obtain ⟨out,decoded,same⟩ := Option.map_eq_some_iff.mp step
  have cells := congrArg Prod.fst same
  change out = diamondStore.1 at cells
  rw [cells] at decoded
  change finiteWriteback (diamondRegistry account) diamondSnapshot diamondInitialStore = some diamondStore.1 at decoded
  rw [diamond_actual_store_decode] at decoded
  exact (Option.some.inj decoded).symm

theorem diamond_actual_full_reencode : finiteEncode diamondChecked.registrations
    (diamondFrame6.1.2.2.ex.world.accounts account).storage diamondStore.2 = some diamondSnapshot := by
  rw [← diamond_pure_equals_actual_store]
  exact diamond_store_full_reencode

end Solidity.Yul.Views.Controls
