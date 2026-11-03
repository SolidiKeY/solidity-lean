import Solidity.Yul.Views.FixedDeclarationStore

namespace Solidity.Yul.Views.Controls

def recursiveInitialCore : ResidualCompanion recursiveDeclEnv.layout recursiveDeclEnv.lay recursiveDeclEnv.lay complementCarrierOwnership :=
  ⟨recursiveState.2.ex,recursiveResidual⟩
def recursiveCallerCore : ResidualCompanion recursiveDeclEnv.layout recursiveDeclEnv.lay recursiveDeclEnv.lay complementCarrierOwnership :=
  ⟨recursiveFrame13.1.2.2.ex,recursiveFrame13.2⟩

theorem recursive_actual_sequence : recursiveCallerCore = runPackedSlots recursiveInitialCore
    [recursivePlan8,recursivePlan9,recursivePlan10,recursivePlan11,recursivePlan12,recursivePlan13] := rfl

theorem recursive_slot_partition : recursiveRegistry account =
    selectedSlotPaths (recursiveRegistry account) 8 ++ (selectedSlotPaths (recursiveRegistry account) 9 ++ (selectedSlotPaths (recursiveRegistry account) 10 ++ (selectedSlotPaths (recursiveRegistry account) 11 ++ (selectedSlotPaths (recursiveRegistry account) 12 ++ (selectedSlotPaths (recursiveRegistry account) 13))))) := rfl

theorem recursive_actual_store_decode : finiteWriteback (recursiveRegistry account) recursiveSnapshot recursiveEmptyStore =
    some (recursiveFrame13.1.2.2.ex.world.accounts account).storage := by
  have step8 := packedPersistent_writeback_exact recursiveInitialCore recursivePlan8 rfl
  have req8 : recursivePlan8.request = ⟨false,account,8,recursiveRaw8⟩ := preparePackedSlot_request _ _ (Option.get_mem recursive_ready8)
  simp only [req8] at step8
  change finiteWriteback (selectedSlotPaths (recursiveRegistry account) 8) (fun _ => recursiveRaw8)
    recursiveEmptyStore = some (recursiveFrame8.1.2.2.ex.world.accounts account).storage at step8
  have step9 := packedPersistent_writeback_exact (⟨recursiveFrame8.1.2.2.ex,recursiveFrame8.2⟩ : ResidualCompanion recursiveDeclEnv.layout recursiveDeclEnv.lay recursiveDeclEnv.lay complementCarrierOwnership) recursivePlan9 rfl
  have req9 : recursivePlan9.request = ⟨false,account,9,recursiveRaw9⟩ := preparePackedSlot_request _ _ (Option.get_mem recursive_ready9)
  simp only [req9] at step9
  change finiteWriteback (selectedSlotPaths (recursiveRegistry account) 9) (fun _ => recursiveRaw9)
    (recursiveFrame8.1.2.2.ex.world.accounts account).storage = some (recursiveFrame9.1.2.2.ex.world.accounts account).storage at step9
  have step10 := packedPersistent_writeback_exact (⟨recursiveFrame9.1.2.2.ex,recursiveFrame9.2⟩ : ResidualCompanion recursiveDeclEnv.layout recursiveDeclEnv.lay recursiveDeclEnv.lay complementCarrierOwnership) recursivePlan10 rfl
  have req10 : recursivePlan10.request = ⟨false,account,10,recursiveRaw10⟩ := preparePackedSlot_request _ _ (Option.get_mem recursive_ready10)
  simp only [req10] at step10
  change finiteWriteback (selectedSlotPaths (recursiveRegistry account) 10) (fun _ => recursiveRaw10)
    (recursiveFrame9.1.2.2.ex.world.accounts account).storage = some (recursiveFrame10.1.2.2.ex.world.accounts account).storage at step10
  have step11 := packedPersistent_writeback_exact (⟨recursiveFrame10.1.2.2.ex,recursiveFrame10.2⟩ : ResidualCompanion recursiveDeclEnv.layout recursiveDeclEnv.lay recursiveDeclEnv.lay complementCarrierOwnership) recursivePlan11 rfl
  have req11 : recursivePlan11.request = ⟨false,account,11,recursiveRaw11⟩ := preparePackedSlot_request _ _ (Option.get_mem recursive_ready11)
  simp only [req11] at step11
  change finiteWriteback (selectedSlotPaths (recursiveRegistry account) 11) (fun _ => recursiveRaw11)
    (recursiveFrame10.1.2.2.ex.world.accounts account).storage = some (recursiveFrame11.1.2.2.ex.world.accounts account).storage at step11
  have step12 := packedPersistent_writeback_exact (⟨recursiveFrame11.1.2.2.ex,recursiveFrame11.2⟩ : ResidualCompanion recursiveDeclEnv.layout recursiveDeclEnv.lay recursiveDeclEnv.lay complementCarrierOwnership) recursivePlan12 rfl
  have req12 : recursivePlan12.request = ⟨false,account,12,recursiveRaw12⟩ := preparePackedSlot_request _ _ (Option.get_mem recursive_ready12)
  simp only [req12] at step12
  change finiteWriteback (selectedSlotPaths (recursiveRegistry account) 12) (fun _ => recursiveRaw12)
    (recursiveFrame11.1.2.2.ex.world.accounts account).storage = some (recursiveFrame12.1.2.2.ex.world.accounts account).storage at step12
  have step13 := packedPersistent_writeback_exact (⟨recursiveFrame12.1.2.2.ex,recursiveFrame12.2⟩ : ResidualCompanion recursiveDeclEnv.layout recursiveDeclEnv.lay recursiveDeclEnv.lay complementCarrierOwnership) recursivePlan13 rfl
  have req13 : recursivePlan13.request = ⟨false,account,13,recursiveRaw13⟩ := preparePackedSlot_request _ _ (Option.get_mem recursive_ready13)
  simp only [req13] at step13
  change finiteWriteback (selectedSlotPaths (recursiveRegistry account) 13) (fun _ => recursiveRaw13)
    (recursiveFrame12.1.2.2.ex.world.accounts account).storage = some (recursiveFrame13.1.2.2.ex.world.accounts account).storage at step13
  have input (q : Roadmap.Word) : ∀ c ∈ selectedSlotPaths (recursiveRegistry account) q, recursiveSnapshot c.slot = recursiveSnapshot q := by
    intro c member
    rw [((selectedSlotPaths_mem _ _ c).mp member).2]
  rw [recursive_slot_partition,
    finiteWriteback_append,
    finiteWriteback_inputs (selectedSlotPaths (recursiveRegistry account) 8) recursiveSnapshot (fun _ => recursiveRaw8) (by intro c member; rw [input 8 c member]; rfl),step8,Option.bind_some,
    finiteWriteback_append,
    finiteWriteback_inputs (selectedSlotPaths (recursiveRegistry account) 9) recursiveSnapshot (fun _ => recursiveRaw9) (by intro c member; rw [input 9 c member]; rfl),step9,Option.bind_some,
    finiteWriteback_append,
    finiteWriteback_inputs (selectedSlotPaths (recursiveRegistry account) 10) recursiveSnapshot (fun _ => recursiveRaw10) (by intro c member; rw [input 10 c member]; rfl),step10,Option.bind_some,
    finiteWriteback_append,
    finiteWriteback_inputs (selectedSlotPaths (recursiveRegistry account) 11) recursiveSnapshot (fun _ => recursiveRaw11) (by intro c member; rw [input 11 c member]; rfl),step11,Option.bind_some,
    finiteWriteback_append,
    finiteWriteback_inputs (selectedSlotPaths (recursiveRegistry account) 12) recursiveSnapshot (fun _ => recursiveRaw12) (by intro c member; rw [input 12 c member]; rfl),step12,Option.bind_some,
    finiteWriteback_inputs (selectedSlotPaths (recursiveRegistry account) 13) recursiveSnapshot (fun _ => recursiveRaw13) (by intro c member; rw [input 13 c member]; rfl),step13]

theorem recursive_pure_equals_actual_store : recursiveStore.1 = (recursiveFrame13.1.2.2.ex.world.accounts account).storage := by
  have step : recursiveChecked.storeWriteback recursiveSnapshot recursiveEmptyStore = some recursiveStore := Option.get_mem recursive_store_ready
  unfold CheckedFixedDeclaration.storeWriteback packedStoreWriteback at step
  obtain ⟨out,decoded,same⟩ := Option.map_eq_some_iff.mp step
  have cells := congrArg Prod.fst same
  change out = recursiveStore.1 at cells
  rw [cells] at decoded
  change finiteWriteback (recursiveRegistry account) recursiveSnapshot recursiveEmptyStore = some recursiveStore.1 at decoded
  rw [recursive_actual_store_decode] at decoded
  exact (Option.some.inj decoded).symm

theorem recursive_actual_full_map_reencode :
    finiteEncode recursiveChecked.registrations (recursiveFrame13.1.2.2.ex.world.accounts account).storage recursiveStore.2 = some recursiveSnapshot := by
  rw [← recursive_pure_equals_actual_store]
  exact recursive_store_full_reencode

end Solidity.Yul.Views.Controls
