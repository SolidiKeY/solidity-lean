import Solidity.Yul.Views.NestedDeclarationStore

namespace Solidity.Yul.Views

theorem finiteWriteback_append {D L} (xs ys : List (ScalarPath D L)) (m : SlotView) (s : Source.Storage D L) :
    finiteWriteback (xs++ys) m s = (finiteWriteback xs m s).bind (finiteWriteback ys m) := by
  induction xs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.cons_append,finiteWriteback]
    rw [Option.bind_assoc]
    apply Option.bind_congr
    intro mid _
    exact ih mid

theorem finiteWriteback_inputs {D L} (cs : List (ScalarPath D L)) (m n : SlotView)
    (same : ∀ c ∈ cs, m c.slot = n c.slot) (s : Source.Storage D L) : finiteWriteback cs m s = finiteWriteback cs n s := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    have first : canonicalPathWriteback c.path c.codec c.slot m s = canonicalPathWriteback c.path c.codec c.slot n s := by
      unfold canonicalPathWriteback
      rw [same c List.mem_cons_self]
    simp only [finiteWriteback,first]
    apply Option.bind_congr
    intro mid _
    exact ih (fun d member => same d (List.mem_cons_of_mem c member)) mid

theorem packedPersistent_writeback_exact {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (p : @PackedSlotPlan D L T ps ts) (tr : p.request.transient = false) :
    finiteWriteback (selectedSlotPaths (ps p.request.address) p.request.slot) (fun _ => p.request.raw)
      (s.source.world.accounts p.request.address).storage =
      some ((applyPackedSlot s p).source.world.accounts p.request.address).storage := by
  have prepared := p.prepared
  unfold packedRequestOp? at prepared
  rw [tr] at prepared
  obtain ⟨out,decoded,same,_,_⟩ := finiteAccountWrite_actual _ _ _ s.source p.sourceOp prepared
  exact decoded.trans (congrArg some same.symm)

end Solidity.Yul.Views

namespace Solidity.Yul.Views.Controls

theorem nested_registry_slot_partition : nestedDeclRegistry account =
    selectedSlotPaths (nestedDeclRegistry account) 4 ++ selectedSlotPaths (nestedDeclRegistry account) 5 ++
      selectedSlotPaths (nestedDeclRegistry account) 6 := rfl

theorem nested_actual_whole_store_decode :
    finiteWriteback (nestedDeclRegistry account) nestedSnapshot nestedEmptyStore =
      some (nestedFrame6.1.2.2.ex.world.accounts account).storage := by
  have step4 := packedPersistent_writeback_exact nestedInitialCore nestedPlan4 rfl
  have step5 := packedPersistent_writeback_exact
    (⟨nestedFrame4.1.2.2.ex,nestedFrame4.2⟩ : ResidualCompanion declBoundaryEnv.layout declBoundaryEnv.lay declBoundaryEnv.lay complementCarrierOwnership) nestedPlan5 rfl
  have step6 := packedPersistent_writeback_exact
    (⟨nestedFrame5.1.2.2.ex,nestedFrame5.2⟩ : ResidualCompanion declBoundaryEnv.layout declBoundaryEnv.lay declBoundaryEnv.lay complementCarrierOwnership) nestedPlan6 rfl
  have request4 : nestedPlan4.request = ⟨false,account,4,nestedRaw4⟩ :=
    preparePackedSlot_request _ _ (Option.get_mem nested_slot4_ready)
  have request5 : nestedPlan5.request = ⟨false,account,5,nestedRaw5⟩ :=
    preparePackedSlot_request _ _ (Option.get_mem nested_slot5_ready)
  have request6 : nestedPlan6.request = ⟨false,account,6,nestedRaw6⟩ :=
    preparePackedSlot_request _ _ (Option.get_mem nested_slot6_ready)
  simp only [request4] at step4
  simp only [request5] at step5
  simp only [request6] at step6
  change finiteWriteback (selectedSlotPaths (nestedDeclRegistry account) 4) (fun _ => nestedRaw4) nestedEmptyStore =
    some (nestedFrame4.1.2.2.ex.world.accounts account).storage at step4
  change finiteWriteback (selectedSlotPaths (nestedDeclRegistry account) 5) (fun _ => nestedRaw5)
    (nestedFrame4.1.2.2.ex.world.accounts account).storage = some (nestedFrame5.1.2.2.ex.world.accounts account).storage at step5
  change finiteWriteback (selectedSlotPaths (nestedDeclRegistry account) 6) (fun _ => nestedRaw6)
    (nestedFrame5.1.2.2.ex.world.accounts account).storage = some (nestedFrame6.1.2.2.ex.world.accounts account).storage at step6
  have input (q : Roadmap.Word) : ∀ c ∈ selectedSlotPaths (nestedDeclRegistry account) q, nestedSnapshot c.slot = nestedSnapshot q := by
    intro c member
    rw [((selectedSlotPaths_mem _ _ c).mp member).2]
  have partition : nestedDeclRegistry account = selectedSlotPaths (nestedDeclRegistry account) 4 ++
      (selectedSlotPaths (nestedDeclRegistry account) 5 ++ selectedSlotPaths (nestedDeclRegistry account) 6) :=
    nested_registry_slot_partition.trans (List.append_assoc _ _ _)
  rw [partition,finiteWriteback_append,
    finiteWriteback_inputs (selectedSlotPaths (nestedDeclRegistry account) 4) nestedSnapshot (fun _ => nestedRaw4) (by intro c member; rw [input 4 c member]; rfl),step4,Option.bind_some,
    finiteWriteback_append,
    finiteWriteback_inputs (selectedSlotPaths (nestedDeclRegistry account) 5) nestedSnapshot (fun _ => nestedRaw5) (by intro c member; rw [input 5 c member]; rfl),step5,Option.bind_some,
    finiteWriteback_inputs (selectedSlotPaths (nestedDeclRegistry account) 6) nestedSnapshot (fun _ => nestedRaw6) (by intro c member; rw [input 6 c member]; rfl),step6]

theorem nested_pure_equals_actual_source_store : nestedStore.1 = (nestedFrame6.1.2.2.ex.world.accounts account).storage := by
  have step : nestedDeclCert.storeWriteback nestedSnapshot nestedEmptyStore = some nestedStore := Option.get_mem nested_store_ready
  unfold NestedDeclaration.storeWriteback packedStoreWriteback at step
  obtain ⟨out,decoded,same⟩ := Option.map_eq_some_iff.mp step
  have cells := congrArg Prod.fst same
  change out = nestedStore.1 at cells
  rw [cells] at decoded
  change finiteWriteback (nestedDeclRegistry account) nestedSnapshot nestedEmptyStore = some nestedStore.1 at decoded
  rw [nested_actual_whole_store_decode] at decoded
  exact (Option.some.inj decoded).symm

theorem nested_actual_source_full_reencoding :
    finiteEncode nestedDeclCert.registrations (nestedFrame6.1.2.2.ex.world.accounts account).storage nestedStore.2 = some nestedSnapshot := by
  rw [← nested_pure_equals_actual_source_store]
  exact nested_store_full_map_reencoding

end Solidity.Yul.Views.Controls
