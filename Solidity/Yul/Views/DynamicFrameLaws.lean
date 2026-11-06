import Solidity.Yul.Views.DynamicSourceSequence
import Solidity.Yul.Views.NestedDeclarationFinal

namespace Solidity.Yul.Views

theorem packedSlot_other_account {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (p : @PackedSlotPlan D L T ps ts) (b : Roadmap.Address) (different : b ≠ p.request.address) :
    (applyPackedSlot s p).source.world.accounts b = s.source.world.accounts b := by
  cases bank : p.request.transient
  · have ready := p.prepared
    unfold packedRequestOp? finiteAccountWrite? at ready
    rw [bank] at ready
    obtain ⟨update,_,same⟩ := Option.map_eq_some_iff.mp ready
    change (s.source.apply p.sourceOp).world.accounts b = _
    rw [← same]
    exact Source.World.set_other _ different _
  · rw [packedTransient_world s p bank]

theorem runPackedSlots_other_account {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (plans : List (@PackedSlotPlan D L T ps ts)) (b : Roadmap.Address)
    (different : ∀ p ∈ plans, b ≠ p.request.address) :
    (runPackedSlots s plans).source.world.accounts b = s.source.world.accounts b := by
  induction plans generalizing s with
  | nil => rfl
  | cons p plans ih =>
    rw [runPackedSlots,ih (applyPackedSlot s p) (fun x hx => different x (List.mem_cons_of_mem _ hx))]
    exact packedSlot_other_account s p b (different p List.mem_cons_self)

theorem runPackedSlots_other_complement {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (plans : List (@PackedSlotPlan D L T ps ts)) (t : Bool) (a : Roadmap.Address) (q : Roadmap.Word)
    (different : ∀ p ∈ plans, q ≠ p.request.slot) :
    (runPackedSlots s plans).residual.cells (complementKey t a q) = s.residual.cells (complementKey t a q) := by
  induction plans generalizing s with
  | nil => rfl
  | cons p plans ih =>
    rw [runPackedSlots,ih (applyPackedSlot s p) (fun x hx => different x (List.mem_cons_of_mem _ hx))]
    exact packed_other_slot_complement s p t a q (different p List.mem_cons_self)

end Solidity.Yul.Views

namespace Solidity.Yul.Views

theorem packedSlot_persistent_unselected {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (p : @PackedSlotPlan D L T ps ts) (b : Roadmap.Address) (q : Source.SPath)
    (unselected : ∀ c ∈ ps b, q ≠ c.path) :
    ((applyPackedSlot s p).source.world.accounts b).storage.cell q = (s.source.world.accounts b).storage.cell q := by
  by_cases same : b = p.request.address
  · subst b
    cases bank : p.request.transient
    · exact packedPersistent_other_path s p bank q (fun c hc => unselected c ((selectedSlotPaths_mem _ _ c).mp hc).1)
    · rw [packedTransient_world s p bank]
  · rw [packedSlot_other_account s p b same]

theorem packedSlot_transient_unselected {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (p : @PackedSlotPlan D L T ps ts) (b : Roadmap.Address) (q : Source.SPath)
    (unselected : ∀ c ∈ ts b, q ≠ c.path) :
    ((applyPackedSlot s p).source.transient.cells b).cell q = (s.source.transient.cells b).cell q := by
  have ready := p.prepared
  cases bank : p.request.transient
  · unfold packedRequestOp? finiteAccountWrite? at ready
    rw [bank] at ready
    obtain ⟨update,_,same⟩ := Option.map_eq_some_iff.mp ready
    change ((s.source.apply p.sourceOp).transient.cells b).cell q = _
    rw [← same]
    rfl
  · by_cases same : b = p.request.address
    · subst b
      exact packedTransient_other_path s p bank q (fun c hc => unselected c ((selectedSlotPaths_mem _ _ c).mp hc).1)
    · unfold packedRequestOp? finiteTransientWrite? at ready
      rw [bank] at ready
      obtain ⟨update,_,op⟩ := Option.map_eq_some_iff.mp ready
      change ((s.source.apply p.sourceOp).transient.cells b).cell q = _
      rw [← op]
      simp only [Source.ExecState.apply,Source.Transient.set,dif_neg same]

theorem runPackedSlots_persistent_unselected {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (plans : List (@PackedSlotPlan D L T ps ts)) (b : Roadmap.Address) (q : Source.SPath)
    (unselected : ∀ c ∈ ps b, q ≠ c.path) :
    ((runPackedSlots s plans).source.world.accounts b).storage.cell q = (s.source.world.accounts b).storage.cell q := by
  induction plans generalizing s with
  | nil => rfl
  | cons p plans ih =>
    rw [runPackedSlots,ih]
    exact packedSlot_persistent_unselected s p b q unselected

theorem runPackedSlots_transient_unselected {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (plans : List (@PackedSlotPlan D L T ps ts)) (b : Roadmap.Address) (q : Source.SPath)
    (unselected : ∀ c ∈ ts b, q ≠ c.path) :
    ((runPackedSlots s plans).source.transient.cells b).cell q = (s.source.transient.cells b).cell q := by
  induction plans generalizing s with
  | nil => rfl
  | cons p plans ih =>
    rw [runPackedSlots,ih]
    exact packedSlot_transient_unselected s p b q unselected

end Solidity.Yul.Views

namespace Solidity.Yul.Views

theorem packedStoreWriteback_residual {D L} (cs : List (ScalarPath D L)) (m : SlotView)
    (s out : Source.Storage D L) (residual : SlotView)
    (step : packedStoreWriteback cs m s = some (out,residual)) : residual = packedMask cs m := by
  obtain ⟨written,_,same⟩ := Option.map_eq_some_iff.mp step
  exact (congrArg Prod.snd same).symm

end Solidity.Yul.Views

namespace Solidity.Yul.Views

theorem initialPackedComplement_false {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    (ps : (a : Roadmap.Address) → List (ScalarPath D (L a)))
    (ts : (a : Roadmap.Address) → List (ScalarPath D (T a))) (m : SlotView)
    (a : Roadmap.Address) (q : Roadmap.Word) :
    (initialPackedComplement ps ts (fun k => m k.slot)).cells (complementKey false a q) = packedMask (ps a) m q := rfl

end Solidity.Yul.Views
