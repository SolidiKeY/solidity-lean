import Solidity.Yul.Views.PackedResidualCodec

/-! Raw requests produce ONE validated plan: source operation and complementary
residual word derive from the SAME bank/account/slot/raw word. The existing
journal carries complement words, not a second untyped source state. -/
namespace Solidity.Yul.Views

def complementCarrierOwnership : ResidualOwnership := fun _ _ _ => False

def complementKey (transient : Bool) (address : Roadmap.Address) (slot : Roadmap.Word) :
    ResidualKey complementCarrierOwnership := ⟨transient,address,slot,fun no => no⟩

structure PackedSlotRequest where
  transient : Bool
  address : Roadmap.Address
  slot : Roadmap.Word
  raw : Roadmap.Word

def selectedSlotPaths {D L} (cs : List (ScalarPath D L)) (slot : Roadmap.Word) : List (ScalarPath D L) :=
  cs.filter (fun c => c.slot == slot)

theorem selectedSlotPaths_mem {D L} (cs : List (ScalarPath D L)) (slot : Roadmap.Word) (c : ScalarPath D L) :
    c ∈ selectedSlotPaths cs slot ↔ c ∈ cs ∧ c.slot = slot := by
  simp only [selectedSlotPaths,List.mem_filter,beq_iff_eq]

theorem selectedSlotPaths_separated {D L} (cs : List (ScalarPath D L)) (slot : Roadmap.Word)
    (sep : finiteSeparated cs) : finiteSeparated (selectedSlotPaths cs slot) := List.Pairwise.filter _ sep

theorem selectedSlotPaths_owns {D L} (cs : List (ScalarPath D L)) (slot : Roadmap.Word) (i : Fin 32) :
    packedOwnsByte (selectedSlotPaths cs slot) slot i = packedOwnsByte cs slot i := by
  apply Bool.eq_iff_iff.mpr
  rw [packedOwnsByte_iff,packedOwnsByte_iff]
  constructor
  · rintro ⟨c,member,eq,inside⟩
    exact ⟨c,((selectedSlotPaths_mem cs slot c).mp member).1,eq,inside⟩
  · rintro ⟨c,member,eq,inside⟩
    exact ⟨c,(selectedSlotPaths_mem cs slot c).mpr ⟨member,eq⟩,eq,inside⟩

def packedCarrierOwns {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    (ps : (a : Roadmap.Address) → List (ScalarPath D (L a)))
    (ts : (a : Roadmap.Address) → List (ScalarPath D (T a)))
    (k : ResidualKey complementCarrierOwnership) (i : Fin 32) : Bool :=
  if k.transient then packedOwnsByte (ts k.address) k.slot i else packedOwnsByte (ps k.address) k.slot i

def packedRequestOp? {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    (ps : (a : Roadmap.Address) → List (ScalarPath D (L a)))
    (ts : (a : Roadmap.Address) → List (ScalarPath D (T a))) (q : PackedSlotRequest) : Option (Source.Op D L T) :=
  if q.transient then finiteTransientWrite? q.address (selectedSlotPaths (ts q.address) q.slot) (fun _ => q.raw)
  else finiteAccountWrite? q.address (selectedSlotPaths (ps q.address) q.slot) (fun _ => q.raw)

/-- Only the concrete validator equation is retained, no inverse/view/safety
law fields. The public preparation function computes this proof intrinsically. -/
structure PackedSlotPlan {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    (ps : (a : Roadmap.Address) → List (ScalarPath D (L a)))
    (ts : (a : Roadmap.Address) → List (ScalarPath D (T a))) where
  request : PackedSlotRequest
  sourceOp : Source.Op D L T
  prepared : packedRequestOp? ps ts request = some sourceOp

def preparePackedSlot {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    (ps : (a : Roadmap.Address) → List (ScalarPath D (L a)))
    (ts : (a : Roadmap.Address) → List (ScalarPath D (T a))) (q : PackedSlotRequest) : Option (PackedSlotPlan ps ts) :=
  (packedRequestOp? ps ts q).pmap (fun op prepared => ⟨q,op,prepared⟩) (fun _ eq => eq)

theorem preparePackedSlot_request {D L T ps ts} (q : PackedSlotRequest) (p : @PackedSlotPlan D L T ps ts)
    (prepared : preparePackedSlot ps ts q = some p) : p.request = q := by
  unfold preparePackedSlot at prepared
  obtain ⟨op,present,ready,same⟩ := Option.pmap_eq_some_iff.mp prepared
  rw [same]


def PackedSlotPlan.residualUpdate {D L T ps ts} (p : @PackedSlotPlan D L T ps ts) :
    ResidualKey complementCarrierOwnership × Roadmap.Word :=
  let k := complementKey p.request.transient p.request.address p.request.slot
  (k,complementWord (packedCarrierOwns ps ts k) p.request.raw)

def applyPackedSlot {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (p : @PackedSlotPlan D L T ps ts) : ResidualCompanion D L T complementCarrierOwnership :=
  ⟨s.source.apply p.sourceOp,residualWrite s.residual p.residualUpdate⟩

def runPackedSlots {D L T ps ts} : ResidualCompanion D L T complementCarrierOwnership →
    List (@PackedSlotPlan D L T ps ts) → ResidualCompanion D L T complementCarrierOwnership
  | s, [] => s
  | s, p::ps => runPackedSlots (applyPackedSlot s p) ps

/-- Lists of source/residual operations are DERIVED from the same raw plans;
the caller cannot independently supply mismatching logical/residual updates. -/
theorem runPackedSlots_split {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (plans : List (@PackedSlotPlan D L T ps ts)) : runPackedSlots s plans =
    companionRunResidual (companionRunSource s (plans.map PackedSlotPlan.sourceOp)) (plans.map PackedSlotPlan.residualUpdate) := by
  induction plans generalizing s with
  | nil => rfl
  | cons p plans ih => rw [runPackedSlots,ih]; rfl

theorem packed_frame_rollback {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (plans : List (@PackedSlotPlan D L T ps ts)) (a c : Roadmap.Address) (v : Roadmap.Word) (i : Roadmap.Bytes) (st : Bool) :
    companionRollback (companionEnter s a c v i st) (runPackedSlots s plans) = s := by
  rw [runPackedSlots_split]
  exact companionRollback_run s _ _ a c v i st

theorem packed_frame_child_rollback {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (caller child : List (@PackedSlotPlan D L T ps ts)) (a c : Roadmap.Address) (v : Roadmap.Word) (i : Roadmap.Bytes) (st : Bool) :
    companionRollback (companionEnter (runPackedSlots s caller) a c v i st)
      (runPackedSlots (runPackedSlots s caller) child) = runPackedSlots s caller := packed_frame_rollback _ _ _ _ _ _ _

theorem packed_frame_outer_commit {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (caller child : List (@PackedSlotPlan D L T ps ts)) (a c : Roadmap.Address) (v : Roadmap.Word) (i : Roadmap.Bytes) (st : Bool) :
    companionRollback (companionEnter s a c v i st)
      (companionCommit (companionEnter (runPackedSlots s caller) a c v i st)
        (runPackedSlots (runPackedSlots s caller) child)) = s := by
  rw [runPackedSlots_split,runPackedSlots_split]
  exact companionRollback_outer_commit s _ _ _ _ a c v i st

end Solidity.Yul.Views
