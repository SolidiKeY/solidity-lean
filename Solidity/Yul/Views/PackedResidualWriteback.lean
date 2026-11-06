import Solidity.Yul.Views.PackedResidualSource

namespace Solidity.Yul.Views

def finiteViewBool {D L} (cs : List (ScalarPath D L)) (s : Source.Storage D L) (m : SlotView) : Bool :=
  cs.all (fun c => decide ((s.read c.path).map c.codec.encode = some (c.field.findWord (m c.slot))))

theorem finiteViewBool_iff {D L} (cs : List (ScalarPath D L)) (s : Source.Storage D L) (m : SlotView) :
    finiteViewBool cs s m = true ↔ finiteView cs s m := by
  simp only [finiteViewBool,List.all_eq_true,decide_eq_true_eq,finiteView,scalarPathView]

def packedRequestUnchanged {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (p : @PackedSlotPlan D L T ps ts) : Bool :=
  (if p.request.transient then finiteViewBool (selectedSlotPaths (ts p.request.address) p.request.slot)
      (s.source.transient.cells p.request.address) (fun _ => p.request.raw)
    else finiteViewBool (selectedSlotPaths (ps p.request.address) p.request.slot)
      (s.source.world.accounts p.request.address).storage (fun _ => p.request.raw)) &&
    (s.residual.cells p.residualUpdate.1 == p.residualUpdate.2)

/-- Canonical writeback PREPARATION preserves the WHOLE administrative input
when fields AND complement are unchanged. This does not execute a Source/Yul
write: actual execution uses packedSourceStep and retains undo entries/static
refusal even for unchanged writes. None is never converted to a no-op. -/
def packedStateWriteback {D L T} (ps : (a : Roadmap.Address) → List (ScalarPath D (L a)))
    (ts : (a : Roadmap.Address) → List (ScalarPath D (T a)))
    (s : ResidualCompanion D L T complementCarrierOwnership) (q : PackedSlotRequest) : Option (ResidualCompanion D L T complementCarrierOwnership) :=
  (preparePackedSlot ps ts q).map (fun p => if packedRequestUnchanged s p then s else applyPackedSlot s p)

theorem packedStateWriteback_identity {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (q : PackedSlotRequest) (p : @PackedSlotPlan D L T ps ts) (prepared : preparePackedSlot ps ts q = some p)
    (logical : if p.request.transient then finiteView (selectedSlotPaths (ts p.request.address) p.request.slot)
      (s.source.transient.cells p.request.address) (fun _ => p.request.raw)
      else finiteView (selectedSlotPaths (ps p.request.address) p.request.slot)
        (s.source.world.accounts p.request.address).storage (fun _ => p.request.raw))
    (residual : s.residual.cells p.residualUpdate.1 = p.residualUpdate.2) : packedStateWriteback ps ts s q = some s := by
  have unchanged : packedRequestUnchanged s p = true := by
    unfold packedRequestUnchanged
    simp only [Bool.and_eq_true]
    constructor
    · cases tr : p.request.transient
      · exact (finiteViewBool_iff _ _ _).mpr (by simpa only [tr,Bool.false_eq_true,if_false] using logical)
      · exact (finiteViewBool_iff _ _ _).mpr (by simpa only [tr,if_true] using logical)
    · exact beq_iff_eq.mpr residual
  rw [packedStateWriteback,prepared,Option.map_some,if_pos unchanged]

/-- Executable validation of real layout separation, not an assumed view law. -/
def packedSeparationCheck {D L} : List (ScalarPath D L) → Bool
  | [] => true
  | c::cs => cs.all (fun d => decide (c.path ≠ d.path ∧ (c.slot ≠ d.slot ∨
      c.field.offset+c.field.width ≤ d.field.offset ∨ d.field.offset+d.field.width ≤ c.field.offset))) && packedSeparationCheck cs

theorem packedSeparationCheck_iff {D L} (cs : List (ScalarPath D L)) : packedSeparationCheck cs = true ↔ finiteSeparated cs := by
  induction cs with
  | nil => exact ⟨fun _ => .nil,fun _ => rfl⟩
  | cons c cs ih =>
    simp only [packedSeparationCheck,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq,ih,
      finiteSeparated,List.pairwise_cons,pathsApart]

def prepareSeparatedPackedSlot {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy} (ps : (a : Roadmap.Address) → List (ScalarPath D (L a)))
    (ts : (a : Roadmap.Address) → List (ScalarPath D (T a))) (q : PackedSlotRequest) : Option (PackedSlotPlan ps ts) :=
  if (if q.transient then packedSeparationCheck (ts q.address) else packedSeparationCheck (ps q.address)) then
    preparePackedSlot ps ts q else none

theorem prepareSeparatedPackedSlot_layout {D L T ps ts} (q : PackedSlotRequest) (p : @PackedSlotPlan D L T ps ts)
    (prepared : prepareSeparatedPackedSlot ps ts q = some p) :
    (if q.transient then finiteSeparated (ts q.address) else finiteSeparated (ps q.address)) ∧ preparePackedSlot ps ts q = some p := by
  cases tr : q.transient
  all_goals simp only [prepareSeparatedPackedSlot,tr,Bool.false_eq_true,if_false,if_true] at prepared ⊢
  all_goals split at prepared
  all_goals first
    | exact ⟨(packedSeparationCheck_iff _).mp (by assumption),prepared⟩
    | cases prepared

end Solidity.Yul.Views
