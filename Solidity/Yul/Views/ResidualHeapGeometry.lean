import Solidity.Yul.Views.ScratchSourceWriteback

namespace Solidity.Yul.Views

/-- Actual half-open byte intervals, including both empty interval cases.
This is arithmetic separation of current images, not a final view/safety law
or a predicate claiming all assembly programs are supported. -/
def ResidualWindowDisjoint {D : Source.Layout} {h : Source.Heap D}
    (p : Placement h) (es : List (MixedHeapEntry p)) (destination size : Nat) : Prop :=
  ∀ e ∈ es, size=0 ∨ e.image.span=0 ∨ destination+size≤p.address e.id ∨
    p.address e.id+e.image.span≤destination

/-- Whole-map frame for ANY separated residual window, not only scratch.
The actual typed encoder is reused; no layout is reconstructed or assumed. -/
theorem encodeMixedHeap_disjoint_copy {D : Source.Layout} {h : Source.Heap D}
    (p : Placement h) (es : List (MixedHeapEntry p)) (residual src : ByteView)
    (destination start size : Nat) (separate : ResidualWindowDisjoint p es destination size) :
    copyBytes (encodeMixedHeap p es residual) src destination start size=
      encodeMixedHeap p es (copyBytes residual src destination start size) := by
  funext a
  by_cases inside : destination≤a ∧ a<destination+size
  · have outside : ∀ e ∈ es, a<p.address e.id ∨ p.address e.id+e.image.span≤a := by
      intro e member
      rcases separate e member with zero | empty | left | right
      · omega
      · omega
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    rw [encodeMixedHeap_residual p es _ a outside]
    simp only [copyBytes,if_pos inside]
  · rw [copyBytes_outside _ _ _ _ _ _ inside]
    exact (encodeMixedHeap_residual_point p es _ _ a (copyBytes_outside _ _ _ _ _ _ inside)).symm

/-- Exact preservation of BOTH reserved words for a disjoint copy. Zero size
is harmless even when the destination lies inside a reserved word. -/
theorem disjoint_copy_reserved (residual src : ByteView) (free : Roadmap.Word)
    (destination start size : Nat)
    (outside : size=0 ∨ destination+size≤64 ∨ 128≤destination)
    (reserved : ReservedOK residual free) :
    ReservedOK (copyBytes residual src destination start size) free := by
  constructor
  · have same := mload_congr (copyBytes residual src destination start size) residual 64 (fun i => by
      have bound:=i.isLt
      apply copyBytes_outside
      rcases outside with zero | left | right <;> omega)
    exact (congrArg Fin.val same).trans reserved.1
  · intro i
    rw [copyBytes_outside _ _ _ _ _ _ (by
      have bound:=i.isLt
      rcases outside with zero | left | right <;> omega)]
    exact reserved.2 i

/-- Constructor-derived live byte span, not the larger retained/rounded
allocation footprint. This makes real byte-object padding checkable. -/
theorem MemoryImage.bytes_span {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {location : Source.DataLoc} {bytes : List UInt8} (image : MemoryImage p (Source.Data.bytes (l:=location) bytes)) :
    image.span=32+bytes.length := by
  cases image with
  | bytes _ _ => rfl
  | words _ _ encoded => cases encoded

/-- Executable actual-Word range/reserved/entry geometry check. No root/node/
length/fuel cap: entries come from the actual finite heap computation. -/
def residualWindowCheck {D : Source.Layout} {h : Source.Heap D}
    (p : Placement h) (es : List (MixedHeapEntry p)) (destination size : Roadmap.Word) : Bool :=
  (decide (destination.val+size.val≤2^256) &&
    decide (size.val=0 ∨ destination.val+size.val≤64 ∨ 128≤destination.val)) &&
    es.all (fun e => decide (size.val=0 ∨ e.image.span=0 ∨ destination.val+size.val≤p.address e.id ∨
      p.address e.id+e.image.span≤destination.val))

theorem residualWindowCheck_iff {D : Source.Layout} {h : Source.Heap D}
    (p : Placement h) (es : List (MixedHeapEntry p)) (destination size : Roadmap.Word) :
    residualWindowCheck p es destination size=true ↔
      destination.val+size.val≤2^256 ∧
      (size.val=0 ∨ destination.val+size.val≤64 ∨ 128≤destination.val) ∧
      ResidualWindowDisjoint p es destination.val size.val := by
  simp only [residualWindowCheck,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,
    ResidualWindowDisjoint,and_assoc]

theorem residualWindowCheck_overlap {D : Source.Layout} {h : Source.Heap D}
    (p : Placement h) (es : List (MixedHeapEntry p)) (destination size : Roadmap.Word)
    (entry : MixedHeapEntry p) (member : entry∈es) (nonempty : 0<size.val) (live : 0<entry.image.span)
    (left : destination.val<p.address entry.id+entry.image.span)
    (right : p.address entry.id<destination.val+size.val) :
    residualWindowCheck p es destination size≠true := by
  intro checked
  have separate := (residualWindowCheck_iff _ _ _ _).mp checked |>.2.2 entry member
  rcases separate with zero | empty | before | after <;> omega

/-- Only computational preparation equations are stored, NOT assumed inverse,
readback/coverage/safety laws. The actual typed inventory is state-indexed. -/
structure ResidualWindowPlan {D : Source.Layout} {h : Source.Heap D} (p : Placement h) where
  destination : Roadmap.Word
  size : Roadmap.Word
  entries : List (MixedHeapEntry p)
  prepared : prepareHeapInventory p=.ok entries
  checked : residualWindowCheck p entries destination size=true

/-- Error reports exact unsupported occupied IDs. Inner None means failed
physical range/geometry preparation, never a Yul refusal/no-op/cleaning verdict. -/
def prepareResidualWindow {D : Source.Layout} {h : Source.Heap D}
    (p : Placement h) (destination size : Roadmap.Word) : Except (List Nat) (Option (ResidualWindowPlan p)) :=
  match prepared : prepareHeapInventory p with
  | .error ids => .error ids
  | .ok es => if checked : residualWindowCheck p es destination size=true then
      .ok (some ⟨destination,size,es,prepared,checked⟩) else .ok none

theorem prepareResidualWindow_plan {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (plan : ResidualWindowPlan p) : prepareResidualWindow p plan.destination plan.size=.ok (some plan) := by
  cases plan with
  | mk destination size entries prepared checked =>
    unfold prepareResidualWindow
    split
    · rename_i ids bad
      rw [prepared] at bad
      cases bad
    · rename_i es ready
      have same : es=entries := Except.ok.inj (ready.symm.trans prepared)
      subst es
      rw [dif_pos checked]

theorem prepareResidualWindow_none {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (destination size : Roadmap.Word) (es : List (MixedHeapEntry p))
    (prepared : prepareHeapInventory p=.ok es) (failed : residualWindowCheck p es destination size≠true) :
    prepareResidualWindow p destination size=.ok none := by
  unfold prepareResidualWindow
  split
  · rename_i ids bad
    rw [prepared] at bad
    cases bad
  · rename_i entries ready
    have same : entries=es := Except.ok.inj (ready.symm.trans prepared)
    subst entries
    rw [dif_neg failed]

theorem prepareResidualWindow_error {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (destination size : Roadmap.Word) (ids : List Nat) (prepared : prepareHeapInventory p=.error ids) :
    prepareResidualWindow p destination size=.error ids := by
  unfold prepareResidualWindow
  split
  · rename_i bad ready
    have same : bad=ids := Except.error.inj (ready.symm.trans prepared)
    subst bad
    rfl
  · rename_i entries ready
    rw [prepared] at ready
    cases ready

theorem prepareResidualWindow_metadata {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (destination size : Roadmap.Word) (plan : ResidualWindowPlan p)
    (ready : prepareResidualWindow p destination size=.ok (some plan)) :
    plan.destination=destination ∧ plan.size=size := by
  unfold prepareResidualWindow at ready
  split at ready
  · cases ready
  · split at ready
    · have same := Option.some.inj (Except.ok.inj ready)
      rw [←same]
      exact ⟨rfl,rfl⟩
    · cases Except.ok.inj ready

end Solidity.Yul.Views
