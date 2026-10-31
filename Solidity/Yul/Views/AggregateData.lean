import Solidity.Yul.Views.PackedSlots

/-! Direct actual Source.Data entry points for the supported storage aggregate
components. A logical storage reference is not its contents; resolve it through
its owner's source state before encoding. Such reference-only inputs return none. -/
namespace Solidity.Yul.Views

def encodePackedStruct {D : Source.Layout} (d : Source.DeclName)
    (cs : PackedMembers D (D.fields d)) (base : Roadmap.Word) (fits : cs.Fits base)
    (data : Source.Data D (.struct .storage d)) (m : SlotView) : Option SlotView := by
  cases data with
  | val _ => exact none
  | struct ds => exact cs.encodeSlots ds base fits m

def encodePackedArray {D : Source.Layout} {τ : Source.STy} (f : Field)
    (w : StorageWidth D τ f.width) (c : ScalarCodec D τ f) (n : Nat) (_ : 0 < n)
    (base : Roadmap.Word) (fits : (repeatedMembers f w c n).Fits base)
    (data : Source.Data D (.array .storage τ (some n))) (m : SlotView) : Option SlotView := by
  cases data with
  | val _ => exact none
  | array len hl xs =>
    have he : n = len := hl n rfl
    subst len
    exact (repeatedMembers f w c n).encodeSlots (arrayMembers n xs) base fits m

theorem encodePackedArray_contents {D : Source.Layout} {τ : Source.STy} (f : Field)
    (w : StorageWidth D τ f.width) (c : ScalarCodec D τ f) (n : Nat) (hn : 0 < n)
    (base : Roadmap.Word) (fits : (repeatedMembers f w c n).Fits base)
    (xs : Fin n → Source.Data D τ) (m : SlotView) :
    encodePackedArray f w c n hn base fits (.array n (fun _ h => (Option.some.inj h).symm) xs) m =
      (repeatedMembers f w c n).encodeSlots (arrayMembers n xs) base fits m := rfl

theorem structData_roundtrip {D : Source.Layout} (d : Source.DeclName)
    (cs : PackedMembers D (D.fields d)) (base : Roadmap.Word) (fits : cs.Fits base)
    (ds : Source.DataList D (D.fields d)) (h : ScalarMembers ds) (m : SlotView) :
    ∃ out, encodePackedStruct d cs base fits (.struct ds) m = some out ∧
      decodePackedStruct d cs base fits (slotBytes out) = some (.struct ds) := by
  obtain ⟨bs, e⟩ := cs.encode_exists ds h _ (slotBytes m)
  refine ⟨slotsOfBytes bs, ?_, ?_⟩
  · change (cs.encode ds (base.val * 32) (slotBytes m)).map slotsOfBytes = _
    rw [e]; rfl
  · simp only [decodePackedStruct, cs.slot_roundtrip ds base fits m bs e, Option.map_some]

theorem arrayData_roundtrip {D : Source.Layout} {τ : Source.STy} (f : Field)
    (w : StorageWidth D τ f.width) (c : ScalarCodec D τ f) (n : Nat) (hn : 0 < n)
    (base : Roadmap.Word) (fits : (repeatedMembers f w c n).Fits base)
    (xs : Fin n → Source.Val D τ) (m : SlotView) :
    ∃ out, encodePackedArray f w c n hn base fits
        (.array n (fun _ h => (Option.some.inj h).symm) (fun i => .val (xs i))) m = some out ∧
      decodePackedArray f w c n hn base fits (slotBytes out) =
        some (.array n (fun _ h => (Option.some.inj h).symm) (fun i => .val (xs i))) := by
  obtain ⟨bs, e⟩ := (repeatedMembers f w c n).encode_exists _ (arrayMembers_scalar n xs) _ (slotBytes m)
  refine ⟨slotsOfBytes bs, ?_, ?_⟩
  · rw [encodePackedArray_contents]
    change ((repeatedMembers f w c n).encode _ _ _).map slotsOfBytes = _
    rw [e]; rfl
  · simp only [decodePackedArray, PackedMembers.slot_roundtrip _ _ base fits m bs e,
      Option.map_some, membersArray_arrayMembers]

theorem structData_refuses_reference {D : Source.Layout} (d : Source.DeclName)
    (cs : PackedMembers D (D.fields d)) (base : Roadmap.Word) (fits : cs.Fits base)
    (path : Source.SPath) (m : SlotView) :
    encodePackedStruct d cs base fits (.val (.storRef rfl path)) m = none := rfl

theorem arrayData_refuses_reference {D : Source.Layout} {τ : Source.STy} (f : Field)
    (w : StorageWidth D τ f.width) (c : ScalarCodec D τ f) (n : Nat) (hn : 0 < n)
    (base : Roadmap.Word) (fits : (repeatedMembers f w c n).Fits base)
    (path : Source.SPath) (m : SlotView) :
    encodePackedArray f w c n hn base fits (.val (.storRef rfl path)) m = none := rfl

theorem structData_unchanged {D : Source.Layout} (d : Source.DeclName)
    (cs : PackedMembers D (D.fields d)) (base : Roadmap.Word) (fits : cs.Fits base)
    (ds : Source.DataList D (D.fields d)) (m : SlotView)
    (h : cs.matches ds (base.val * 32) (slotBytes m)) :
    encodePackedStruct d cs base fits (.struct ds) m = some m :=
  cs.slot_unchanged ds base fits m h

theorem arrayData_unchanged {D : Source.Layout} {τ : Source.STy} (f : Field)
    (w : StorageWidth D τ f.width) (c : ScalarCodec D τ f) (n : Nat) (hn : 0 < n)
    (base : Roadmap.Word) (fits : (repeatedMembers f w c n).Fits base)
    (xs : Fin n → Source.Data D τ) (m : SlotView)
    (h : (repeatedMembers f w c n).matches (arrayMembers n xs) (base.val * 32) (slotBytes m)) :
    encodePackedArray f w c n hn base fits
      (.array n (fun _ h => (Option.some.inj h).symm) xs) m = some m := by
  rw [encodePackedArray_contents]
  exact PackedMembers.slot_unchanged _ _ base fits m h

theorem PackedMembers.encodedSlots_residual {D : Source.Layout} {τs : List Source.STy}
    (cs : PackedMembers D τs) (ds : Source.DataList D τs) (base : Roadmap.Word)
    (fits : cs.Fits base) (m out : SlotView) (e : cs.encodeSlots ds base fits m = some out)
    (a : Nat) (bound : a < (2 ^ 256) * 32) (unowned : ¬ cs.owns (base.val * 32) a) :
    slotBytes out a = slotBytes m a := by
  unfold PackedMembers.encodeSlots at e
  cases he : cs.encode ds (base.val * 32) (slotBytes m) with
  | none => simp only [he, Option.map_none] at e; cases e
  | some bs =>
    simp only [he, Option.map_some] at e
    cases e
    exact cs.slot_residual_byte ds base m bs he a bound unowned

end Solidity.Yul.Views
