import Solidity.Yul.Views.OwnedBoolUpdates

namespace Solidity.Yul.Views

theorem representedBool_unchanged_value (D : Source.Layout) (field : Field) (width : field.width=1)
    (old : BoolTrueByte) (value : Source.Val D .bool) :
    chooseTrueByte old (fieldBooleanByte field width ((representedBoolCodec D field width old).encode value))=old := by
  cases value with
  | bool b => exact representedBool_unchanged D field width old b
  | memRef h _ | storRef h _ | cdRef h _ => cases h

theorem codec_cast_encode {D σ τ field} (same : σ=τ) (codec : ScalarCodec D τ field) (value : Source.Val D σ) :
    (same.symm ▸ codec).encode value=codec.encode (same ▸ value) := by
  cases same
  rfl

theorem chosenPathCode_view {D L} (c : ScalarPath D L) (old : BoolTrueByte)
    (s : Source.Storage D L) (raw : SlotView)
    (view : scalarPathView (representedPath c old).path (representedPath c old).codec (representedPath c old).slot s raw) :
    chosenPathCode c old raw=old := by
  unfold chosenPathCode
  split
  · rename_i typed
    unfold representedPath at view
    rw [dif_pos typed] at view
    obtain ⟨value,read,encoded⟩ := Option.map_eq_some_iff.mp view
    rw [codec_cast_encode typed] at encoded
    have unchanged := representedBool_unchanged_value D c.field (c.bool_width typed) old (typed ▸ value)
    rw [encoded] at unchanged
    exact unchanged
  · rfl

theorem encodingWrites_unchanged {D L} (cs : List (ScalarPath D L)) (bank) (a)
    (raw : SlotView) (before : BoolEncodingJournal) (s : Source.Storage D L)
    (view : finiteView (representedRegistry cs bank a before) s raw) : encodingWrites cs bank a raw before=[] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro c member
  unfold pathEncodingWrite
  have here := view (representedPath c (before.cells (ownedByteKey bank a c))) (List.mem_map.mpr ⟨c,member,rfl⟩)
  have unchanged := chosenPathCode_view c _ s raw here
  dsimp only
  rw [unchanged,if_pos rfl]

theorem representedRegistry_owns {D L} (cs : List (ScalarPath D L)) (bank) (a) (before)
    (slot : Roadmap.Word) (i : Fin 32) :
    packedOwnsByte (representedRegistry cs bank a before) slot i=packedOwnsByte cs slot i := by
  simp only [packedOwnsByte,representedRegistry,List.any_map,Function.comp_def,representedPath_slot,representedPath_field]

theorem representedRegistry_mask {D L} (cs : List (ScalarPath D L)) (bank) (a) (before) (raw : SlotView) :
    packedMask (representedRegistry cs bank a before) raw=packedMask cs raw := by
  funext slot
  unfold packedMask
  have same : packedOwnsByte (representedRegistry cs bank a before) slot=packedOwnsByte cs slot := by
    funext i
    exact representedRegistry_owns cs bank a before slot i
  rw [same]

/-- Pure preparation decodes the SAME actual source values and preserves the
WHOLE administrative store and representation journal on an unchanged view. -/
def representedStoreWriteback {D L} (cs : List (ScalarPath D L)) (bank) (a) (raw : SlotView)
    (before : BoolEncodingJournal) (s : Source.Storage D L) :=
  let encoding := boolEncodingRun before (encodingWrites cs bank a raw before)
  (packedStoreWriteback (representedRegistry cs bank a encoding) raw s).map fun result => (result,encoding)

theorem representedStoreWriteback_unchanged {D L} (cs : List (ScalarPath D L)) (bank) (a)
    (raw : SlotView) (before : BoolEncodingJournal) (s : Source.Storage D L)
    (view : finiteView (representedRegistry cs bank a before) s raw) :
    representedStoreWriteback cs bank a raw before s=some ((s,packedMask cs raw),before) := by
  unfold representedStoreWriteback
  rw [encodingWrites_unchanged cs bank a raw before s view]
  dsimp only [boolEncodingRun]
  rw [packedStoreWriteback_unchanged _ _ _ _ view (representedRegistry_mask cs bank a before raw),Option.map_some]

end Solidity.Yul.Views
