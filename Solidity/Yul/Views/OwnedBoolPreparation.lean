import Solidity.Yul.Views.OwnedBoolFollowing

namespace Solidity.Yul.Views

theorem canonicalDecode_cast_exists {D σ τ field} (same : σ=τ) (codec : ScalarCodec D τ field) (raw : field.Value)
    (found : ∃ v, canonicalScalarDecode codec raw=some v) :
    ∃ v, canonicalScalarDecode (same.symm ▸ codec) raw=some v := by
  cases same
  exact found

/-- A bool field's selected physical representation always decodes its complete
owned byte. Other scalar types keep their ORIGINAL validation behaviour. -/
theorem chosenPath_bool_decodes {D L} (c : ScalarPath D L) (old : BoolTrueByte) (raw : SlotView)
    (typed : L c.path=.bool) :
    ∃ v, canonicalScalarDecode (representedPath c (chosenPathCode c old raw)).codec
      ((representedPath c (chosenPathCode c old raw)).field.findWord (raw c.slot))=some v := by
  unfold representedPath
  rw [dif_pos typed]
  apply canonicalDecode_cast_exists typed
  refine ⟨.bool (boolByteMeaning (fieldBooleanByte c.field (c.bool_width typed) (c.field.findWord (raw c.slot)))),?_⟩
  unfold chosenPathCode
  rw [dif_pos typed]
  exact representedBool_canonicalDecode_raw D c.field (c.bool_width typed) old _

theorem finitePrepare_found {D L} (cs : List (ScalarPath D L)) (raw : SlotView)
    (each : ∀ c ∈ cs, ∃ v, canonicalScalarDecode c.codec (c.field.findWord (raw c.slot))=some v) :
    (finitePrepare cs raw).isSome := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨v,ready⟩ := each c List.mem_cons_self
    have tail := ih (fun d member => each d (List.mem_cons_of_mem _ member))
    unfold finitePrepare
    rw [ready]
    simpa only [Option.bind_some,Option.isSome_map] using tail

/-- The only input conditions here are actual original non-bool codec checks
and genuine coordinate separation, not an assumed inverse/result-view law. -/
theorem representedPrepare_found {D L} (cs : List (ScalarPath D L)) (bank) (a) (encoding) (raw : SlotView)
    (separated : finiteSeparated cs)
    (nonbool : ∀ c ∈ cs, L c.path≠.bool → (canonicalScalarDecode c.codec (c.field.findWord (raw c.slot))).isSome) :
    (finitePrepare (representedRegistry cs bank a (boolEncodingRun encoding (encodingWrites cs bank a raw encoding))) raw).isSome := by
  apply finitePrepare_found
  intro represented member
  obtain ⟨c,inside,same⟩ := List.mem_map.mp member
  subst represented
  rw [encodingWrites_result cs bank a raw encoding separated c inside,representedPath_slot]
  by_cases typed : L c.path=.bool
  · exact chosenPath_bool_decodes c _ raw typed
  · rw [show chosenPathCode c (encoding.cells (ownedByteKey bank a c)) raw=encoding.cells (ownedByteKey bank a c) from dif_neg typed]
    rw [representedPath_nonbool c _ typed]
    exact Option.isSome_iff_exists.mp (nonbool c inside typed)

theorem representedRegistry_nonbool {D L} (cs : List (ScalarPath D L)) (bank) (a) (encoding)
    (nonbool : ∀ c ∈ cs, L c.path≠.bool) : representedRegistry cs bank a encoding=cs := by
  calc
    representedRegistry cs bank a encoding=cs.map id := by
      apply List.map_congr_left
      intro c member
      exact representedPath_nonbool c _ (nonbool c member)
    _=cs := List.map_id cs

end Solidity.Yul.Views
