import Solidity.Yul.Views.PackedResidualCodec
import Solidity.Source.Hoare

/-! Canonical typed cell writes preserve a complete finite packed view. This
uses the existing physical field patch and actual Source.Storage write; it is
not changing-inventory or dirty-owned representation adequacy. -/
namespace Solidity.Yul.Views.PackedCellUpdate

theorem apart {D L} (cs : List (ScalarPath D L)) (separated : finiteSeparated cs)
    (c d : ScalarPath D L) (hc : c ∈ cs) (hd : d ∈ cs) (different : c ≠ d) :
    c.path ≠ d.path ∧ pathsApart c d := by
  first | (simp only;done) | skip
  induction cs with
  | nil => cases hc
  | cons head tail ih =>
    obtain ⟨front,rest⟩ := List.pairwise_cons.mp separated
    rcases List.mem_cons.mp hc with equalC | cTail
    · subst c
      rcases List.mem_cons.mp hd with equalD | dTail
      · subst d; exact False.elim (different rfl)
      · exact front d dTail
    · rcases List.mem_cons.mp hd with equalD | dTail
      · subst d
        have pair := front c cTail
        exact ⟨Ne.symm pair.1,pathsApart_symm pair.2⟩
      · exact ih rest cTail dTail

def raw {D L} (c : ScalarPath D L) (value : Source.Val D (L c.path)) (m : SlotView) :=
  patchScalarSlot m c.slot c.field (c.codec.encode value)

/-- A write entirely inside an owned field leaves the complete complement unchanged. -/
theorem complement {D L} (cs : List (ScalarPath D L)) (c : ScalarPath D L)
    (member : c ∈ cs) (value : Source.Val D (L c.path)) (m : SlotView) :
    packedMask cs (raw c value m)=packedMask cs m := by
  first | (simp only;done) | skip
  funext slot
  apply word_eq_of_lowBytes
  intro i
  cases owned : packedOwnsByte cs slot i
  · rw [packedMask_residual _ _ _ _ owned,packedMask_residual _ _ _ _ owned]
    by_cases same : slot=c.slot
    · subst slot
      have outside : i.val<c.field.offset ∨ c.field.offset+c.field.width≤i.val := by
        by_cases inside : c.field.offset≤i.val ∧ i.val<c.field.offset+c.field.width
        · have byte : packedOwnsByte cs c.slot i=true := (packedOwnsByte_iff _ _ _).mpr
            ⟨c,member,rfl,inside.1,inside.2⟩
          rw [owned] at byte
          contradiction
        · omega
      rw [raw,patchScalarSlot,find_saveSlot]
      exact c.field.lowByte_other (m c.slot) (c.codec.encode value) i outside
    · rw [raw,patchScalarSlot,find_saveSlot_other _ _ _ _ same]
  · rw [packedMask_owned_zero _ _ _ _ owned,packedMask_owned_zero _ _ _ _ owned]

theorem view {D L} (cs : List (ScalarPath D L)) (c : ScalarPath D L)
    (member : c ∈ cs) (separated : finiteSeparated cs) (s : Source.Storage D L)
    (m : SlotView) (before : finiteView cs s m) (value : Source.Val D (L c.path)) :
    finiteView cs (s.write c.path value) (raw c value m) := by
  first | (simp only;done) | skip
  intro d inside
  by_cases same : d=c
  · subst d
    simp only [scalarPathView,Source.Storage.write_read,Option.map_some,raw,patchScalarSlot_find]
  · have pair := apart cs separated c d member inside (Ne.symm same)
    unfold scalarPathView
    rw [Source.Storage.write_other s (Ne.symm pair.1) value]
    rw [raw,patchScalarSlot_other_field m c.slot d.slot c.field d.field (c.codec.encode value) pair.2]
    exact before d inside

theorem unchanged {D L} (cs : List (ScalarPath D L)) (c : ScalarPath D L)
    (member : c ∈ cs) (separated : finiteSeparated cs) (s : Source.Storage D L)
    (m : SlotView) (before : finiteView cs s m) (value : Source.Val D (L c.path)) :
    finiteWriteback cs (raw c value m) (s.write c.path value)=some (s.write c.path value) :=
  finiteWriteback_unchanged cs _ _ (view cs c member separated s m before value)

theorem reencode {D L} (cs : List (ScalarPath D L)) (c : ScalarPath D L)
    (member : c ∈ cs) (separated : finiteSeparated cs) (s : Source.Storage D L)
    (m : SlotView) (before : finiteView cs s m) (value : Source.Val D (L c.path)) :
    finiteEncode cs (s.write c.path value) (packedMask cs (raw c value m))=some (raw c value m) :=
  finiteEncode_fromComplement cs _ _ separated (view cs c member separated s m before value)

theorem reencode_original_complement {D L} (cs : List (ScalarPath D L)) (c : ScalarPath D L)
    (member : c ∈ cs) (separated : finiteSeparated cs) (s : Source.Storage D L)
    (m : SlotView) (before : finiteView cs s m) (value : Source.Val D (L c.path)) :
    finiteEncode cs (s.write c.path value) (packedMask cs m)=some (raw c value m) := by
  rw [←complement cs c member value m]
  exact reencode cs c member separated s m before value

/-- Actual persistent Source administration; static refusal is not preparation. -/
theorem source {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (c : ScalarPath E.layout (E.lay F.this)) (value : Source.Val E.layout (E.cellTy c.path))
    (bank : E.transientRoot c.path=false) (allowed : F.static=false) :
    (Source.setCell F c.path (some value)).run s=
      (.ok (),(s.1,{s.2 with ex:=s.2.ex.apply (.account F.this
        (fun account => {account with storage:=account.storage.write c.path value}))})) := by
  first | (simp only;done) | skip
  simp only [Source.setCell,bank,Bool.false_eq_true,if_false,Source.applyOp,allowed]
  rfl

theorem source_view {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (cs : List (ScalarPath E.layout (E.lay F.this))) (c : ScalarPath E.layout (E.lay F.this))
    (member : c ∈ cs) (separated : finiteSeparated cs) (m : SlotView)
    (before : finiteView cs (s.2.ex.world.accounts F.this).storage m)
    (value : Source.Val E.layout (E.cellTy c.path))
    (bank : E.transientRoot c.path=false) (allowed : F.static=false) :
    finiteView cs (((Source.setCell F c.path (some value)).run s).2.2.ex.world.accounts F.this).storage
      (raw c value m) := by
  rw [source F s c value bank allowed]
  change finiteView cs ((s.2.ex.world.set F.this _).accounts F.this).storage _
  rw [Source.World.set_get]
  exact view cs c member separated _ m before value
theorem source_reencode {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (cs : List (ScalarPath E.layout (E.lay F.this))) (c : ScalarPath E.layout (E.lay F.this))
    (member : c ∈ cs) (separated : finiteSeparated cs) (m : SlotView)
    (before : finiteView cs (s.2.ex.world.accounts F.this).storage m)
    (value : Source.Val E.layout (E.cellTy c.path))
    (bank : E.transientRoot c.path=false) (allowed : F.static=false) :
    finiteEncode cs (((Source.setCell F c.path (some value)).run s).2.2.ex.world.accounts F.this).storage
      (packedMask cs m)=some (raw c value m) := by
  rw [←complement cs c member value m]
  exact finiteEncode_fromComplement cs _ _ separated (source_view F s cs c member separated m before value bank allowed)
end Solidity.Yul.Views.PackedCellUpdate
