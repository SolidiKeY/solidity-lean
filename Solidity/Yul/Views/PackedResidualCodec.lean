import Solidity.Yul.Views.PackedResidualMask

namespace Solidity.Yul.Views

theorem slotBytes_lowByte (m : SlotView) (q : Roadmap.Word) (i : Fin 32) :
    slotBytes m (q.val*32+i.val) = lowByte (m q) i := by
  have div : (q.val*32+i.val)/32 = q.val := by have hi := i.isLt; omega
  have mod : (q.val*32+i.val)%32 = i.val := by have hi := i.isLt; omega
  simp only [slotBytes,div,mod,Nat.mod_eq_of_lt q.isLt,lowByte]

theorem unowned_coordinates {D L} (cs : List (ScalarPath D L)) (q : Roadmap.Word) (i : Fin 32)
    (unowned : packedOwnsByte cs q i = false) : ∀ c ∈ cs, scalarByteUnowned c.slot c.field (q.val*32+i.val) := by
  intro c member
  have div : (q.val*32+i.val)/32 = q.val := by have hi := i.isLt; omega
  have mod : (q.val*32+i.val)%32 = i.val := by have hi := i.isLt; omega
  unfold scalarByteUnowned
  rw [div,mod]
  by_cases eq : c.slot = q
  · subst q
    have no : ¬(c.field.offset ≤ i.val ∧ i.val < c.field.offset+c.field.width) := by
      intro yes
      have owned := (packedOwnsByte_iff cs c.slot i).mpr ⟨c,member,rfl,yes⟩
      rw [unowned] at owned
      cases owned
    omega
  · exact Or.inl (fun same => eq (Fin.ext same.symm))

/-- Owned fields plus the computed complement reconstruct the ENTIRE supplied
physical map, including nonzero padding/high bytes in partially owned slots. -/
theorem finiteEncode_fromComplement {D L} (cs : List (ScalarPath D L)) (s : Source.Storage D L)
    (m : SlotView) (sep : finiteSeparated cs) (view : finiteView cs s m) :
    finiteEncode cs s (packedMask cs m) = some m := by
  have available : ∀ c ∈ cs, ∃ v, s.read c.path = some v := by
    intro c member
    obtain ⟨v,read,_⟩ := Option.map_eq_some_iff.mp (view c member)
    exact ⟨v,read⟩
  obtain ⟨out,encoded⟩ := finiteEncode_exists cs s (packedMask cs m) available
  have outputView := finiteEncode_view cs s (packedMask cs m) out sep encoded
  have equal : out = m := by
    funext q
    apply word_eq_of_lowBytes
    intro i
    cases ownership : packedOwnsByte cs q i with
    | true =>
      obtain ⟨c,member,slot,inside⟩ := (packedOwnsByte_iff cs q i).mp ownership
      have payload : c.field.findWord (out c.slot) = c.field.findWord (m c.slot) :=
        Option.some.inj ((outputView c member).symm.trans (view c member))
      rw [slot] at payload
      exact c.field.lowByte_of_find (out q) (m q) payload i inside
    | false =>
      have residual := finiteEncode_residual cs s (packedMask cs m) out encoded (q.val*32+i.val)
        (by have hq := q.isLt; have hi := i.isLt; omega) (unowned_coordinates cs q i ownership)
      rw [slotBytes_lowByte,slotBytes_lowByte] at residual
      exact residual.trans (packedMask_residual cs m q i ownership)
  rw [equal] at encoded
  exact encoded

/-- Pure actual-store writeback keeps the original store as input and the
precise complement of the SAME snapshot, never caller-supplied padding. -/
def packedStoreWriteback {D L} (cs : List (ScalarPath D L)) (m : SlotView) (s : Source.Storage D L) :
    Option (Source.Storage D L × SlotView) := (finiteWriteback cs m s).map (fun out => (out,packedMask cs m))

theorem packedStoreWriteback_reencode {D L} (cs : List (ScalarPath D L)) (m : SlotView)
    (s out : Source.Storage D L) (residual : SlotView) (sep : finiteSeparated cs)
    (step : packedStoreWriteback cs m s = some (out,residual)) : finiteEncode cs out residual = some m := by
  obtain ⟨written,decoded,same⟩ := Option.map_eq_some_iff.mp step
  cases same
  exact finiteEncode_fromComplement cs out m sep (finiteWriteback_result_view cs m s out sep decoded)

theorem packedMask_idempotent {D L} (cs : List (ScalarPath D L)) (m : SlotView) : packedMask cs (packedMask cs m) = packedMask cs m := by
  funext q
  apply word_eq_of_lowBytes
  intro i
  simp only [packedMask,complementWord_byte]
  cases packedOwnsByte cs q i <;> rfl

theorem packedStoreWriteback_unchanged {D L} (cs : List (ScalarPath D L)) (m residual : SlotView)
    (s : Source.Storage D L) (view : finiteView cs s m) (sameResidual : packedMask cs m = residual) :
    packedStoreWriteback cs m s = some (s,residual) := by
  rw [packedStoreWriteback,finiteWriteback_unchanged cs m s view,Option.map_some,sameResidual]

theorem packedStoreWriteback_other {D L} (cs : List (ScalarPath D L)) (m : SlotView)
    (s out : Source.Storage D L) (residual : SlotView) (step : packedStoreWriteback cs m s = some (out,residual))
    (p : Source.SPath) (unselected : ∀ c ∈ cs, p ≠ c.path) : out.cell p = s.cell p := by
  obtain ⟨written,decoded,same⟩ := Option.map_eq_some_iff.mp step
  cases same
  exact finiteWriteback_other cs m s out decoded p unselected

end Solidity.Yul.Views
