import Solidity.Yul.Views.ScalarBytes
import Solidity.Yul.Views.PackedSlots

/-!
# Concrete canonical scalar-path writeback into actual Source.Storage

Only successfully decoded canonical payloads are supported here. None means
unsupported preparation input, not an assembly revert/refusal/no-op semantics.
Dirty/noncanonical owned bits still require the full physical/source extension.
Unchanged values preserve the original administrative cell, including none.
-/
namespace Solidity.Yul.Views

theorem ScalarCodec.encode_injective {D : Source.Layout} {τ : Source.STy} {f : Field}
    (c : ScalarCodec D τ f) {v w : Source.Val D τ} (h : c.encode v = c.encode w) : v = w := by
  have hd := congrArg c.decode h
  rw [c.decode_encode, c.decode_encode] at hd
  exact Option.some.inj hd

def canonicalScalarDecode {D : Source.Layout} {τ : Source.STy} {f : Field}
    (c : ScalarCodec D τ f) (raw : f.Value) : Option (Source.Val D τ) :=
  (c.decode raw).bind (fun v => if c.encode v = raw then some v else none)

theorem canonicalScalarDecode_encode {D : Source.Layout} {τ : Source.STy} {f : Field}
    (c : ScalarCodec D τ f) (v : Source.Val D τ) : canonicalScalarDecode c (c.encode v) = some v := by
  simp only [canonicalScalarDecode, c.decode_encode, Option.bind_some, if_true]

theorem canonicalScalarDecode_sound {D : Source.Layout} {τ : Source.STy} {f : Field}
    (c : ScalarCodec D τ f) (raw : f.Value) (v : Source.Val D τ)
    (e : canonicalScalarDecode c raw = some v) : c.decode raw = some v ∧ c.encode v = raw := by
  obtain ⟨w, hd, hw⟩ := Option.bind_eq_some_iff.mp e
  split at hw
  · rename_i h
    cases hw
    exact ⟨hd, h⟩
  · cases hw

/-- Encoded comparison avoids requiring extrinsic equality on source values. -/
def preserveScalarWrite {D : Source.Layout} {L : Source.SPath → Source.STy}
    {f : Field} (p : Source.SPath) (c : ScalarCodec D (L p) f)
    (v : Source.Val D (L p)) (s : Source.Storage D L) : Source.Storage D L :=
  if (s.read p).map c.encode = some (c.encode v) then s else s.write p v

theorem preserveScalarWrite_read {D : Source.Layout} {L : Source.SPath → Source.STy}
    {f : Field} (p : Source.SPath) (c : ScalarCodec D (L p) f)
    (v : Source.Val D (L p)) (s : Source.Storage D L) : (preserveScalarWrite p c v s).read p = some v := by
  unfold preserveScalarWrite
  split
  · rename_i h
    obtain ⟨old, hr, hv⟩ := Option.map_eq_some_iff.mp h
    have he := c.encode_injective hv
    rw [he] at hr
    exact hr
  · exact Source.Storage.write_read s p v

theorem preserveScalarWrite_unchanged {D : Source.Layout} {L : Source.SPath → Source.STy}
    {f : Field} (p : Source.SPath) (c : ScalarCodec D (L p) f)
    (v : Source.Val D (L p)) (s : Source.Storage D L) (h : s.read p = some v) :
    preserveScalarWrite p c v s = s := by
  simp only [preserveScalarWrite, h, Option.map_some, if_true]

theorem preserveScalarWrite_changed {D : Source.Layout} {L : Source.SPath → Source.STy}
    {f : Field} (p : Source.SPath) (c : ScalarCodec D (L p) f)
    (v : Source.Val D (L p)) (s : Source.Storage D L)
    (h : (s.read p).map c.encode ≠ some (c.encode v)) : preserveScalarWrite p c v s = s.write p v := by
  simp only [preserveScalarWrite, if_neg h]

theorem preserveScalarWrite_cell_other {D : Source.Layout} {L : Source.SPath → Source.STy}
    {f : Field} (p q : Source.SPath) (c : ScalarCodec D (L p) f)
    (v : Source.Val D (L p)) (s : Source.Storage D L) (h : q ≠ p) :
    (preserveScalarWrite p c v s).cell q = s.cell q := by
  unfold preserveScalarWrite
  split
  · rfl
  · simp only [Source.Storage.write, Source.Storage.set, dif_neg h]

theorem preserveScalarWrite_other_read {D : Source.Layout} {L : Source.SPath → Source.STy}
    {f : Field} (p q : Source.SPath) (c : ScalarCodec D (L p) f)
    (v : Source.Val D (L p)) (s : Source.Storage D L) (h : q ≠ p) :
    (preserveScalarWrite p c v s).read q = s.read q := by
  unfold Source.Storage.read
  rw [preserveScalarWrite_cell_other p q c v s h]

theorem preserveScalarWrite_idempotent {D : Source.Layout} {L : Source.SPath → Source.STy}
    {f : Field} (p : Source.SPath) (c : ScalarCodec D (L p) f)
    (v : Source.Val D (L p)) (s : Source.Storage D L) :
    preserveScalarWrite p c v (preserveScalarWrite p c v s) = preserveScalarWrite p c v s :=
  preserveScalarWrite_unchanged p c v _ (preserveScalarWrite_read p c v s)

def canonicalPathWriteback {D : Source.Layout} {L : Source.SPath → Source.STy} {f : Field}
    (p : Source.SPath) (c : ScalarCodec D (L p) f) (slot : Roadmap.Word)
    (m : SlotView) (s : Source.Storage D L) : Option (Source.Storage D L) :=
  (canonicalScalarDecode c (f.findWord (m slot))).map (fun v => preserveScalarWrite p c v s)

def scalarPathView {D : Source.Layout} {L : Source.SPath → Source.STy} {f : Field}
    (p : Source.SPath) (c : ScalarCodec D (L p) f) (slot : Roadmap.Word)
    (s : Source.Storage D L) (m : SlotView) : Prop :=
  (s.read p).map c.encode = some (f.findWord (m slot))

def patchScalarSlot (m : SlotView) (slot : Roadmap.Word) (f : Field) (v : f.Value) : SlotView :=
  saveSlot m slot (f.saveWord (m slot) v)

def encodeScalarPath {D : Source.Layout} {L : Source.SPath → Source.STy} {f : Field}
    (p : Source.SPath) (c : ScalarCodec D (L p) f) (slot : Roadmap.Word)
    (s : Source.Storage D L) (residual : SlotView) : Option SlotView :=
  (s.read p).map (fun v => patchScalarSlot residual slot f (c.encode v))

theorem patchScalarSlot_find (m : SlotView) (slot : Roadmap.Word) (f : Field) (v : f.Value) :
    f.findWord (patchScalarSlot m slot f v slot) = v := by
  rw [patchScalarSlot, find_saveSlot, Field.find_saveWord]

theorem encodeScalarPath_view {D : Source.Layout} {L : Source.SPath → Source.STy} {f : Field}
    (p : Source.SPath) (c : ScalarCodec D (L p) f) (slot : Roadmap.Word)
    (s : Source.Storage D L) (residual out : SlotView) (e : encodeScalarPath p c slot s residual = some out) :
    scalarPathView p c slot s out := by
  obtain ⟨v, hr, he⟩ := Option.map_eq_some_iff.mp e
  subst out
  simp only [scalarPathView, hr, Option.map_some, patchScalarSlot_find]

theorem canonicalPathWriteback_unchanged {D : Source.Layout} {L : Source.SPath → Source.STy} {f : Field}
    (p : Source.SPath) (c : ScalarCodec D (L p) f) (slot : Roadmap.Word)
    (s : Source.Storage D L) (m : SlotView) (h : scalarPathView p c slot s m) :
    canonicalPathWriteback p c slot m s = some s := by
  obtain ⟨v, hr, hv⟩ := Option.map_eq_some_iff.mp h
  unfold canonicalPathWriteback
  rw [← hv, canonicalScalarDecode_encode]
  simp only [Option.map_some, preserveScalarWrite_unchanged p c v s hr]

theorem canonicalPathWriteback_result_view {D : Source.Layout} {L : Source.SPath → Source.STy} {f : Field}
    (p : Source.SPath) (c : ScalarCodec D (L p) f) (slot : Roadmap.Word)
    (s s' : Source.Storage D L) (m : SlotView) (e : canonicalPathWriteback p c slot m s = some s') :
    scalarPathView p c slot s' m := by
  obtain ⟨v, hd, he⟩ := Option.map_eq_some_iff.mp e
  subst s'
  simp only [scalarPathView, preserveScalarWrite_read, Option.map_some,
    (canonicalScalarDecode_sound c _ v hd).2]

theorem canonicalPathWriteback_cell_other {D : Source.Layout} {L : Source.SPath → Source.STy} {f : Field}
    (p q : Source.SPath) (c : ScalarCodec D (L p) f) (slot : Roadmap.Word)
    (s s' : Source.Storage D L) (m : SlotView) (e : canonicalPathWriteback p c slot m s = some s') (h : q ≠ p) :
    s'.cell q = s.cell q := by
  obtain ⟨v, _, he⟩ := Option.map_eq_some_iff.mp e
  subst s'
  exact preserveScalarWrite_cell_other p q c v s h

theorem canonicalPathWriteback_changed {D : Source.Layout} {L : Source.SPath → Source.STy} {f : Field}
    (p : Source.SPath) (c : ScalarCodec D (L p) f) (slot : Roadmap.Word)
    (s : Source.Storage D L) (m : SlotView) (v : Source.Val D (L p))
    (hd : canonicalScalarDecode c (f.findWord (m slot)) = some v)
    (changed : (s.read p).map c.encode ≠ some (f.findWord (m slot))) :
    canonicalPathWriteback p c slot m s = some (s.write p v) := by
  simp only [canonicalPathWriteback, hd, Option.map_some]
  apply congrArg some
  exact preserveScalarWrite_changed p c v s (by rw [(canonicalScalarDecode_sound c _ v hd).2]; exact changed)

theorem scalar_read_available {D : Source.Layout} {L : Source.SPath → Source.STy}
    (p : Source.SPath) (v : Source.Val D (L p)) (h : Source.Val.default D (L p) = some v)
    (s : Source.Storage D L) : ∃ w, s.read p = some w := by
  cases he : s.cell p with
  | none => exact ⟨v, by simp only [Source.Storage.read, he, h]⟩
  | some w => exact ⟨w, by simp only [Source.Storage.read, he]⟩

/-- A derived singleton instance, not an assumed whole-store physical agreement. -/
def singletonScalarObligations {D : Source.Layout} {L : Source.SPath → Source.STy} {f : Field}
    (p : Source.SPath) (c : ScalarCodec D (L p) f) (width : StorageWidth D (L p) f.width)
    (H : Storage.Pre → Nat) (loc : Storage.Loc)
    (default : Source.Val D (L p)) (hd : Source.Val.default D (L p) = some default) :
    ScalarStorageObligations D L Unit where
  path _ := p
  hash := H
  location _ := loc
  field _ := f
  width_agrees _ := width
  codec _ := c
  view := scalarPathView p c (physicalSlot H loc)
  realize s := by
    obtain ⟨v, hr⟩ := scalar_read_available p default hd s
    exact ⟨patchScalarSlot (fun _ => 0) (physicalSlot H loc) f (c.encode v), by
      simp only [scalarPathView, hr, Option.map_some, patchScalarSlot_find]⟩
  read_agrees s m _ v hv hr := by
    change (s.read p).map c.encode = some _ at hv
    rw [hr] at hv
    exact congrArg Fin.val (Option.some.inj hv).symm
  writeback := canonicalPathWriteback p c (physicalSlot H loc)
  unchanged := fun s m h => canonicalPathWriteback_unchanged p c _ s m h
  result_view := fun s m s' e => canonicalPathWriteback_result_view p c _ s s' m e

theorem source_scalar_writes_commute {D : Source.Layout} {L : Source.SPath → Source.STy}
    (s : Source.Storage D L) (p q : Source.SPath) (vp : Source.Val D (L p)) (vq : Source.Val D (L q))
    (h : p ≠ q) : (s.write p vp).write q vq = (s.write q vq).write p vp := by
  apply congrArg Source.Storage.mk
  funext r
  by_cases hp : r = p
  · subst r
    simp only [Source.Storage.set, Source.Storage.write, dif_pos, dif_neg h]
  · by_cases hq : r = q
    · subst r
      simp only [Source.Storage.set, Source.Storage.write, dif_pos, dif_neg (Ne.symm h)]
    · simp only [Source.Storage.set, Source.Storage.write, dif_neg hp, dif_neg hq]

theorem preserveScalarWrite_commute {D : Source.Layout} {L : Source.SPath → Source.STy} {f g : Field}
    (p q : Source.SPath) (c : ScalarCodec D (L p) f) (d : ScalarCodec D (L q) g)
    (vp : Source.Val D (L p)) (vq : Source.Val D (L q)) (s : Source.Storage D L) (h : p ≠ q) :
    preserveScalarWrite p c vp (preserveScalarWrite q d vq s) =
      preserveScalarWrite q d vq (preserveScalarWrite p c vp s) := by
  change (if ((preserveScalarWrite q d vq s).read p).map c.encode = some (c.encode vp)
      then preserveScalarWrite q d vq s else (preserveScalarWrite q d vq s).write p vp) =
    (if ((preserveScalarWrite p c vp s).read q).map d.encode = some (d.encode vq)
      then preserveScalarWrite p c vp s else (preserveScalarWrite p c vp s).write q vq)
  rw [preserveScalarWrite_other_read q p d vq s h,
    preserveScalarWrite_other_read p q c vp s (Ne.symm h)]
  by_cases hp : (s.read p).map c.encode = some (c.encode vp)
  · by_cases hq : (s.read q).map d.encode = some (d.encode vq)
    · simp only [preserveScalarWrite, if_pos hp, if_pos hq]
    · simp only [preserveScalarWrite, if_pos hp, if_neg hq]
  · by_cases hq : (s.read q).map d.encode = some (d.encode vq)
    · simp only [preserveScalarWrite, if_neg hp, if_pos hq]
    · simp only [preserveScalarWrite, if_neg hp, if_neg hq]
      exact (source_scalar_writes_commute s p q vp vq h).symm

theorem patchScalarSlot_other_field (m : SlotView) (s t : Roadmap.Word) (f g : Field) (v : f.Value)
    (h : s ≠ t ∨ f.offset + f.width ≤ g.offset ∨ g.offset + g.width ≤ f.offset) :
    g.findWord (patchScalarSlot m s f v t) = g.findWord (m t) := by
  rcases h with h | h
  · rw [patchScalarSlot, find_saveSlot_other m s t _ (Ne.symm h)]
  · by_cases hs : t = s
    · subst t
      rw [patchScalarSlot, find_saveSlot]
      apply Fin.ext
      exact f.find_save_disjoint g (m s).val v h
    · rw [patchScalarSlot, find_saveSlot_other m s t _ hs]

theorem Field.lowByte_other (f : Field) (w : Roadmap.Word) (v : f.Value) (i : Fin 32)
    (h : i.val < f.offset ∨ f.offset + f.width ≤ i.val) :
    wordByte (f.saveWord w v) (reverseByteIndex 32 i) = wordByte w (reverseByteIndex 32 i) := by
  let g : Field := ⟨i.val, 1, by decide, by have hi := i.isLt; omega⟩
  have hg : f.offset + f.width ≤ g.offset ∨ g.offset + g.width ≤ f.offset := by
    change f.offset + f.width ≤ i.val ∨ i.val + 1 ≤ f.offset
    omega
  have obs := f.find_save_disjoint g w.val v hg
  have hi : 31 - (31 - i.val) = i.val := by have ht := i.isLt; omega
  apply UInt8.toNat_inj.mp
  simp only [wordByte, reverseByteIndex, hi, UInt8.toNat_ofNat']
  exact obs

/-- Byte coordinates are low-end within each slot; unowned bits are not erased. -/
def scalarByteUnowned (slot : Roadmap.Word) (f : Field) (a : Nat) : Prop :=
  a / 32 ≠ slot.val ∨ a % 32 < f.offset ∨ f.offset + f.width ≤ a % 32

theorem patchScalarSlot_unowned_byte (m : SlotView) (slot : Roadmap.Word) (f : Field) (v : f.Value)
    (a : Nat) (bound : a < (2 ^ 256) * 32) (h : scalarByteUnowned slot f a) :
    slotBytes (patchScalarSlot m slot f v) a = slotBytes m a := by
  have hq : a / 32 < 2 ^ 256 := by omega
  unfold slotBytes
  rcases h with h | h
  · have hn : (⟨(a / 32) % (2 ^ 256), Nat.mod_lt _ (by decide)⟩ : Roadmap.Word) ≠ slot := by
      intro he
      have hv := congrArg Fin.val he
      change (a / 32) % (2 ^ 256) = slot.val at hv
      rw [Nat.mod_eq_of_lt hq] at hv
      exact h hv
    rw [patchScalarSlot, find_saveSlot_other _ _ _ _ hn]
  · by_cases hs : a / 32 = slot.val
    · have he : (⟨(a / 32) % (2 ^ 256), Nat.mod_lt _ (by decide)⟩ : Roadmap.Word) = slot := by
        apply Fin.ext
        change (a / 32) % (2 ^ 256) = slot.val
        rw [Nat.mod_eq_of_lt hq, hs]
      rw [he, patchScalarSlot, find_saveSlot]
      exact f.lowByte_other (m slot) v ⟨a % 32, Nat.mod_lt _ (by decide)⟩ h
    · have hn : (⟨(a / 32) % (2 ^ 256), Nat.mod_lt _ (by decide)⟩ : Roadmap.Word) ≠ slot := by
        intro he
        have hv := congrArg Fin.val he
        change (a / 32) % (2 ^ 256) = slot.val at hv
        rw [Nat.mod_eq_of_lt hq] at hv
        exact hs hv
      rw [patchScalarSlot, find_saveSlot_other _ _ _ _ hn]

theorem encodeScalarPath_residual {D : Source.Layout} {L : Source.SPath → Source.STy} {f : Field}
    (p : Source.SPath) (c : ScalarCodec D (L p) f) (slot : Roadmap.Word)
    (s : Source.Storage D L) (residual out : SlotView) (e : encodeScalarPath p c slot s residual = some out)
    (a : Nat) (bound : a < (2 ^ 256) * 32) (h : scalarByteUnowned slot f a) :
    slotBytes out a = slotBytes residual a := by
  obtain ⟨v, _, he⟩ := Option.map_eq_some_iff.mp e
  subst out
  exact patchScalarSlot_unowned_byte residual slot f (c.encode v) a bound h

theorem encodeScalarPath_unchanged {D : Source.Layout} {L : Source.SPath → Source.STy} {f : Field}
    (p : Source.SPath) (c : ScalarCodec D (L p) f) (slot : Roadmap.Word)
    (s : Source.Storage D L) (m : SlotView) (h : scalarPathView p c slot s m) :
    encodeScalarPath p c slot s m = some m := by
  obtain ⟨v, hr, he⟩ := Option.map_eq_some_iff.mp h
  simp only [encodeScalarPath, hr, Option.map_some]
  apply congrArg some
  unfold patchScalarSlot
  rw [he, Field.saveWord_unchanged, saveSlot_unchanged]

end Solidity.Yul.Views
