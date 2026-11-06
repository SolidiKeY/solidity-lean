import Solidity.Yul.Views.ScalarWorld

/-! Constructive finite canonical path collections over actual Source.Storage.
Every entry carries an actual path-indexed codec and bounded physical field/slot.
Separation/default availability are real inputs; no aggregate inverse or view laws are fields.
A finite collection is not a whole-store layout or dirty-bit semantics. None is
unsupported canonical preparation, not an assembly refusal/no-op. -/
namespace Solidity.Yul.Views

structure ScalarPath (D : Source.Layout) (L : Source.SPath → Source.STy) where
  path : Source.SPath
  slot : Roadmap.Word
  field : Field
  codec : ScalarCodec D (L path) field
  width : StorageWidth D (L path) field.width

def pathsApart {D L} (c d : ScalarPath D L) : Prop :=
  c.slot ≠ d.slot ∨ c.field.offset + c.field.width ≤ d.field.offset ∨
    d.field.offset + d.field.width ≤ c.field.offset

theorem pathsApart_symm {D L} {c d : ScalarPath D L} (h : pathsApart c d) : pathsApart d c := by
  rcases h with h | h | h
  · exact Or.inl (Ne.symm h)
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

def finiteSeparated {D L} (cs : List (ScalarPath D L)) : Prop :=
  cs.Pairwise (fun c d => c.path ≠ d.path ∧ pathsApart c d)

def finiteView {D L} (cs : List (ScalarPath D L)) (s : Source.Storage D L) (m : SlotView) : Prop :=
  ∀ c ∈ cs, scalarPathView c.path c.codec c.slot s m

def finiteEncode {D L} : List (ScalarPath D L) → Source.Storage D L → SlotView → Option SlotView
  | [], _, m => some m
  | c :: cs, s, m => (encodeScalarPath c.path c.codec c.slot s m).bind (finiteEncode cs s)

def finiteWriteback {D L} : List (ScalarPath D L) → SlotView → Source.Storage D L → Option (Source.Storage D L)
  | [], _, s => some s
  | c :: cs, m, s => (canonicalPathWriteback c.path c.codec c.slot m s).bind (finiteWriteback cs m)

theorem finiteWriteback_other {D L} (cs : List (ScalarPath D L)) (m : SlotView)
    (s out : Source.Storage D L) (e : finiteWriteback cs m s = some out)
    (q : Source.SPath) (h : ∀ c ∈ cs, q ≠ c.path) : out.cell q = s.cell q := by
  induction cs generalizing s with
  | nil => exact congrArg (fun x => x.cell q) (Option.some.inj e).symm
  | cons c cs ih =>
    obtain ⟨mid, hc, ht⟩ := Option.bind_eq_some_iff.mp e
    rw [ih mid ht (fun d hd => h d (List.mem_cons_of_mem c hd))]
    exact canonicalPathWriteback_cell_other c.path q c.codec c.slot s mid m hc (h c List.mem_cons_self)

theorem finiteWriteback_other_read {D L} (cs : List (ScalarPath D L)) (m : SlotView)
    (s out : Source.Storage D L) (e : finiteWriteback cs m s = some out)
    (q : Source.SPath) (h : ∀ c ∈ cs, q ≠ c.path) : out.read q = s.read q := by
  unfold Source.Storage.read
  rw [finiteWriteback_other cs m s out e q h]

theorem finiteWriteback_unchanged {D L} (cs : List (ScalarPath D L)) (m : SlotView)
    (s : Source.Storage D L) (h : finiteView cs s m) : finiteWriteback cs m s = some s := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [finiteWriteback, canonicalPathWriteback_unchanged c.path c.codec c.slot s m (h c List.mem_cons_self)]
    exact ih (fun d hd => h d (List.mem_cons_of_mem c hd))

theorem finiteWriteback_result_view {D L} (cs : List (ScalarPath D L)) (m : SlotView)
    (s out : Source.Storage D L) (sep : finiteSeparated cs)
    (e : finiteWriteback cs m s = some out) : finiteView cs out m := by
  induction cs generalizing s with
  | nil => intro c hc; cases hc
  | cons c cs ih =>
    obtain ⟨head, tail⟩ := List.pairwise_cons.mp sep
    obtain ⟨mid, hc, ht⟩ := Option.bind_eq_some_iff.mp e
    intro d hd
    rcases List.mem_cons.mp hd with he | he
    · subst d
      unfold scalarPathView
      rw [finiteWriteback_other_read cs m mid out ht c.path (fun x hx => (head x hx).1)]
      exact canonicalPathWriteback_result_view c.path c.codec c.slot s mid m hc
    · exact ih mid tail ht d he

theorem finiteEncode_other_field {D L} (cs : List (ScalarPath D L)) (s : Source.Storage D L)
    (m out : SlotView) (e : finiteEncode cs s m = some out) (d : ScalarPath D L)
    (sep : ∀ c ∈ cs, pathsApart c d) : d.field.findWord (out d.slot) = d.field.findWord (m d.slot) := by
  induction cs generalizing m with
  | nil => exact congrArg (fun x => d.field.findWord (x d.slot)) (Option.some.inj e).symm
  | cons c cs ih =>
    obtain ⟨mid, hc, ht⟩ := Option.bind_eq_some_iff.mp e
    rw [ih mid ht (fun x hx => sep x (List.mem_cons_of_mem c hx))]
    obtain ⟨v, hr, he⟩ := Option.map_eq_some_iff.mp hc
    subst mid
    exact patchScalarSlot_other_field m c.slot d.slot c.field d.field (c.codec.encode v) (sep c List.mem_cons_self)

theorem finiteEncode_view {D L} (cs : List (ScalarPath D L)) (s : Source.Storage D L)
    (m out : SlotView) (sep : finiteSeparated cs) (e : finiteEncode cs s m = some out) : finiteView cs s out := by
  induction cs generalizing m with
  | nil => intro c hc; cases hc
  | cons c cs ih =>
    obtain ⟨head, tail⟩ := List.pairwise_cons.mp sep
    obtain ⟨mid, hc, ht⟩ := Option.bind_eq_some_iff.mp e
    intro d hd
    rcases List.mem_cons.mp hd with he | he
    · subst d
      have h := finiteEncode_other_field cs s mid out ht c (fun x hx => pathsApart_symm (head x hx).2)
      unfold scalarPathView
      rw [h]
      exact encodeScalarPath_view c.path c.codec c.slot s m mid hc
    · exact ih mid tail ht d he

theorem finiteEncode_unchanged {D L} (cs : List (ScalarPath D L)) (s : Source.Storage D L)
    (m : SlotView) (h : finiteView cs s m) : finiteEncode cs s m = some m := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [finiteEncode, encodeScalarPath_unchanged c.path c.codec c.slot s m (h c List.mem_cons_self)]
    exact ih (fun d hd => h d (List.mem_cons_of_mem c hd))

theorem finiteEncode_residual {D L} (cs : List (ScalarPath D L)) (s : Source.Storage D L)
    (m out : SlotView) (e : finiteEncode cs s m = some out) (a : Nat)
    (bound : a < (2 ^ 256) * 32) (unowned : ∀ c ∈ cs, scalarByteUnowned c.slot c.field a) :
    slotBytes out a = slotBytes m a := by
  induction cs generalizing m with
  | nil => exact congrArg (fun x => slotBytes x a) (Option.some.inj e).symm
  | cons c cs ih =>
    obtain ⟨mid, hc, ht⟩ := Option.bind_eq_some_iff.mp e
    rw [ih mid ht (fun d hd => unowned d (List.mem_cons_of_mem c hd))]
    exact encodeScalarPath_residual c.path c.codec c.slot s m mid hc a bound (unowned c List.mem_cons_self)

theorem finiteEncode_exists {D L} (cs : List (ScalarPath D L)) (s : Source.Storage D L)
    (m : SlotView) (available : ∀ c ∈ cs, ∃ v, s.read c.path = some v) : ∃ out, finiteEncode cs s m = some out := by
  induction cs generalizing m with
  | nil => exact ⟨m, rfl⟩
  | cons c cs ih =>
    obtain ⟨v, hr⟩ := available c List.mem_cons_self
    obtain ⟨out, ht⟩ := ih (patchScalarSlot m c.slot c.field (c.codec.encode v))
      (fun d hd => available d (List.mem_cons_of_mem c hd))
    exact ⟨out, by simp only [finiteEncode, encodeScalarPath, hr, Option.map_some, Option.bind_some, ht]⟩

theorem finiteWriteback_encode {D L} (cs : List (ScalarPath D L)) (s : Source.Storage D L)
    (m out : SlotView) (sep : finiteSeparated cs) (e : finiteEncode cs s m = some out) :
    finiteWriteback cs out s = some s :=
  finiteWriteback_unchanged cs out s (finiteEncode_view cs s m out sep e)

theorem finiteWriteback_idempotent {D L} (cs : List (ScalarPath D L)) (m : SlotView)
    (s out : Source.Storage D L) (sep : finiteSeparated cs) (e : finiteWriteback cs m s = some out) :
    finiteWriteback cs m out = some out :=
  finiteWriteback_unchanged cs m out (finiteWriteback_result_view cs m s out sep e)

theorem finiteEncode_after_writeback {D L} (cs : List (ScalarPath D L)) (m : SlotView)
    (s out : Source.Storage D L) (sep : finiteSeparated cs) (e : finiteWriteback cs m s = some out) :
    finiteEncode cs out m = some m :=
  finiteEncode_unchanged cs out m (finiteWriteback_result_view cs m s out sep e)

/-- Derived finite instance. Locations and defaults are actual layout/type inputs,
not inverse/adequacy assumptions. The caller's residual map is used in realization. -/
def finiteScalarObligations {D L} (cs : List (ScalarPath D L)) (sep : finiteSeparated cs)
    (H : Storage.Pre → Nat) (loc : {c // c ∈ cs} → Storage.Loc)
    (slots : ∀ c, c.val.slot = physicalSlot H (loc c))
    (defaults : ∀ c ∈ cs, ∃ v, Source.Val.default D (L c.path) = some v) (residual : SlotView) :
    ScalarStorageObligations D L {c // c ∈ cs} where
  path c := c.val.path
  hash := H
  location := loc
  field c := c.val.field
  width_agrees c := c.val.width
  codec c := c.val.codec
  view := finiteView cs
  realize s := by
    have available : ∀ c ∈ cs, ∃ v, s.read c.path = some v := by
      intro c hc
      obtain ⟨v, hv⟩ := defaults c hc
      exact scalar_read_available c.path v hv s
    obtain ⟨out, he⟩ := finiteEncode_exists cs s residual available
    exact ⟨out, finiteEncode_view cs s residual out sep he⟩
  read_agrees s m c v hv hr := by
    have h := hv c.val c.property
    change (s.read c.val.path).map c.val.codec.encode = some _ at h
    rw [hr] at h
    rw [← slots c]
    exact congrArg Fin.val (Option.some.inj h).symm
  writeback := finiteWriteback cs
  unchanged s m h := finiteWriteback_unchanged cs m s h
  result_view s m out e := finiteWriteback_result_view cs m s out sep e

theorem canonicalWrites_commute {D L} (c d : ScalarPath D L) (m : SlotView)
    (s : Source.Storage D L) (h : c.path ≠ d.path) :
    (canonicalPathWriteback c.path c.codec c.slot m s).bind
      (canonicalPathWriteback d.path d.codec d.slot m) =
    (canonicalPathWriteback d.path d.codec d.slot m s).bind
      (canonicalPathWriteback c.path c.codec c.slot m) := by
  unfold canonicalPathWriteback
  cases hc : canonicalScalarDecode c.codec (c.field.findWord (m c.slot)) with
  | none =>
    cases canonicalScalarDecode d.codec (d.field.findWord (m d.slot)) <;> rfl
  | some v =>
    cases hd : canonicalScalarDecode d.codec (d.field.findWord (m d.slot)) with
    | none => simp only [Option.map_none, Option.bind_none, Option.map_some, Option.bind_some]
    | some w =>
      simp only [Option.map_some, Option.bind_some]
      exact congrArg some (preserveScalarWrite_commute d.path c.path d.codec c.codec w v s (Ne.symm h))

theorem finiteSeparated_perm {D L} {cs ds : List (ScalarPath D L)} (p : cs.Perm ds)
    (h : finiteSeparated cs) : finiteSeparated ds :=
  h.perm p (fun h => ⟨Ne.symm h.1, pathsApart_symm h.2⟩)

theorem finiteWriteback_perm {D L} {cs ds : List (ScalarPath D L)} (p : cs.Perm ds)
    (m : SlotView) (s : Source.Storage D L) (h : finiteSeparated cs) :
    finiteWriteback cs m s = finiteWriteback ds m s := by
  induction p generalizing s with
  | nil => rfl
  | cons c p ih =>
    unfold finiteWriteback
    apply Option.bind_congr
    intro mid hm
    exact ih mid (List.pairwise_cons.mp h).2
  | swap c d cs =>
    have hd : d.path ≠ c.path := ((List.pairwise_cons.mp h).1 c List.mem_cons_self).1
    simp only [finiteWriteback, ← Option.bind_assoc]
    rw [canonicalWrites_commute d c m s hd]
  | trans p q ihp ihq => exact (ihp s h).trans (ihq s (finiteSeparated_perm p h))

theorem finiteWriteback_reverse {D L} (cs : List (ScalarPath D L)) (m : SlotView)
    (s : Source.Storage D L) (h : finiteSeparated cs) :
    finiteWriteback cs.reverse m s = finiteWriteback cs m s :=
  (finiteWriteback_perm (List.reverse_perm cs).symm m s h).symm

/-- Validate every canonical payload before producing a typed store transformer. -/
def finitePrepare {D L} : List (ScalarPath D L) → SlotView → Option (Source.Storage D L → Source.Storage D L)
  | [], _ => some id
  | c :: cs, m => (canonicalScalarDecode c.codec (c.field.findWord (m c.slot))).bind
      (fun v => (finitePrepare cs m).map (fun tail s => tail (preserveScalarWrite c.path c.codec v s)))

theorem finiteWriteback_prepare {D L} (cs : List (ScalarPath D L)) (m : SlotView)
    (s : Source.Storage D L) : finiteWriteback cs m s = (finitePrepare cs m).map (fun f => f s) := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    cases hd : canonicalScalarDecode c.codec (c.field.findWord (m c.slot)) with
    | none => simp only [finiteWriteback, canonicalPathWriteback, finitePrepare, hd, Option.map_none, Option.bind_none]
    | some v =>
      simp only [finiteWriteback, canonicalPathWriteback, finitePrepare, hd, Option.map_some, Option.bind_some, ih,
        Option.map_map, Function.comp_def]

theorem finiteView_decode {D L} (cs : List (ScalarPath D L)) (s : Source.Storage D L)
    (m : SlotView) (h : finiteView cs s m) (c : ScalarPath D L) (hc : c ∈ cs) :
    canonicalScalarDecode c.codec (c.field.findWord (m c.slot)) = s.read c.path := by
  obtain ⟨v, hr, he⟩ := Option.map_eq_some_iff.mp (h c hc)
  rw [← he, canonicalScalarDecode_encode, hr]

theorem finitePrepare_invalid_member {D L} (cs : List (ScalarPath D L)) (m : SlotView)
    (c : ScalarPath D L) (hc : c ∈ cs)
    (bad : canonicalScalarDecode c.codec (c.field.findWord (m c.slot)) = none) : finitePrepare cs m = none := by
  induction cs with
  | nil => cases hc
  | cons d ds ih =>
    rcases List.mem_cons.mp hc with he | ht
    · subst d
      simp only [finitePrepare, bad, Option.bind_none]
    · rw [finitePrepare, ih ht]
      cases canonicalScalarDecode d.codec (d.field.findWord (m d.slot)) <;> rfl

theorem finiteWriteback_invalid_member {D L} (cs : List (ScalarPath D L)) (m : SlotView)
    (s : Source.Storage D L) (c : ScalarPath D L) (hc : c ∈ cs)
    (bad : canonicalScalarDecode c.codec (c.field.findWord (m c.slot)) = none) : finiteWriteback cs m s = none := by
  rw [finiteWriteback_prepare, finitePrepare_invalid_member cs m c hc bad]
  rfl

end Solidity.Yul.Views
