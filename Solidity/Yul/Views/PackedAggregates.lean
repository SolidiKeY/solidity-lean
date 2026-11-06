import Solidity.Yul.Views.ScalarBytes

/-!
# Constructive flat fixed-size storage aggregate components

Coordinates count bytes from the low end of each storage slot, not memory
addresses. Scalar fields pack until the next one would cross a 32-byte slot.
Arrays/structs begin at a slot boundary; their successors begin after rounding
up the component end. Supported members are actual Source.Data.val values.
Nested aggregates, references, dynamic/mapping regions and dirty owned bytes
are not represented by these canonical components. No Source state is added.
-/
namespace Solidity.Yul.Views

def reverseByteIndex (n : Nat) (i : Fin n) : Fin n := ⟨n - 1 - i.val, by have := i.isLt; omega⟩

theorem reverseByteIndex_twice (n : Nat) (i : Fin n) :
    reverseByteIndex n (reverseByteIndex n i) = i := by
  apply Fin.ext
  have := i.isLt
  simp only [reverseByteIndex]
  omega

def ByteCodec.littleEndian {D : Source.Layout} {τ : Source.STy} {n : Nat}
    (c : ByteCodec D τ n) : ByteCodec D τ n where
  encode v i := c.encode v (reverseByteIndex n i)
  decode bs := c.decode (fun i => bs (reverseByteIndex n i))
  decode_encode v := by
    simp only [reverseByteIndex_twice]
    exact c.decode_encode v

def patchBytes (m : ByteView) (base n : Nat) (bs : Fin n → UInt8) : ByteView :=
  fun a => if h : base ≤ a ∧ a < base + n then bs ⟨a - base, by omega⟩ else m a

theorem patchBytes_at (m : ByteView) (base n : Nat) (bs : Fin n → UInt8) (i : Fin n) :
    patchBytes m base n bs (base + i.val) = bs i := by
  simp only [patchBytes, Nat.le_add_right, Nat.add_lt_add_iff_left, i.isLt, and_self,
    ↓reduceDIte, Nat.add_sub_cancel_left]

theorem patchBytes_outside (m : ByteView) (base n : Nat) (bs : Fin n → UInt8)
    (a : Nat) (h : ¬ (base ≤ a ∧ a < base + n)) : patchBytes m base n bs a = m a := by
  simp only [patchBytes, dif_neg h]

theorem patchBytes_unchanged (m : ByteView) (base n : Nat) (bs : Fin n → UInt8)
    (h : ∀ i : Fin n, bs i = m (base + i.val)) : patchBytes m base n bs = m := by
  funext a
  unfold patchBytes
  split
  · rename_i ha
    rw [h, Nat.add_sub_of_le ha.1]
  · rfl

/-- First fitting low-byte position, including the mandatory inter-slot gap. -/
def packedStart (cursor width : Nat) : Nat :=
  if cursor % 32 + width ≤ 32 then cursor else cursor + (32 - cursor % 32)

theorem packedStart_spec (cursor : Nat) (f : Field) :
    cursor ≤ packedStart cursor f.width ∧ packedStart cursor f.width % 32 + f.width ≤ 32 := by
  have hw := f.fits
  have hr := Nat.mod_lt cursor (by decide : 0 < 32)
  unfold packedStart
  split
  · rename_i h
    exact ⟨Nat.le_refl cursor, h⟩
  · have he : cursor + (32 - cursor % 32) = (cursor / 32 + 1) * 32 := by
      have := Nat.mod_add_div cursor 32
      omega
    rw [he]
    omega

/-- Each supplied scalar codec has its documented source byte width. -/
inductive PackedMembers (D : Source.Layout) : List Source.STy → Type where
  | nil : PackedMembers D []
  | cons {τ τs} (f : Field) (width : StorageWidth D τ f.width)
      (codec : ScalarCodec D τ f) (rest : PackedMembers D τs) : PackedMembers D (τ :: τs)

def PackedMembers.endByte {D : Source.Layout} {τs : List Source.STy}
    (cs : PackedMembers D τs) (cursor : Nat) : Nat :=
  by
    cases cs with
    | nil => exact cursor
    | cons f _ _ rest => exact rest.endByte (packedStart cursor f.width + f.width)

/-- Byte addresses owned by members; padding is deliberately outside this set. -/
def PackedMembers.owns {D : Source.Layout} {τs : List Source.STy}
    (cs : PackedMembers D τs) (cursor a : Nat) : Prop :=
  by
    cases cs with
    | nil => exact False
    | cons f _ _ rest => exact
        ((packedStart cursor f.width ≤ a ∧ a < packedStart cursor f.width + f.width) ∨
          rest.owns (packedStart cursor f.width + f.width) a)

/-- A raw view is patched only after an actual scalar Data constructor is found. -/
def PackedMembers.encode {D : Source.Layout} {τs : List Source.STy}
    (cs : PackedMembers D τs) (ds : Source.DataList D τs) (cursor : Nat) (m : ByteView) : Option ByteView :=
  by
    cases cs with
    | nil => cases ds; exact some m
    | cons f _ c rest =>
      cases ds with
      | cons d tail =>
        cases d with
        | val v => exact (rest.encode tail (packedStart cursor f.width + f.width)
            (patchBytes m (packedStart cursor f.width) f.width (c.bytesBE.littleEndian.encode v)))
        | _ => exact none

def PackedMembers.decode {D : Source.Layout} {τs : List Source.STy}
    (cs : PackedMembers D τs) (cursor : Nat) (m : ByteView) : Option (Source.DataList D τs) :=
  by
    cases cs with
    | nil => exact some .nil
    | cons f _ c rest => exact do
      let v ← c.bytesBE.littleEndian.decode (fun i => m (packedStart cursor f.width + i.val))
      let tail ← rest.decode (packedStart cursor f.width + f.width) m
      pure (.cons (.val v) tail)

theorem PackedMembers.end_mono {D : Source.Layout} {τs : List Source.STy}
    (cs : PackedMembers D τs) (cursor : Nat) : cursor ≤ cs.endByte cursor := by
  induction cs generalizing cursor with
  | nil => exact Nat.le_refl cursor
  | cons f w c rest ih =>
    have hs := (packedStart_spec cursor f).1
    exact Nat.le_trans (by omega) (ih _)

theorem PackedMembers.encode_before {D : Source.Layout} {τs : List Source.STy}
    (cs : PackedMembers D τs) (ds : Source.DataList D τs) (cursor : Nat) (m out : ByteView)
    (e : cs.encode ds cursor m = some out) (a : Nat) (before : a < cursor) : out a = m a := by
  induction cs generalizing cursor m out with
  | nil => cases ds; cases e; rfl
  | cons f w c rest ih =>
    cases ds with
    | cons d tail =>
      cases d with
      | val v =>
        have hs := (packedStart_spec cursor f).1
        rw [ih tail _ _ out e (by omega)]
        exact patchBytes_outside _ _ _ _ a (by omega)
      | _ => cases e

/-- All unowned bytes, including intra-slot/trailing padding, survive exactly. -/
theorem PackedMembers.encode_residual {D : Source.Layout} {τs : List Source.STy}
    (cs : PackedMembers D τs) (ds : Source.DataList D τs) (cursor : Nat) (m out : ByteView)
    (e : cs.encode ds cursor m = some out) (a : Nat) (h : ¬ cs.owns cursor a) : out a = m a := by
  induction cs generalizing cursor m out with
  | nil => cases ds; cases e; rfl
  | cons f w c rest ih =>
    cases ds with
    | cons d tail =>
      cases d with
      | val v =>
        change ¬ (_ ∨ _) at h
        rw [ih tail _ _ out e (fun ht => h (Or.inr ht))]
        exact patchBytes_outside _ _ _ _ a (fun hh => h (Or.inl hh))
      | _ => cases e

/-- A successful constructive aggregate encoding decodes to actual DataList. -/
theorem PackedMembers.decode_encode {D : Source.Layout} {τs : List Source.STy}
    (cs : PackedMembers D τs) (ds : Source.DataList D τs) (cursor : Nat) (m out : ByteView)
    (e : cs.encode ds cursor m = some out) : cs.decode cursor out = some ds := by
  induction cs generalizing cursor m out with
  | nil => cases ds; rfl
  | cons f w c rest ih =>
    cases ds with
    | cons d tail =>
      cases d with
      | val v =>
        have bytes : (fun i : Fin f.width => out (packedStart cursor f.width + i.val)) =
            c.bytesBE.littleEndian.encode v := by
          funext i
          rw [rest.encode_before tail _ _ out e _ (by have := i.isLt; omega)]
          exact patchBytes_at _ _ _ _ i
        change (do
          let vv ← c.bytesBE.littleEndian.decode (fun i => out (packedStart cursor f.width + i.val))
          let tt ← rest.decode (packedStart cursor f.width + f.width) out
          pure (Source.DataList.cons (.val vv) tt)) = _
        rw [bytes, ByteCodec.decode_encode]
        rw [ih tail _ _ out e]
        rfl
      | _ => cases e

/-- Supported members are actual scalar Data constructors, not a second value list. -/
inductive ScalarMembers {D : Source.Layout} : {τs : List Source.STy} → Source.DataList D τs → Prop where
  | nil : ScalarMembers .nil
  | cons {τ τs} (v : Source.Val D τ) (ds : Source.DataList D τs)
      (rest : ScalarMembers ds) : ScalarMembers (.cons (.val v) ds)

theorem PackedMembers.encode_exists {D : Source.Layout} {τs : List Source.STy}
    (cs : PackedMembers D τs) (ds : Source.DataList D τs) (h : ScalarMembers ds)
    (cursor : Nat) (m : ByteView) : ∃ out, cs.encode ds cursor m = some out := by
  induction cs generalizing cursor m with
  | nil => cases h; exact ⟨m, rfl⟩
  | cons f w c rest ih =>
    cases h with
    | cons v tail ht => exact ih tail ht _ _

/-- Canonical owned bytes only; all gaps and trailing padding remain unrestricted. -/
def PackedMembers.matches {D : Source.Layout} {τs : List Source.STy}
    (cs : PackedMembers D τs) (ds : Source.DataList D τs) (cursor : Nat) (m : ByteView) : Prop :=
  by
    cases cs with
    | nil => cases ds; exact True
    | cons f _ c rest =>
      cases ds with
      | cons d tail =>
        cases d with
        | val v => exact
            ((∀ i : Fin f.width, c.bytesBE.littleEndian.encode v i = m (packedStart cursor f.width + i.val)) ∧
              rest.matches tail (packedStart cursor f.width + f.width) m)
        | _ => exact False

theorem PackedMembers.encode_unchanged {D : Source.Layout} {τs : List Source.STy}
    (cs : PackedMembers D τs) (ds : Source.DataList D τs) (cursor : Nat) (m : ByteView)
    (h : cs.matches ds cursor m) : cs.encode ds cursor m = some m := by
  induction cs generalizing cursor m with
  | nil => cases ds; rfl
  | cons f w c rest ih =>
    cases ds with
    | cons d tail =>
      cases d with
      | val v =>
        change _ ∧ _ at h
        change rest.encode tail _ (patchBytes m _ _ _) = some m
        rw [patchBytes_unchanged _ _ _ _ h.1]
        exact ih tail _ m h.2
      | _ => cases h

theorem PackedMembers.encode_matches {D : Source.Layout} {τs : List Source.STy}
    (cs : PackedMembers D τs) (ds : Source.DataList D τs) (cursor : Nat) (m out : ByteView)
    (e : cs.encode ds cursor m = some out) : cs.matches ds cursor out := by
  induction cs generalizing cursor m out with
  | nil => cases ds; trivial
  | cons f w c rest ih =>
    cases ds with
    | cons d tail =>
      cases d with
      | val v =>
        constructor
        · intro i
          rw [rest.encode_before tail _ _ out e _ (by have := i.isLt; omega)]
          exact (patchBytes_at _ _ _ _ i).symm
        · exact ih tail _ _ out e
      | _ => cases e

/-- Exact unchanged re-encoding is constructive for every successful encoding. -/
theorem PackedMembers.encode_idempotent {D : Source.Layout} {τs : List Source.STy}
    (cs : PackedMembers D τs) (ds : Source.DataList D τs) (cursor : Nat) (m out : ByteView)
    (e : cs.encode ds cursor m = some out) : cs.encode ds cursor out = some out :=
  cs.encode_unchanged ds cursor out (cs.encode_matches ds cursor m out e)

theorem PackedMembers.owned_bounds {D : Source.Layout} {τs : List Source.STy}
    (cs : PackedMembers D τs) (cursor a : Nat) (h : cs.owns cursor a) :
    cursor ≤ a ∧ a < cs.endByte cursor := by
  induction cs generalizing cursor with
  | nil => cases h
  | cons f w c rest ih =>
    have hs := (packedStart_spec cursor f).1
    change cursor ≤ a ∧ a < rest.endByte (packedStart cursor f.width + f.width)
    cases h with
    | inl hh => have he := rest.end_mono (packedStart cursor f.width + f.width); exact ⟨by omega, by omega⟩
    | inr hh => have ht := ih _ hh; exact ⟨by omega, ht.2⟩

/-- A component starts at a real storage slot and fits without word-address wrap. -/
def PackedMembers.Fits {D : Source.Layout} {τs : List Source.STy}
    (cs : PackedMembers D τs) (base : Roadmap.Word) : Prop :=
  cs.endByte (base.val * 32) ≤ (2 ^ 256) * 32

/-- Slot after an aggregate, preserving its mandatory trailing slot boundary. -/
def PackedMembers.nextSlot {D : Source.Layout} {τs : List Source.STy}
    (cs : PackedMembers D τs) (base : Roadmap.Word) : Nat :=
  (cs.endByte (base.val * 32) + 31) / 32

def decodePackedStruct {D : Source.Layout} (d : Source.DeclName)
    (cs : PackedMembers D (D.fields d)) (base : Roadmap.Word) (_ : cs.Fits base) (m : ByteView) :
    Option (Source.Data D (.struct .storage d)) :=
  (cs.decode (base.val * 32) m).map Source.Data.struct

theorem packedStruct_roundtrip {D : Source.Layout} (d : Source.DeclName)
    (cs : PackedMembers D (D.fields d)) (base : Roadmap.Word) (fits : cs.Fits base)
    (ds : Source.DataList D (D.fields d)) (h : ScalarMembers ds) (m : ByteView) :
    ∃ out, cs.encode ds (base.val * 32) m = some out ∧
      decodePackedStruct d cs base fits out = some (.struct ds) := by
  obtain ⟨out, e⟩ := cs.encode_exists ds h _ m
  exact ⟨out, e, by simp only [decodePackedStruct, cs.decode_encode ds _ m out e, Option.map_some]⟩

/-- Actual homogeneous DataList conversion, used only to construct fixed arrays. -/
def arrayMembers {D : Source.Layout} {τ : Source.STy} : (n : Nat) →
    (Fin n → Source.Data D τ) → Source.DataList D (List.replicate n τ)
  | 0, _ => .nil
  | n + 1, xs => .cons (xs ⟨0, by omega⟩) (arrayMembers n (fun i => xs i.succ))

def scalarMemberHead {D : Source.Layout} {τ : Source.STy} {τs : List Source.STy}
    (ds : Source.DataList D (τ :: τs)) : Source.Data D τ := by
  cases ds with
  | cons x _ => exact x

def scalarMemberTail {D : Source.Layout} {τ : Source.STy} {τs : List Source.STy}
    (ds : Source.DataList D (τ :: τs)) : Source.DataList D τs := by
  cases ds with
  | cons _ xs => exact xs

def membersArray {D : Source.Layout} {τ : Source.STy} : (n : Nat) →
    Source.DataList D (List.replicate n τ) → Fin n → Source.Data D τ
  | 0, _ => Fin.elim0
  | n + 1, ds => Fin.cases (scalarMemberHead ds) (membersArray n (scalarMemberTail ds))

theorem membersArray_arrayMembers {D : Source.Layout} {τ : Source.STy} (n : Nat)
    (xs : Fin n → Source.Data D τ) : membersArray n (arrayMembers n xs) = xs := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact congrFun (ih (fun i => xs i.succ)) j

def repeatedMembers {D : Source.Layout} {τ : Source.STy} (f : Field)
    (w : StorageWidth D τ f.width) (c : ScalarCodec D τ f) :
    (n : Nat) → PackedMembers D (List.replicate n τ)
  | 0 => .nil
  | n + 1 => .cons f w c (repeatedMembers f w c n)

theorem arrayMembers_scalar {D : Source.Layout} {τ : Source.STy} (n : Nat)
    (xs : Fin n → Source.Val D τ) : ScalarMembers (arrayMembers n (fun i => .val (xs i))) := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact .cons _ _ (ih (fun i => xs i.succ))

def decodePackedArray {D : Source.Layout} {τ : Source.STy} (f : Field)
    (w : StorageWidth D τ f.width) (c : ScalarCodec D τ f) (n : Nat) (_ : 0 < n)
    (base : Roadmap.Word) (_ : (repeatedMembers f w c n).Fits base) (m : ByteView) :
    Option (Source.Data D (.array .storage τ (some n))) :=
  ((repeatedMembers f w c n).decode (base.val * 32) m).map
    (fun ds => .array n (fun _ h => (Option.some.inj h).symm) (membersArray n ds))

theorem packedArray_roundtrip {D : Source.Layout} {τ : Source.STy} (f : Field)
    (w : StorageWidth D τ f.width) (c : ScalarCodec D τ f) (n : Nat) (hn : 0 < n)
    (base : Roadmap.Word) (fits : (repeatedMembers f w c n).Fits base)
    (xs : Fin n → Source.Val D τ) (m : ByteView) :
    ∃ out, (repeatedMembers f w c n).encode (arrayMembers n (fun i => .val (xs i)))
      (base.val * 32) m = some out ∧
      decodePackedArray f w c n hn base fits out =
        some (.array n (fun _ h => (Option.some.inj h).symm) (fun i => .val (xs i))) := by
  obtain ⟨out, e⟩ := (repeatedMembers f w c n).encode_exists _ (arrayMembers_scalar n xs) _ m
  refine ⟨out, e, ?_⟩
  simp only [decodePackedArray, PackedMembers.decode_encode _ _ _ m out e,
    Option.map_some, membersArray_arrayMembers]

theorem PackedMembers.head_tail_disjoint {D : Source.Layout} {τs : List Source.STy}
    (cs : PackedMembers D τs) (cursor : Nat) (f : Field) (a : Nat)
    (tail : cs.owns (packedStart cursor f.width + f.width) a) :
    ¬ (packedStart cursor f.width ≤ a ∧ a < packedStart cursor f.width + f.width) := by
  have h := cs.owned_bounds _ a tail
  omega

theorem PackedMembers.nextSlot_spec {D : Source.Layout} {τs : List Source.STy}
    (cs : PackedMembers D τs) (base : Roadmap.Word) :
    cs.endByte (base.val * 32) ≤ cs.nextSlot base * 32 ∧
    cs.nextSlot base * 32 < cs.endByte (base.val * 32) + 32 := by
  unfold PackedMembers.nextSlot
  have := Nat.mod_add_div (cs.endByte (base.val * 32) + 31) 32
  have := Nat.mod_lt (cs.endByte (base.val * 32) + 31) (by decide : 0 < 32)
  omega

theorem PackedMembers.decode_congr {D : Source.Layout} {τs : List Source.STy}
    (cs : PackedMembers D τs) (cursor : Nat) (m m' : ByteView)
    (h : ∀ a, cs.owns cursor a → m a = m' a) : cs.decode cursor m = cs.decode cursor m' := by
  induction cs generalizing cursor with
  | nil => rfl
  | cons f w c rest ih =>
    have hb : (fun i : Fin f.width => m (packedStart cursor f.width + i.val)) =
        (fun i : Fin f.width => m' (packedStart cursor f.width + i.val)) := by
      funext i
      exact h _ (Or.inl ⟨by omega, by have := i.isLt; omega⟩)
    change (do
      let v ← c.bytesBE.littleEndian.decode (fun i => m (packedStart cursor f.width + i.val))
      let tail ← rest.decode (packedStart cursor f.width + f.width) m
      pure (Source.DataList.cons (.val v) tail)) = (do
      let v ← c.bytesBE.littleEndian.decode (fun i => m' (packedStart cursor f.width + i.val))
      let tail ← rest.decode (packedStart cursor f.width + f.width) m'
      pure (Source.DataList.cons (.val v) tail))
    rw [hb, ih _ (fun a ha => h a (Or.inr ha))]

end Solidity.Yul.Views
