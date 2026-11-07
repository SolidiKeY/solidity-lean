import Solidity.Yul.Views.Widths
import Solidity.Source.Observe

/-!
# Canonical scalar packing over actual source values

Storage fields are right-aligned within their byte interval, including bytesN.
Signed integers retain the low-width two's-complement payload. These codecs
are canonical logical-value components, not a dirty-bit writeback policy or
an instance of the whole G27 source layout.
-/
-- Retain typed codec proof reductions across the 4.35 generated eliminators.
set_option backward.isDefEq.respectTransparency false

namespace Solidity.Yul.Views

/-- An arbitrary valid offset for an integer's documented byte width. -/
def intField (t : Source.IntTy) (off : Nat) (fits : off + t.bits / 8 ≤ 32) : Field :=
  ⟨off, t.bits / 8, by have h := t.valid; omega, fits⟩

theorem intField_modulus (t : Source.IntTy) (off : Nat) (fits : off + t.bits / 8 ≤ 32) :
    (intField t off fits).modulus = 2 ^ t.bits := by
  change (2 ^ 8) ^ (t.bits / 8) = 2 ^ t.bits
  rw [← Nat.pow_mul]
  congr 1
  have h := t.valid
  omega

theorem int_modulus_double (t : Source.IntTy) :
    2 ^ t.bits = 2 ^ (t.bits - 1) + 2 ^ (t.bits - 1) := by
  have h := t.valid
  have e : t.bits = (t.bits - 1) + 1 := by omega
  conv => lhs; rw [e, Nat.pow_succ]
  omega

/-- Low-width two's complement; range proofs below prevent truncation. -/
def intPayload (t : Source.IntTy) (v : Int) : Nat :=
  (if v < 0 then v + (2 ^ t.bits : Nat) else v).toNat

def readIntPayload (t : Source.IntTy) (n : Nat) : Int :=
  if t.signed ∧ 2 ^ (t.bits - 1) ≤ n then (n : Int) - (2 ^ t.bits : Nat) else n

theorem intPayload_bound (t : Source.IntTy) (v : Int) (h : t.lo ≤ v ∧ v ≤ t.hi) :
    intPayload t v < 2 ^ t.bits := by
  have hd := int_modulus_double t
  have hp : 0 < 2 ^ (t.bits - 1) := Nat.pow_pos (by decide)
  unfold intPayload
  simp only [Source.IntTy.lo, Source.IntTy.hi] at h
  cases hs : t.signed <;> simp only [hs, Bool.false_eq_true, if_false, if_true] at h
  · split <;> omega
  · split <;> omega

theorem read_intPayload (t : Source.IntTy) (v : Int) (h : t.lo ≤ v ∧ v ≤ t.hi) :
    readIntPayload t (intPayload t v) = v := by
  have hd := int_modulus_double t
  have hp : 0 < 2 ^ (t.bits - 1) := Nat.pow_pos (by decide)
  unfold intPayload readIntPayload
  simp only [Source.IntTy.lo, Source.IntTy.hi] at h
  cases hs : t.signed <;>
    simp only [hs, Bool.false_eq_true, if_false, if_true, false_and, true_and] at h ⊢
  · omega
  · split <;> split <;> omega

/-- Decode may fail its source range check; canonical encodings always pass. -/
def intCodec (D : Source.Layout) (t : Source.IntTy) (off : Nat)
    (fits : off + t.bits / 8 ≤ 32) : ScalarCodec D (.int t) (intField t off fits) where
  encode v := by
    cases v with
    | int n h => exact ⟨intPayload t n, by rw [intField_modulus]; exact intPayload_bound t n h⟩
    | memRef h _ | storRef h _ | cdRef h _ => cases h
  decode n := let v := readIntPayload t n.val
    if h : t.lo ≤ v ∧ v ≤ t.hi then some (.int v h) else none
  decode_encode v := by
    cases v with
    | int n h => simp only [Source.STy.int.noConfusion, Source.STy.noConfusion, id, read_intPayload t n h, dif_pos h]
    | memRef h _ | storRef h _ | cdRef h _ => cases h

/-- Address and contract payloads use the same 20-byte representation. -/
def addressField (off : Nat) (fits : off + 20 ≤ 32) : Field := ⟨off, 20, by decide, fits⟩

def addressCodec (D : Source.Layout) (p : Bool) (off : Nat) (fits : off + 20 ≤ 32) :
    ScalarCodec D (.address p) (addressField off fits) where
  encode v := by
    cases v with
    | address a => exact a
    | memRef h _ | storRef h _ | cdRef h _ => cases h
  decode a := some (.address a)
  decode_encode v := by
    cases v with
    | address a => rfl
    | memRef h _ | storRef h _ | cdRef h _ => cases h

def contractCodec (D : Source.Layout) (d : Source.DeclName) (off : Nat) (fits : off + 20 ≤ 32) :
    ScalarCodec D (.contract d) (addressField off fits) where
  encode v := by
    cases v with
    | contract a => exact a
    | memRef h _ | storRef h _ | cdRef h _ => cases h
  decode a := some (.contract a)
  decode_encode v := by
    cases v with
    | contract a => rfl
    | memRef h _ | storRef h _ | cdRef h _ => cases h

def enumField (off : Nat) (fits : off + 1 ≤ 32) : Field := ⟨off, 1, by decide, fits⟩

def enumCodec (D : Source.Layout) (d : Source.DeclName) (off : Nat) (fits : off + 1 ≤ 32)
    (size : D.enumSize d ≤ 256) : ScalarCodec D (.enum d) (enumField off fits) where
  encode v := by
    cases v with
    | enum i => exact ⟨i.val, by have hi := i.isLt; change i.val < 256; omega⟩
    | memRef h _ | storRef h _ | cdRef h _ => cases h
  decode n := if h : n.val < D.enumSize d then some (.enum ⟨n.val, h⟩) else none
  decode_encode v := by
    cases v with
    | enum i => simp only [Source.STy.enum.noConfusion, Source.STy.noConfusion, id, dif_pos i.isLt]
    | memRef h _ | storRef h _ | cdRef h _ => cases h

/-- UDVTs reuse a codec for their actual declared underlying source type. -/
def udvtCodec (D : Source.Layout) (d : Source.DeclName) (f : Field)
    (c : ScalarCodec D (D.underlying d) f) : ScalarCodec D (.udvt d) f where
  encode v := by
    cases v with
    | udvt x => exact c.encode x
    | memRef h _ | storRef h _ | cdRef h _ => cases h
  decode n := (c.decode n).map Source.Val.udvt
  decode_encode v := by
    cases v with
    | udvt x => simp only [Source.STy.udvt.noConfusion, Source.STy.noConfusion, id, c.decode_encode, Option.map_some]
    | memRef h _ | storRef h _ | cdRef h _ => cases h

/-- Fixed point stores its scaled integer, using the declared signedness/width. -/
def fixedIntTy (f : Source.FixTy) : Source.IntTy :=
  ⟨f.signed, f.bits, f.valid.1, f.valid.2.1, f.valid.2.2.1⟩

def fixedCodec (D : Source.Layout) (f : Source.FixTy) (off : Nat)
    (fits : off + f.bits / 8 ≤ 32) : ScalarCodec D (.fixed f) (intField (fixedIntTy f) off fits) where
  encode v := by
    cases v with
    | fixed n h => exact ⟨intPayload (fixedIntTy f) n, by
        rw [intField_modulus]; exact intPayload_bound (fixedIntTy f) n h⟩
    | memRef h _ | storRef h _ | cdRef h _ => cases h
  decode n := let v := readIntPayload (fixedIntTy f) n.val
    if h : f.lo ≤ v ∧ v ≤ f.hi then some (.fixed v h) else none
  decode_encode v := by
    cases v with
    | fixed n h => simp only [Source.STy.fixed.noConfusion, Source.STy.noConfusion, id, read_intPayload (fixedIntTy f) n h, dif_pos h]
    | memRef h _ | storRef h _ | cdRef h _ => cases h

theorem scalar_beValue_bound (bs : List UInt8) : Source.beValue bs < 256 ^ bs.length := by
  have aux (xs : List UInt8) : Source.beValue xs.reverse < 256 ^ xs.reverse.length := by
    induction xs with
    | nil => decide
    | cons b xs ih =>
      rw [List.reverse_cons, List.length_append, List.length_singleton,
        Nat.pow_succ, Source.beValue_append]
      have hb := UInt8.toNat_lt b
      omega
  simpa only [List.reverse_reverse] using aux bs.reverse

/-- The other byte/numeric inverse, for any finite byte string. -/
theorem scalar_beBytes_value (bs : List UInt8) :
    Source.beBytes bs.length (Source.beValue bs) = bs := by
  have aux (xs : List UInt8) :
      Source.beBytes xs.reverse.length (Source.beValue xs.reverse) = xs.reverse := by
    induction xs with
    | nil => rfl
    | cons b xs ih =>
      rw [List.reverse_cons, List.length_append, List.length_singleton, Source.beValue_append,
        Source.beBytes]
      have hb := UInt8.toNat_lt b
      have hd : (Source.beValue xs.reverse * 256 + b.toNat) / 256 = Source.beValue xs.reverse := by omega
      have hm : (Source.beValue xs.reverse * 256 + b.toNat) % 256 = b.toNat := by omega
      rw [hd, hm, UInt8.ofNat_toNat, ih]
  simpa only [List.reverse_reverse] using aux bs.reverse

def fixedBytesField (n : Nat) (h : 1 ≤ n ∧ n ≤ 32) (off : Nat)
    (fits : off + n ≤ 32) : Field := ⟨off, n, h.1, fits⟩

/-- bytesN is a big-endian N-byte payload in storage, unlike its ABI word. -/
def fixedBytesCodec (D : Source.Layout) (n : Nat) (h : 1 ≤ n ∧ n ≤ 32) (off : Nat)
    (fits : off + n ≤ 32) : ScalarCodec D (.fixedBytes n h) (fixedBytesField n h off fits) where
  encode v := by
    cases v with
    | fixedBytes bs hl => exact ⟨Source.beValue bs, by
        change Source.beValue bs < 256 ^ n; rw [← hl]; exact scalar_beValue_bound bs⟩
    | memRef h _ | storRef h _ | cdRef h _ => cases h
  decode v := some (.fixedBytes (Source.beBytes n v.val) (Source.beBytes_length n v.val))
  decode_encode v := by
    cases v with
    | fixedBytes bs hl => simp only [Source.STy.fixedBytes.noConfusion, Source.STy.noConfusion, id, ← hl, scalar_beBytes_value]
    | memRef h _ | storRef h _ | cdRef h _ => cases h

/-- Changing only a field offset preserves the intrinsic codec value domain. -/
def ScalarCodec.atOffset {D : Source.Layout} {τ : Source.STy} {f : Field}
    (c : ScalarCodec D τ f) (off : Nat) (fits : off + f.width ≤ 32) :
    ScalarCodec D τ ⟨off, f.width, f.positive, fits⟩ where
  encode := c.encode
  decode := c.decode
  decode_encode := c.decode_encode

def boolCodecAt (D : Source.Layout) (off : Nat) (fits : off + 1 ≤ 32) :
    ScalarCodec D .bool ⟨off, 1, by decide, fits⟩ := (boolCodec D).atOffset off fits

def externalFnField (off : Nat) (fits : off + 24 ≤ 32) : Field := ⟨off, 24, by decide, fits⟩

/-- A packed external function contains its address followed by its selector. -/
def externalFnCodec (D : Source.Layout) (ps rs : List Source.STy) (m : Option Source.Mutability)
    (off : Nat) (fits : off + 24 ≤ 32) :
    ScalarCodec D (.fn true ps rs m) (externalFnField off fits) where
  encode v := by
    cases v with
    | externalFn a sel hl =>
      exact ⟨a.val * 256 ^ 4 + Source.beValue sel, by
        have ha := a.isLt
        have hs := scalar_beValue_bound sel
        rw [hl] at hs
        change a.val * 256 ^ 4 + Source.beValue sel < 256 ^ 24
        omega⟩
    | memRef h _ | storRef h _ | cdRef h _ => cases h
  decode v := some (.externalFn
    ⟨v.val / 256 ^ 4, by have hv := v.isLt; change v.val < 256 ^ 24 at hv; omega⟩
    (Source.beBytes 4 (v.val % 256 ^ 4)) (Source.beBytes_length 4 _))
  decode_encode v := by
    cases v with
    | externalFn a sel hl =>
      have hs := scalar_beValue_bound sel
      rw [hl] at hs
      have hd : (a.val * 256 ^ 4 + Source.beValue sel) / 256 ^ 4 = a.val := by omega
      have hm : (a.val * 256 ^ 4 + Source.beValue sel) % 256 ^ 4 = Source.beValue sel := by omega
      change some (Source.Val.externalFn
        ⟨(a.val * 256 ^ 4 + Source.beValue sel) / 256 ^ 4, _⟩
        (Source.beBytes 4 ((a.val * 256 ^ 4 + Source.beValue sel) % 256 ^ 4)) _) = _
      have hb : Source.beBytes 4 (Source.beValue sel) = sel := by
        rw [← hl]
        exact scalar_beBytes_value sel
      simp only [hd, hm, hb]
    | memRef h _ | storRef h _ | cdRef h _ => cases h

end Solidity.Yul.Views
