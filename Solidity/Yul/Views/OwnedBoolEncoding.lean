import Solidity.Yul.Views.ScalarWriteback
import Solidity.Yul.Views.DeclarationPacking

namespace Solidity.Yul.Views

/-- All eight owned bits are retained. A true bool may use any nonzero byte;
false is zero. This is a physical representation parameter, not another
logical source bool or a dirty-local embedding. -/
abbrev BoolTrueByte := {byte : Fin 256 // byte.val ≠ 0}

def canonicalTrueByte : BoolTrueByte := ⟨⟨1,by decide⟩,by decide⟩

/-- Zero has no nonzero true encoding to replace: retain the previous choice.
This preserves exact representation state on an unchanged false view. -/
def chooseTrueByte (old : BoolTrueByte) (raw : Fin 256) : BoolTrueByte :=
  if nonzero : raw.val≠0 then ⟨raw,nonzero⟩ else old

def boolByteMeaning (raw : Fin 256) : Bool := decide (raw.val≠0)

/-- Same real Source.Val bool; only the physical byte encoder varies. No old
canonical codec/guard is changed and no bit is put in the unowned complement. -/
def representedBoolCodec (D : Source.Layout) (field : Field) (width : field.width=1)
    (code : BoolTrueByte) : ScalarCodec D .bool field where
  encode value := by
    cases value with
    | bool b => exact ⟨if b then code.val.val else 0, by
        change _ < field.modulus
        rw [Field.modulus,width]
        cases b
        · change 0 < 256^1; decide
        · change code.val.val < 256; exact code.val.isLt⟩
    | memRef h _ | storRef h _ | cdRef h _ => cases h
  decode raw := if raw.val=0 then some (.bool false)
    else if raw.val=code.val.val then some (.bool true) else none
  decode_encode value := by
    cases value with
    | bool b =>
      cases b
      · rfl
      · change (if code.val.val=0 then _ else if code.val.val=code.val.val then _ else _)=_
        rw [if_neg code.property,if_pos rfl]
    | memRef h _ | storRef h _ | cdRef h _ => cases h

def fieldBooleanByte (field : Field) (width : field.width=1) (raw : field.Value) : Fin 256 :=
  ⟨raw.val,by have bound:=raw.isLt; simpa only [Field.modulus,width] using bound⟩

theorem representedBool_decode_raw (D : Source.Layout) (field : Field) (width : field.width=1)
    (old : BoolTrueByte) (raw : field.Value) :
    (representedBoolCodec D field width (chooseTrueByte old (fieldBooleanByte field width raw))).decode raw=
      some (.bool (boolByteMeaning (fieldBooleanByte field width raw))) := by
  by_cases zero : raw.val=0
  · simp only [representedBoolCodec,chooseTrueByte,fieldBooleanByte,boolByteMeaning,zero,ne_eq,not_true_eq_false,decide_false,if_true]
  · simp only [representedBoolCodec,chooseTrueByte,fieldBooleanByte,boolByteMeaning,zero,ne_eq,not_false_eq_true,decide_true,dif_pos trivial,if_false,if_true]

theorem representedBool_encode_raw (D : Source.Layout) (field : Field) (width : field.width=1)
    (old : BoolTrueByte) (raw : field.Value) :
    (representedBoolCodec D field width (chooseTrueByte old (fieldBooleanByte field width raw))).encode
      (.bool (boolByteMeaning (fieldBooleanByte field width raw)))=raw := by
  apply Fin.ext
  by_cases zero : raw.val=0
  · simp only [representedBoolCodec,chooseTrueByte,fieldBooleanByte,boolByteMeaning,zero,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,if_false]
  · simp only [representedBoolCodec,chooseTrueByte,fieldBooleanByte,boolByteMeaning,zero,ne_eq,not_false_eq_true,decide_true,if_true,dif_pos trivial]

theorem representedBool_canonicalDecode_raw (D : Source.Layout) (field : Field) (width : field.width=1)
    (old : BoolTrueByte) (raw : field.Value) :
    canonicalScalarDecode (representedBoolCodec D field width (chooseTrueByte old (fieldBooleanByte field width raw))) raw=
      some (.bool (boolByteMeaning (fieldBooleanByte field width raw))) := by
  rw [canonicalScalarDecode,representedBool_decode_raw,Option.bind_some,representedBool_encode_raw,if_pos rfl]

theorem chooseTrueByte_self (old : BoolTrueByte) : chooseTrueByte old old.val=old := by
  unfold chooseTrueByte
  rw [dif_pos old.property]

theorem chooseTrueByte_zero (old : BoolTrueByte) : chooseTrueByte old ⟨0,by decide⟩=old := rfl

theorem representedBool_unchanged (D : Source.Layout) (field : Field) (width : field.width=1)
    (old : BoolTrueByte) (b : Bool) :
    chooseTrueByte old (fieldBooleanByte field width ((representedBoolCodec D field width old).encode (.bool b)))=old := by
  cases b
  · exact chooseTrueByte_zero old
  · exact chooseTrueByte_self old

/-- Checked canonical compatibility, not a change to canonical bool admission. -/
theorem representedBool_canonical (D : Source.Layout) :
    representedBoolCodec D boolField rfl canonicalTrueByte=boolCodec D := by
  rfl

end Solidity.Yul.Views
