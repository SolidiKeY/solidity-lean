import Solidity.Yul.Views.ScalarBytes
import Solidity.Yul.Views.Controls

/-! Concrete canonical scalar and residual combination witnesses. Refused
canonical enum decoding is not an admission rule for dirty assembly storage. -/
namespace Solidity.Yul.Views.Controls

def signed8 : Source.IntTy := ⟨true, 8, by decide⟩
def signed256 : Source.IntTy := ⟨true, 256, by decide⟩
def scaled16 : Source.FixTy := ⟨true, 16, 2, by decide⟩
def scalarLayout : Source.Layout := ⟨fun _ => [], fun _ => 3, fun _ => .bool⟩
def scalarName : Source.DeclName := ⟨some "Physical", "Scalar"⟩

theorem signed_boundaries :
    intPayload signed8 (-128) = 128 ∧ intPayload signed8 (-1) = 255 ∧
    intPayload signed8 127 = 127 ∧ readIntPayload signed8 255 = -1 := by decide

theorem unsigned_is_not_signed : readIntPayload Source.IntTy.u8 255 = 255 ∧
    readIntPayload signed8 255 = -1 := by decide

theorem full_signed_boundary :
    readIntPayload signed256 (intPayload signed256 (-((2 ^ 255 : Nat) : Int))) =
      -((2 ^ 255 : Nat) : Int) :=
  read_intPayload signed256 _ (by decide)

theorem canonical_signed_decode :
    (intCodec layout signed8 7 (by decide)).decode ⟨255, by decide⟩ =
      some (.int (-1) (by decide)) := rfl

theorem canonical_scaled_decode :
    (fixedCodec layout scaled16 3 (by decide)).decode ⟨65511, by decide⟩ =
      some (.fixed (-25) (by decide)) := rfl

theorem canonical_bytes_payload :
    ((fixedBytesCodec layout 2 (by decide) 1 (by decide)).encode
      (.fixedBytes [0x12, 0x34] rfl)).val = 0x1234 := rfl

theorem canonical_bytes_serialization :
    List.ofFn ((fixedBytesCodec layout 2 (by decide) 1 (by decide)).bytesBE.encode
      (.fixedBytes [0x12, 0x34] rfl)) = [0x12, 0x34] := rfl

theorem address_high_boundary :
    ((addressCodec layout false 12 (by decide)).encode
      (.address ⟨2 ^ 160 - 1, by decide⟩)).val = 2 ^ 160 - 1 := rfl

theorem contract_decode :
    (contractCodec layout scalarName 2 (by decide)).decode ⟨0x1234, by decide⟩ =
      some (.contract ⟨0x1234, by decide⟩) := rfl

theorem enum_decode_controls :
    (enumCodec scalarLayout scalarName 5 (by decide) (by decide)).decode ⟨2, by decide⟩ =
      some (.enum ⟨2, by decide⟩) ∧
    (enumCodec scalarLayout scalarName 5 (by decide) (by decide)).decode ⟨3, by decide⟩ = none := by
  constructor <;> rfl

theorem udvt_underlying_identity :
    ((udvtCodec scalarLayout scalarName boolField (boolCodec scalarLayout)).encode
      (.udvt (.bool true))).val = 1 := rfl

theorem external_function_payload :
    ((externalFnCodec layout [] [] none 8 (by decide)).encode
      (.externalFn ⟨0x1234, by decide⟩ [0xde, 0xad, 0xbe, 0xef] rfl)).val = 0x1234deadbeef := rfl

def scalarPackedSlot : Nat :=
  (⟨3, 1, by decide, by decide⟩ : Field).save
    ((fixedBytesField 2 (by decide) 1 (by decide)).save
      ((intField signed8 0 (by decide)).save 0x556600000000
        ((intCodec layout signed8 0 (by decide)).encode (.int (-1) (by decide))))
      ((fixedBytesCodec layout 2 (by decide) 1 (by decide)).encode (.fixedBytes [0x12, 0x34] rfl)))
    ((boolCodecAt layout 3 (by decide)).encode (.bool true))

theorem packed_scalar_combination :
    scalarPackedSlot = 0x5566011234ff ∧
    (intField signed8 0 (by decide)).find scalarPackedSlot = 255 ∧
    (fixedBytesField 2 (by decide) 1 (by decide)).find scalarPackedSlot = 0x1234 ∧
    scalarPackedSlot / 256 ^ 4 = 0x5566 := by decide

theorem concrete_signed_residual_region :
    oneRegion.encode (fun _ => (intCodec layout signed8 0 (by decide)).bytesBE)
      (fun _ => .int (-1) (by decide)) (fun _ => 0xa5) 0 = 255 ∧
    oneRegion.encode (fun _ => (intCodec layout signed8 0 (by decide)).bytesBE)
      (fun _ => .int (-1) (by decide)) (fun _ => 0xa5) 19 = 0xa5 := by decide

#print axioms read_intPayload
#print axioms ScalarCodec.bytesBE
#print axioms packed_scalar_combination

end Solidity.Yul.Views.Controls
