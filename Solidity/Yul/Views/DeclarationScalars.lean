import Solidity.Yul.Views.PackedSlots
import Solidity.Yul.Views.FinitePaths
import Solidity.Yul.Views.ComponentComposition

/-! Declaration-driven seeds for the EXISTING packing planner. Actual source
scalar types choose existing exact codecs; no alternative type/state or assumed
inverse/read/safety law. Unsupported preparation is not a language refusal. -/
namespace Solidity.Yul.Views

structure DeclScalar (D : Source.Layout) (τ : Source.STy) where
  field : Field
  width : StorageWidth D τ field.width
  codec : ScalarCodec D τ field

def declarationScalar? (D : Source.Layout) : (τ : Source.STy) → Option (DeclScalar D τ)
  | .bool => some ⟨boolField,.bool,boolCodec D⟩
  | .int t => some ⟨intField t 0 (by have := t.valid; omega),.int t,intCodec D t 0 (by have := t.valid; omega)⟩
  | .fixed t => some ⟨intField (fixedIntTy t) 0 (by change 0 + t.bits / 8 ≤ 32; have := t.valid; omega),.fixed t,fixedCodec D t 0 (by have := t.valid; omega)⟩
  | .address p => some ⟨addressField 0 (by decide),.address p,addressCodec D p 0 (by decide)⟩
  | .contract d => some ⟨addressField 0 (by decide),.contract d,contractCodec D d 0 (by decide)⟩
  | .fixedBytes n h => some ⟨fixedBytesField n h 0 (by omega),.fixedBytes n h,fixedBytesCodec D n h 0 (by omega)⟩
  | .enum d => if bounded : 0 < D.enumSize d ∧ D.enumSize d ≤ 256 then
      some ⟨enumField 0 (by decide),.enum d bounded,enumCodec D d 0 (by decide) bounded.2⟩ else none
  | .fn true ps rs m => some ⟨externalFnField 0 (by decide),.externalFn ps rs m,externalFnCodec D ps rs m 0 (by decide)⟩
  | _ => none

def declarationMembers? (D : Source.Layout) : (types : List Source.STy) → Option (PackedMembers D types)
  | [] => some .nil
  | τ::types => (declarationScalar? D τ).bind (fun scalar =>
      (declarationMembers? D types).map (fun rest => .cons scalar.field scalar.width scalar.codec rest))

/-- Member coordinates reuse packedStart, not a second packing algorithm. -/
structure DeclPosition (D : Source.Layout) (τ : Source.STy) where
  start : Nat
  field : Field
  width : StorageWidth D τ field.width
  codec : ScalarCodec D τ field
  aligned : field.offset = start % 32

/-- Shift only the field offset; the existing exact payload codec is reused. -/
def DeclScalar.position {D τ} (seed : DeclScalar D τ) (cursor : Nat) : DeclPosition D τ :=
  let start := packedStart cursor seed.field.width
  let fits := (packedStart_spec cursor seed.field).2
  ⟨start,⟨start % 32,seed.field.width,seed.field.positive,fits⟩,seed.width,
    seed.codec.atOffset (start % 32) fits,rfl⟩

theorem DeclScalar.position_bounds {D τ} (seed : DeclScalar D τ) (cursor : Nat) :
    cursor ≤ (seed.position cursor).start ∧
    (seed.position cursor).start % 32 + (seed.position cursor).field.width ≤ 32 :=
  packedStart_spec cursor seed.field

theorem DeclScalar.position_width {D τ} (seed : DeclScalar D τ) (cursor : Nat) :
    (seed.position cursor).field.width = seed.field.width := rfl

end Solidity.Yul.Views
