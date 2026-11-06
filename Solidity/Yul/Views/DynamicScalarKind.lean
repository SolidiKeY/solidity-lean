import Solidity.Yul.Views.DeclarationScalars
import Solidity.Source.Machine

namespace Solidity.Yul.Views

/-- Intrinsic descriptor of additional ACTUAL source scalar families. Not an
integer reinterpretation, new source type, or admission/refusal policy. -/
inductive DynamicScalarKind where
  | bool
  | address (payable : Bool)
  | fixedBytes (n : Nat) (valid : 0 < n ∧ n ≤ 32)
  deriving DecidableEq

def DynamicScalarKind.ty : DynamicScalarKind → Source.STy
  | .bool => .bool
  | .address p => .address p
  | .fixedBytes n h => .fixedBytes n h

def DynamicScalarKind.seed (k : DynamicScalarKind) (D : Source.Layout) : DeclScalar D k.ty :=
  match k with
  | .bool => ⟨boolField,.bool,boolCodec D⟩
  | .address p => ⟨addressField 0 (by decide),.address p,addressCodec D p 0 (by decide)⟩
  | .fixedBytes n h => ⟨fixedBytesField n h 0 (by omega),.fixedBytes n h,fixedBytesCodec D n h 0 (by omega)⟩

theorem DynamicScalarKind.cell (k : DynamicScalarKind) : k.ty.cell = k.ty := by
  cases k <;> rfl

theorem DynamicScalarKind.isValue (k : DynamicScalarKind) : k.ty.isValue = true := by
  cases k <;> rfl

end Solidity.Yul.Views
