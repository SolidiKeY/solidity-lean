import Solidity.Backend.MemoryCopies.SourceStoredFields

/-! Reference closure of proved existing Source storage-copy families.
These obligations extend SourceStoredValue, without a new type selector. -/
namespace Solidity.Backend.MemoryCopies

def SourceStoredStructValue {E : Source.Env} {Γ : Source.RCtx} {frame : Source.Fr}
    {path : Source.SPath} {before : Source.EMState E Γ} (name : Source.DeclName)
    (fields : SourceStoredFields frame path before 0 (E.layout.fields name)) : Prop :=
  ∃ value : SourceStoredValue frame path before (.struct .memory name),
    value.horizon = fields.horizon + 2 ∧ value.objects = fields.objects + 1

def SourceStoredEmptyArrayValue {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
    (path : Source.SPath) (before : Source.EMState E Γ) (element : Source.STy) : Prop :=
  ∃ value : SourceStoredValue frame path before (.array .memory element none),
    value.horizon = 3 ∧ value.objects = 1

def SourceStoredByteArrayValue {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
    (path : Source.SPath) (before : Source.EMState E Γ) (children : List (List UInt8)) : Prop :=
  ∃ value : SourceStoredValue frame path before (.array .memory (.bytes .memory) none),
    value.horizon = byteChildrenHorizon children + 2 ∧ value.objects = children.length + 1

end Solidity.Backend.MemoryCopies
