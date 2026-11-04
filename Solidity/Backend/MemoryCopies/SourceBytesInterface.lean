import Solidity.Backend.MemoryCopies.SourceRootCopies
import Solidity.Backend.Aggregates.G18ArrayAccess

/-! Static typed Source storage inputs for the existing byte-copy traversal.
No successful aggregate load, compiler or physical layout is assumed. -/
namespace Solidity.Backend.MemoryCopies

/-- An actual persistent Source storage cell at its exact type and value.
The representation is the published Source storage; no read run is a field. -/
structure PersistentSourceCell {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (frame : Source.Fr) (path : Source.SPath) (before : Source.EMState E Γ)
    (value : Source.Val E.layout τ) : Prop where
  typed : E.cellTy path = τ
  persistent : E.transientRoot path = false
  stored : (before.2.ex.world.accounts frame.this).storage.read path =
    some (cast (congrArg (Source.Val E.layout) typed.symm) value)

/-- Typed actual payload cells. Length and its integer range are supplied
separately. This is the persistent-storage fragment, not Source admission. -/
def SourceByteRange {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
    (path : Source.SPath) (before : Source.EMState E Γ) (start : Nat) (bytes : List UInt8) : Prop :=
  ∀ index : Fin bytes.length,
    PersistentSourceCell frame (path.go (.index (start + index.val))) before
      (Source.Val.fixedBytes (h := by decide) [bytes[index]] rfl)

end Solidity.Backend.MemoryCopies
