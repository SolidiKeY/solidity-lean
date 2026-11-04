import Solidity.Backend.MemoryCopies.SourceBytesInterface

/-! String copies share the existing Source byte reader and static cell inputs. -/
namespace Solidity.Backend.MemoryCopies

/-- A complete Source string-copy family from actual persistent length/payload
cells. No string load success or string/bytes admission conversion is assumed. -/
structure SourceStringCopies : Prop where
  copy : ∀ (E : Source.Env) (Γ : Source.RCtx) (frame : Source.Fr) (path : Source.SPath)
    (before : Source.EMState E Γ) (bytes : List UInt8) (slack : Nat)
    (range : Source.IntTy.u256.lo ≤ (bytes.length : Int) ∧ (bytes.length : Int) ≤ Source.IntTy.u256.hi),
    PersistentSourceCell frame path before (Source.Val.int bytes.length range) →
    SourceByteRange frame path before 0 bytes →
    SourceStorageCopyCertificate frame (bytes.length + 2 + slack) (.string .memory) rfl path before before
      (allocatedState (Source.Data.string (l := .memory) bytes) before) before.2.heap.next (Source.Data.string bytes)

end Solidity.Backend.MemoryCopies
