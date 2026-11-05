import Solidity.Backend.MemoryCopies.SourceStringsInterface
import Solidity.Backend.MemoryCopies.SourceBytes

/-! Actual Source string payload load and fresh-parent allocation. -/
namespace Solidity.Backend.MemoryCopies

theorem sourceStringLoad_run {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
    (path : Source.SPath) (before : Source.EMState E Γ) (bytes : List UInt8) (slack : Nat)
    (range : Source.IntTy.u256.lo ≤ (bytes.length : Int) ∧ (bytes.length : Int) ≤ Source.IntTy.u256.hi)
    (length : PersistentSourceCell frame path before (Source.Val.int bytes.length range))
    (cells : SourceByteRange frame path before 0 bytes) :
    (Source.loadMem (E := E) (Γ := Γ) frame (bytes.length + 2 + slack) (.string .memory) path).run before =
      (.ok (.string bytes),before) := by
  have budget : bytes.length + 2 + slack = (bytes.length + 1 + slack) + 1 := by omega
  rw [budget,Source.loadMem,Source.Hoare.run_bind,sourceByteLength_run frame path before bytes range length]
  dsimp only
  rw [Source.Hoare.run_bind,sourceByteRange_run frame path before bytes 0 slack cells]
  rfl

def sourceStringCopies : SourceStringCopies where
  copy := by
    intro E Γ frame path before bytes slack range length cells
    exact storageCopyCertificate frame _ _ rfl path before before (.string bytes)
      (sourceStringLoad_run frame path before bytes slack range length cells)

#print axioms sourceStringLoad_run
#print axioms sourceStringCopies
end Solidity.Backend.MemoryCopies
