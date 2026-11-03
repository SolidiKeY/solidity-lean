import Solidity.Lowering.V08.LiteralFailureCalldataDecode

/-! The published calldata-slice progress proof consumed by the existing calldata
ABI decoder arm. No slice or decoder semantics is reimplemented. -/
namespace Solidity.Lowering.V08.LiteralFailureSliceDecode
open Solidity Source

/-- The data-expression premise is discharged by the actual published slice
law for arbitrary typed caller indices, both explicit and absent ends. -/
theorem slice_ok {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 {H : HeapTy} {types : List STy} {t u : IntTy}
 (x : Idx Γ (.bytes .calldata)) (s : Idx Γ (.int t))
 (hs : STy.isIndex (.int t) = true) (e : Idx Γ (.int u))
 (he : STy.isIndex (.int u) = true) (toEnd : Bool)
 (admitted : types.all (STy.decodable E) = true) :
 Hoare (MemOK E H)
  (evalE G F (n+1+1+1)
   (.abiDecode (.slice (.local x) rfl (.local s) hs (.local e) he toEnd) rfl admitted))
  (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v)
  (fun failure y => MemOK E H y ∧ NotStuck failure) := by
 exact LiteralFailureCalldataDecode.arm G F (n+1+1) _ admitted
  (evalE_cdSlice_ok G F n x rfl s hs e he toEnd)

end Solidity.Lowering.V08.LiteralFailureSliceDecode
