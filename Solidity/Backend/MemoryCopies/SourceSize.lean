import Solidity.Backend.MemoryCopies.Premises

/-! The current Source length check is a local derived law. This does not
supply the separate S03 finalize-allocation/cursor-overflow semantics. -/
namespace Solidity.Backend.MemoryCopies

/-- Length evaluation effects are retained by the panic branch. The panic
result is a conclusion, not a constructor argument to the premise record. -/
theorem NewArrayLengthPanicPremise.failure {E : Source.Env} {Γ : Source.RCtx}
    {τ σ : Source.STy} {global : Source.Glob E} {frame : Source.Fr}
    {fuel : Nat} {newable : τ.newable = true} {length : Source.RExpr E Γ σ}
    {index : σ.isIndex = true} {value : Source.RVal E.layout σ} {count : Nat}
    {before reached : Source.EMState E Γ}
    (p : NewArrayLengthPanicPremise global frame fuel newable length index value count before reached) :
    (Source.evalE global frame (fuel + 1)
      (Source.RExpr.newArray (τ := τ) newable length index)).run before =
        (Source.panic .alloc, reached) := by
  change (do
    let value ← Source.evalE global frame fuel length
    let count ← Source.indexNat value
    if 2 ^ 64 ≤ count then Source.EM.lift (Source.panic .alloc)
    else do
      let data ← Source.EM.lift (Source.newData τ count)
      let reference ← Source.allocRef data
      pure (Source.RVal.val reference)).run before = _
  rw [Source.Hoare.run_bind, p.evaluation]
  change (do
    let count ← Source.indexNat value
    if 2 ^ 64 ≤ count then Source.EM.lift (Source.panic .alloc)
    else do
      let data ← Source.EM.lift (Source.newData τ count)
      let reference ← Source.allocRef data
      pure (Source.RVal.val reference)).run reached = _
  rw [Source.Hoare.run_bind, p.conversion]
  simp only [if_pos p.oversized]
  rfl

#print axioms NewArrayLengthPanicPremise.failure
end Solidity.Backend.MemoryCopies
