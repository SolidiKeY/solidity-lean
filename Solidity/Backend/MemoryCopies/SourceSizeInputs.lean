import Solidity.Backend.MemoryCopies.Premises

/-! Additive inputs for deriving the existing new-array length-panic premise.
The published record and its failure projection remain unchanged. -/
namespace Solidity.Backend.MemoryCopies

/-- Evaluation, conversion and the published oversized-length branch, without
assuming its final panic equation. This does not finalize allocation or supply
cursor-overflow semantics from S03-PANIC41. -/
structure NewArrayLengthPanicInputs {E : Source.Env} {Γ : Source.RCtx}
    {τ σ : Source.STy} (global : Source.Glob E) (frame : Source.Fr)
    (fuel : Nat) (newable : τ.newable = true) (length : Source.RExpr E Γ σ)
    (index : σ.isIndex = true) (value : Source.RVal E.layout σ) (count : Nat)
    (before reached : Source.EMState E Γ) : Prop where
  evaluation : (Source.evalE global frame fuel length).run before = (.ok value, reached)
  conversion : (Source.indexNat (E := E) (Γ := Γ) value).run reached = (.ok count, reached)
  oversized : 2 ^ 64 ≤ count

end Solidity.Backend.MemoryCopies
