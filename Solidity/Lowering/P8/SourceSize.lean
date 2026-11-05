import Solidity.Backend.MemoryCopies.Premises

/-! Additive compatible Source-size consumer interface (SS1/H30).
The existing NewArrayLengthPanicPremise record, including its failure field,
is unchanged. This derived law has the same statement under a distinct name
and proves it from evaluation, conversion and oversized, not that field.
The complete reached state and exact allocation-panic result are retained.
This covers only the existing 2^64 new-array branch; it does not supply missing
finalize-allocation/cursor-overflow semantics, a compiler certificate, admission
or physical allocation adequacy. Public indices and result type are frozen.
-/
namespace Solidity.Backend.MemoryCopies

/-- The exact existing failure-field statement, derived independently from
its three operational parts. No rollback to the initial state is introduced. -/
theorem NewArrayLengthPanicPremise.failure_of_parts
    {E : Source.Env} {Γ : Source.RCtx} {τ σ : Source.STy}
    {global : Source.Glob E} {frame : Source.Fr} {fuel : Nat}
    {newable : τ.newable = true} {length : Source.RExpr E Γ σ}
    {index : σ.isIndex = true} {value : Source.RVal E.layout σ} {count : Nat}
    {before reached : Source.EMState E Γ}
    (p : NewArrayLengthPanicPremise global frame fuel newable length index value
      count before reached) :
    (Source.evalE global frame (fuel + 1)
      (Source.RExpr.newArray (τ := τ) newable length index)).run before =
        (Source.panic .alloc, reached) := by
  rw [Source.evalE]
  simp only [Source.Hoare.run_bind, p.evaluation, p.conversion, if_pos p.oversized]
  rfl

end Solidity.Backend.MemoryCopies

/-- info: 'Solidity.Backend.MemoryCopies.NewArrayLengthPanicPremise.failure_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.MemoryCopies.NewArrayLengthPanicPremise.failure_of_parts
