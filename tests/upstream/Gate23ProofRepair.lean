import Solidity.Calculus.CallbackDerive

/-! Focused proof controls for the gate-23 repairs. The source API fixtures
remain unchanged and are checked separately by the coordinator's full gate. -/
namespace Solidity.Tests.Gate23ProofRepair
open Decide

private def u (n : Nat) (h : PrimTy.uint.inRange n = true) : LTm C (.val .uint) :=
  .lit (PrimTy.uint.ofLit n h)

/-- A returning symbolic numerator still fails at a literal zero divisor. -/
theorem symbolicZero (C : Contract) :
    ({} : Facts C).fold2 (.binop .div rfl) (.var 0) (u 0 rfl) = .err := by rfl

/-- An unknown numerator's evaluation stays in front of failure. -/
theorem partialNumerator (C : Contract) :
    ({} : Facts C).fold2 (.binop .div rfl)
      (.app2 (.binop .div rfl) (.var 0) (.var 1)) (u 0 rfl) =
      .seq (.app2 (.binop .div (p := .uint) rfl) (.var 0) (.var 1)) .err := by rfl

/-- A failing denominator is not mistaken for a literal zero. -/
theorem partialDenominator (C : Contract) :
    ({} : Facts C).fold2 (.binop .div rfl) (.var 0) .err =
      .app2 (.binop .div (p := .uint) rfl) (.var 0) .err := by rfl

/-- The adjacent nonzero divisor keeps its ordinary symbolic operation. -/
theorem nonzeroDivisor (C : Contract) :
    ({} : Facts C).fold2 (.binop .div rfl) (.var 0) (u 1 rfl) =
      .app2 (.binop .div rfl) (.var 0) (u 1 rfl) := by rfl

/-- Signed zero has the same failure behavior; no unsigned cast is used. -/
theorem signedZero (C : Contract) :
    ({} : Facts C).fold2 (.binop .div rfl) (.var (p := .int) 0)
      (.lit (PrimTy.int.ofLit 0 rfl)) = .err := by rfl

/-- With no break condition, invPost discards this callback continuation.
Dispatch must inspect that resulting formula before scanning its arguments. -/
theorem discardedContinuation (C : Contract) :
    ProvesC (C := C) .tt false [] .nil
      (Fml.invPost .box (Γ := []) .refl Prog.nil Frames.nil (.havoc .tt) .tt none) := by
  sol_prove

#print axioms symbolicZero
#print axioms partialNumerator
#print axioms partialDenominator
#print axioms nonzeroDivisor
#print axioms signedZero
#print axioms discardedContinuation
#print axioms zeroDivisor_eval

end Solidity.Tests.Gate23ProofRepair
