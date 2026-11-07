import Solidity.Source.Agreement.PrimitiveTypes

/-!
# A total model-to-source primitive value producer

The two independently defined integer ranges agree, including their signed
endpoints. This lets every supported model value produce an intrinsically
well-ranged source value without a caller-supplied range hypothesis. This is
only the value clause of SS-AGREE; it does not assert execution agreement.
-/

namespace Solidity.Source.Agreement

/-- Model's strict upper bound equals source's inclusive upper bound. -/
theorem uint_range (n : Int) : PrimTy.uint.inRange n = true ↔
    IntTy.u256.lo ≤ n ∧ n ≤ IntTy.u256.hi := by
  simp only [PrimTy.inRange, decide_eq_true_eq, IntTy.lo, IntTy.hi,
    IntTy.u256, Bool.false_eq_true, if_false]
  omega

/-- Signed endpoints agree without interpreting an unsigned word as signed. -/
theorem int_range (n : Int) : PrimTy.int.inRange n = true ↔
    ({ IntTy.u256 with signed := true } : IntTy).lo ≤ n ∧
    n ≤ ({ IntTy.u256 with signed := true } : IntTy).hi := by
  simp only [PrimTy.inRange, decide_eq_true_eq, IntTy.lo, IntTy.hi,
    IntTy.u256, if_true]
  omega

/-- A genuine value producer, retaining the number and deriving its source
range internally from the model's intrinsic evidence. -/
def ofModel (D : Layout) : (p : PrimTy) → p.Denote → Source.Val D (sourceTy p)
  | .bool, b => .bool b
  | .uint, v => .int v.1 ((uint_range v.1).mp v.2)
  | .int, v => .int v.1 ((int_range v.1).mp v.2)

/-- Every produced value satisfies the typed correspondence. The source value
is computed, not supplied as a desired outcome or a future proof premise. -/
theorem ofModel_related (D : Layout) (p : PrimTy) (v : p.Denote) :
    PrimitiveRel D p (ofModel D p v) v := by
  cases p <;> constructor

/-- The correspondence cannot turn a false source boolean into true. -/
theorem false_not_true (D : Layout) :
    ¬ PrimitiveRel D .bool (.bool false) true := by
  intro h
  cases h

/-- The same number can be an unsigned value but not a signed value.
This is a raw value control, not an execution or compiler fixture. -/
theorem signed_upper_control :
    PrimTy.uint.inRange (2 ^ 255) = true ∧
      PrimTy.int.inRange (2 ^ 255) = false := by
  simp only [PrimTy.inRange, decide_eq_true_eq, decide_eq_false_iff_not]
  omega

end Solidity.Source.Agreement
