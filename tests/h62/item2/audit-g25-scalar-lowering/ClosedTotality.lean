import tests.h62.item2.«audit-g25-scalar-lowering».ScalarTotality

/-! Supported closed programs use the original intrinsic Val constructors and
actual certificate combinators. This does not quantify over unsupported reads,
locations, calls, or short-circuit control compilation. -/
namespace Solidity.Backend.Scalar.H62Audit.Totality
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar

variable {C : Contract} {Γ : Ctx}

def literalExpression : (p : PrimTy) → p.Denote → Val C Γ p
  | .bool, b => .simple (.bool b)
  | .uint, v => .simple (.lit v.val v.property)
  | .int, v => .simple (.lit v.val v.property)

def literalCertificate : (p : PrimTy) → (v : p.Denote) →
    ClosedCertificate (literalExpression (C := C) (Γ := Γ) p v)
  | .bool, b => boolLiteral b
  | .uint, v => numericLiteral .uint v.val v.property
  | .int, v => numericLiteral .int v.val v.property

theorem literal_value (p : PrimTy) (v : p.Denote) :
    (literalCertificate (C := C) (Γ := Γ) p v).value = v := by
  cases p <;> rfl

theorem literal_code (p : PrimTy) (v : p.Denote) :
    (literalCertificate (C := C) (Γ := Γ) p v).code = literal p v := by
  cases p <;> rfl

theorem closed_program_success {p : PrimTy} {e : Val C Γ p}
    (c : ClosedCertificate e) (σ : State C Γ) (tail : Stack) :
    e.evalT σ = .ok c.value ∧ run c.code tail = some (encodeValue p c.value :: tail) :=
  ⟨c.source σ, c.target tail⟩

theorem closed_reject_all_impossible {p : PrimTy} {e : Val C Γ p} :
    ¬ ∃ c : ClosedCertificate e, ∀ tail : Stack, run c.code tail = none := by
  rintro ⟨c, reject⟩
  have success := c.target []
  rw [reject] at success
  cases success

/-- A concrete supported expression exists for every available pure unary arm.
The operation equation is proved from well-ranged data, not assumed. -/
theorem supported_closed_unary (op : UnOp) (p : PrimTy) (h : op.accepts p = true)
    (c : UnaryCertificate op p h) :
    Nonempty (ClosedCertificate (C := C) (Γ := Γ)
      (.unop op h rfl (literalExpression p (operand p)))) := by
  obtain ⟨r, source⟩ := unary_source_success op p h
  refine ⟨(literalCertificate p (operand p)).unary c r ?_⟩
  rw [literal_value]
  exact source

theorem supported_closed_binary (op : BinOp) (p : PrimTy) (h : op.accepts p = true)
    (c : BinaryCertificate op p h) :
    Nonempty (ClosedCertificate (C := C) (Γ := Γ)
      (.binop op h rfl (literalExpression p (leftOperand op p))
        (literalExpression p (operand p)))) := by
  obtain ⟨r, source⟩ := binary_source_success op p h
  refine ⟨(literalCertificate p (leftOperand op p)).binary
    (literalCertificate p (operand p)) c r ?_ ?_⟩
  · rw [literal_value, literal_value]
    exact source
  · rw [literal_value]
    exact binary_short_declines op p h

/-- Actual literal slices are physically feasible at every supported stack tail. -/
theorem literal_capacity (p : PrimTy) (v : p.Denote) (tail : Stack)
    (space : tail.length < 1024) : stackBound (literal p v) (tail.length : Int) = true := by
  simp only [literal, pushWord, stackBound, heightTrace, stackDelta,
    List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    safeHeight, decide_eq_true_eq]
  constructor <;> constructor <;> omega

/-- The excluded physical boundary is an observed failure of the capacity test. -/
theorem literal_full_stack_refused (p : PrimTy) (v : p.Denote) :
    stackBound (literal p v) 1024 = false := by
  simp only [literal, pushWord, stackBound, heightTrace, stackDelta,
    List.all_cons, List.all_nil, safeHeight]
  decide +kernel

end Solidity.Backend.Scalar.H62Audit.Totality
