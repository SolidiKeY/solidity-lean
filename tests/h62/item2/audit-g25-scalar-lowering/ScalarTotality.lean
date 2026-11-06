import tests.h62.item2.«audit-g25-scalar-lowering».Fixtures

/-! Constructive success and capacity availability for every accepted scalar
operator/type pair, using the actual public selectors and certificates.
These are the frozen gasless component contracts, not full fetched-EVM claims.
Binary operands are already evaluated; no eager short-circuit lowering is inferred. -/
namespace Solidity.Backend.Scalar.H62Audit.Totality
open Solidity
open Solidity.Backend
open Solidity.Backend.Scalar
open Solidity.Backend.Scalar.H62Audit.Fixtures

/-- One concrete, well-ranged operand at every intrinsic primitive type. -/
def operand : (p : PrimTy) → p.Denote
  | .bool => false
  | .uint => u1
  | .int => i1

/-- The Boolean conjunction input deliberately declines short-circuiting. -/
def leftOperand (op : BinOp) : (p : PrimTy) → p.Denote
  | .bool => decide (op = .and)
  | .uint => u1
  | .int => i1

theorem unary_source_isSome (op : UnOp) (p : PrimTy) (h : op.accepts p = true) :
    (op.evalT h (operand p)).isSome = true := by
  cases op <;> cases p <;> first | rfl | cases h

theorem binary_source_isSome (op : BinOp) (p : PrimTy) (h : op.accepts p = true) :
    (op.evalT h (leftOperand op p) (operand p)).isSome = true := by
  cases op <;> cases p <;> first | rfl | cases h

theorem binary_short_declines (op : BinOp) (p : PrimTy) (h : op.accepts p = true) :
    op.shortT (leftOperand op p) = none := by
  cases op <;> cases p <;> first | rfl | cases h

theorem unary_source_success (op : UnOp) (p : PrimTy) (h : op.accepts p = true) :
    ∃ r : (op.ret p).Denote, op.evalT h (operand p) = some r := by
  have success := unary_source_isSome op p h
  cases result : op.evalT h (operand p) with
  | none => rw [result] at success; cases success
  | some r => exact ⟨r, rfl⟩

theorem binary_source_success (op : BinOp) (p : PrimTy) (h : op.accepts p = true) :
    ∃ r : (op.ret p).Denote, op.evalT h (leftOperand op p) (operand p) = some r := by
  have success := binary_source_isSome op p h
  cases result : op.evalT h (leftOperand op p) (operand p) with
  | none => rw [result] at success; cases success
  | some r => exact ⟨r, rfl⟩

/-- No postulated target-success premise: the source-success case is constructed. -/
theorem unary_certificate_success {op : UnOp} {p : PrimTy} {h : op.accepts p = true}
    (c : UnaryCertificate op p h) :
    ∃ r : (op.ret p).Denote, op.evalT h (operand p) = some r ∧
      ∀ tail : Stack, run c.code (encodeValue p (operand p) :: tail) =
        some (encodeValue (op.ret p) r :: tail) := by
  obtain ⟨r, source⟩ := unary_source_success op p h
  refine ⟨r, source, ?_⟩
  intro tail
  rw [c.correct, source]
  rfl

theorem binary_certificate_success {op : BinOp} {p : PrimTy} {h : op.accepts p = true}
    (c : BinaryCertificate op p h) :
    ∃ r : (op.ret p).Denote, op.evalT h (leftOperand op p) (operand p) = some r ∧
      ∀ tail : Stack, run c.code
        (encodeValue p (leftOperand op p) :: encodeValue p (operand p) :: tail) =
        some (encodeValue (op.ret p) r :: tail) := by
  obtain ⟨r, source⟩ := binary_source_success op p h
  refine ⟨r, source, ?_⟩
  intro tail
  rw [c.correct, source]
  rfl

theorem checked_unary_certificate_success {op : UnOp} {p : PrimTy} {h : op.accepts p = true}
    (c : CheckedUnaryCertificate op p h) :
    ∃ r : (op.ret p).Denote, op.evalT h (operand p) = some r ∧
      ∀ tail : Stack, guarded c.test c.body overflowFailure (encodeValue p (operand p) :: tail) =
        some (.ok (encodeValue (op.ret p) r :: tail)) := by
  obtain ⟨r, source⟩ := unary_source_success op p h
  refine ⟨r, source, ?_⟩
  intro tail
  rw [c.correct, source]
  rfl

theorem checked_binary_certificate_success {op : BinOp} {p : PrimTy} {h : op.accepts p = true}
    (c : CheckedCertificate op p h) :
    ∃ r : (op.ret p).Denote, op.evalT h (leftOperand op p) (operand p) = some r ∧
      ∀ tail : Stack, guarded c.test c.body overflowFailure
        (encodeValue p (leftOperand op p) :: encodeValue p (operand p) :: tail) =
        some (.ok (encodeValue (op.ret p) r :: tail)) := by
  obtain ⟨r, source⟩ := binary_source_success op p h
  refine ⟨r, source, ?_⟩
  intro tail
  rw [c.correct, source]
  rfl

theorem unary_reject_all_impossible (op : UnOp) (p : PrimTy) (h : op.accepts p = true) :
    ¬ ∃ c : UnaryCertificate op p h, ∀ st : Stack, run c.code st = none := by
  rintro ⟨c, reject⟩
  obtain ⟨r, _, target⟩ := unary_certificate_success c
  have success := target []
  rw [reject] at success
  cases success

theorem binary_reject_all_impossible (op : BinOp) (p : PrimTy) (h : op.accepts p = true) :
    ¬ ∃ c : BinaryCertificate op p h, ∀ st : Stack, run c.code st = none := by
  rintro ⟨c, reject⟩
  obtain ⟨r, _, target⟩ := binary_certificate_success c
  have success := target []
  rw [reject] at success
  cases success

theorem checked_unary_reject_all_impossible (op : UnOp) (p : PrimTy) (h : op.accepts p = true) :
    ¬ ∃ c : CheckedUnaryCertificate op p h, ∀ st : Stack,
      guarded c.test c.body overflowFailure st = none := by
  rintro ⟨c, reject⟩
  obtain ⟨r, _, target⟩ := checked_unary_certificate_success c
  have success := target []
  rw [reject] at success
  cases success

theorem checked_binary_reject_all_impossible (op : BinOp) (p : PrimTy) (h : op.accepts p = true) :
    ¬ ∃ c : CheckedCertificate op p h, ∀ st : Stack,
      guarded c.test c.body overflowFailure st = none := by
  rintro ⟨c, reject⟩
  obtain ⟨r, _, target⟩ := checked_binary_certificate_success c
  have success := target []
  rw [reject] at success
  cases success

/-- Arbitrary failure payloads cannot disguise always-revert as supported success. -/
theorem checked_unary_always_revert_impossible (op : UnOp) (p : PrimTy) (h : op.accepts p = true) :
    ¬ ∃ (c : CheckedUnaryCertificate op p h) (payload : List UInt8), ∀ st : Stack,
      guarded c.test c.body overflowFailure st = some (.error payload) := by
  rintro ⟨c, payload, revert⟩
  obtain ⟨r, _, target⟩ := checked_unary_certificate_success c
  have success := target []
  rw [revert] at success
  cases success

theorem checked_binary_always_revert_impossible (op : BinOp) (p : PrimTy) (h : op.accepts p = true) :
    ¬ ∃ (c : CheckedCertificate op p h) (payload : List UInt8), ∀ st : Stack,
      guarded c.test c.body overflowFailure st = some (.error payload) := by
  rintro ⟨c, payload, revert⟩
  obtain ⟨r, _, target⟩ := checked_binary_certificate_success c
  have success := target []
  rw [revert] at success
  cases success

/-- Actual selector availability includes capacity, not merely inhabited types. -/
theorem unary_selection_capacity (op : UnOp) (p : PrimTy) (h : op.accepts p = true) :
    (∃ c : UnaryCertificate op p h, selectUnary op p h = some c ∧ stackBound c.code 1 = true) ∨
    (∃ c : CheckedUnaryCertificate op p h, selectCheckedUnary op p h = some c ∧
      stackBound c.test 1 = true ∧ stackBound c.body 1 = true) := by
  cases op <;> cases p <;> cases h <;> first
    | exact Or.inl ⟨_, rfl, by decide +kernel⟩
    | exact Or.inr ⟨_, rfl, by decide +kernel, by decide +kernel⟩
    | cases h

theorem binary_selection_capacity (op : BinOp) (p : PrimTy) (h : op.accepts p = true) :
    (∃ c : BinaryCertificate op p h, selectBinary op p h = some c ∧
      ∀ a b : p.Denote, BinaryInvocation c a b []) ∨
    (∃ c : CheckedCertificate op p h, selectChecked op p h = some c ∧
      ∀ a b : p.Denote, CheckedInvocation c a b []) ∨
    (op = .div ∨ op = .mod) := by
  cases op <;> cases p <;> cases h <;> first
    | exact Or.inl ⟨_, rfl, fun _ _ => ⟨by decide +kernel⟩⟩
    | exact Or.inr (Or.inl ⟨_, rfl, fun _ _ => ⟨by decide +kernel, by decide +kernel⟩⟩)
    | exact Or.inr (Or.inr (Or.inl rfl))
    | exact Or.inr (Or.inr (Or.inr rfl))
    | cases h

theorem modular_certificate_success {op : ModOp} (c : ModularCertificate op) (tail : Stack) :
    guarded c.test c.body divisionFailure
      (encodeValue .uint u1 :: encodeValue .uint u1 :: encodeValue .uint u1 :: tail) =
      some (.ok (encodeValue .uint u0 :: tail)) := by
  cases op <;> exact c.correct u1 u1 u1 tail

theorem modular_selection_capacity (op : ModOp) :
    stackBound (selectModular op).test 3 = true ∧ stackBound (selectModular op).body 3 = true := by
  cases op <;> decide +kernel

theorem modular_always_revert_impossible (op : ModOp) :
    ¬ ∃ (c : ModularCertificate op) (payload : List UInt8), ∀ st : Stack,
      guarded c.test c.body divisionFailure st = some (.error payload) := by
  rintro ⟨c, payload, revert⟩
  have success := modular_certificate_success c []
  rw [revert] at success
  cases success

/-- The fallback arms of binary_selection_coverage also have supported successes. -/
theorem uint_div_positive (tail : Stack) :
    guarded (zeroTest ⟨1, by decide⟩) [.op .DIV] divisionFailure
      (encodeValue .uint u1 :: encodeValue .uint u1 :: tail) =
      some (.ok (encodeValue .uint u1 :: tail)) := uint_div_correct u1 u1 tail

theorem uint_mod_positive (tail : Stack) :
    guarded (zeroTest ⟨1, by decide⟩) [.op .MOD] divisionFailure
      (encodeValue .uint u1 :: encodeValue .uint u1 :: tail) =
      some (.ok (encodeValue .uint u0 :: tail)) := uint_mod_correct u1 u1 tail

theorem int_div_positive (tail : Stack) :
    signedDivExecute (encodeValue .int i1 :: encodeValue .int i1 :: tail) =
      some (.ok (encodeValue .int i1 :: tail)) := int_div_correct i1 i1 tail

theorem int_mod_positive (tail : Stack) :
    guarded (zeroTest ⟨1, by decide⟩) [.op .SMOD] divisionFailure
      (encodeValue .int i1 :: encodeValue .int i1 :: tail) =
      some (.ok (encodeValue .int i0 :: tail)) := int_mod_correct i1 i1 tail

theorem division_components_capacity :
    stackBound (zeroTest ⟨1, by decide⟩) 2 = true ∧
    stackBound signedDivOverflowTest 2 = true ∧
    stackBound [.op .DIV] 2 = true ∧ stackBound [.op .MOD] 2 = true ∧
    stackBound [.op .SDIV] 2 = true ∧ stackBound [.op .SMOD] 2 = true := by decide +kernel

end Solidity.Backend.Scalar.H62Audit.Totality
