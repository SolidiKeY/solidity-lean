import Solidity.Backend.Scalar.Typed

/-! Typed numeric comparisons, including signed opcode selection and the exact
Boolean negation used for non-strict comparisons. -/
namespace Solidity.Backend.Scalar

theorem flag_not_lt (a b : Int) :
    flag (flag (decide (b < a)) == 0) = flag (decide (a ≤ b)) := by
  by_cases h : b < a
  · have hn : ¬ a ≤ b := by omega
    simp only [h, hn, decide_true, decide_false, flag, if_true]
    rfl
  · have hn : a ≤ b := by omega
    simp only [h, hn, decide_true, decide_false, flag, if_true]
    rfl

/-- `uint` lt preserves the intrinsic comparison at every input. -/
def uintLt : BinaryCertificate .lt .uint rfl where
  code := [.op .LT]
  correct := by
    intro a b tail
    change some (flag (decide ((encodeValue .uint a).toNat < (encodeValue .uint b).toNat)) :: tail) = some (flag (decide (a.val < b.val)) :: tail)
    rw [encode_uint_toNat, encode_uint_toNat]
    have ha : 0 ≤ a.val ∧ a.val < ((2 ^ 256 : Nat) : Int) := uint_range a
    have hb : 0 ≤ b.val ∧ b.val < ((2 ^ 256 : Nat) : Int) := uint_range b
    have hc : (a.val.toNat < b.val.toNat) ↔ a.val < b.val := by omega
    simp only [hc]

/-- `uint` gt preserves the intrinsic comparison at every input. -/
def uintGt : BinaryCertificate .gt .uint rfl where
  code := [.op .GT]
  correct := by
    intro a b tail
    change some (flag (decide ((encodeValue .uint b).toNat < (encodeValue .uint a).toNat)) :: tail) = some (flag (decide (b.val < a.val)) :: tail)
    rw [encode_uint_toNat, encode_uint_toNat]
    have ha : 0 ≤ a.val ∧ a.val < ((2 ^ 256 : Nat) : Int) := uint_range a
    have hb : 0 ≤ b.val ∧ b.val < ((2 ^ 256 : Nat) : Int) := uint_range b
    have hc : (b.val.toNat < a.val.toNat) ↔ b.val < a.val := by omega
    simp only [hc]

/-- `uint` le preserves the intrinsic comparison at every input. -/
def uintLe : BinaryCertificate .le .uint rfl where
  code := [.op .GT , .op .ISZERO]
  correct := by
    intro a b tail
    change some (flag (flag (decide ((encodeValue .uint b).toNat < (encodeValue .uint a).toNat)) == 0) :: tail) = some (flag (decide (a.val ≤ b.val)) :: tail)
    rw [encode_uint_toNat, encode_uint_toNat]
    have ha : 0 ≤ a.val ∧ a.val < ((2 ^ 256 : Nat) : Int) := uint_range a
    have hb : 0 ≤ b.val ∧ b.val < ((2 ^ 256 : Nat) : Int) := uint_range b
    have hc : (b.val.toNat < a.val.toNat) ↔ b.val < a.val := by omega
    simp only [hc, flag_not_lt]

/-- `uint` ge preserves the intrinsic comparison at every input. -/
def uintGe : BinaryCertificate .ge .uint rfl where
  code := [.op .LT , .op .ISZERO]
  correct := by
    intro a b tail
    change some (flag (flag (decide ((encodeValue .uint a).toNat < (encodeValue .uint b).toNat)) == 0) :: tail) = some (flag (decide (b.val ≤ a.val)) :: tail)
    rw [encode_uint_toNat, encode_uint_toNat]
    have ha : 0 ≤ a.val ∧ a.val < ((2 ^ 256 : Nat) : Int) := uint_range a
    have hb : 0 ≤ b.val ∧ b.val < ((2 ^ 256 : Nat) : Int) := uint_range b
    have hc : (a.val.toNat < b.val.toNat) ↔ a.val < b.val := by omega
    simp only [hc, flag_not_lt]

/-- `int` lt preserves the intrinsic comparison at every input. -/
def intLt : BinaryCertificate .lt .int rfl where
  code := [.op .SLT]
  correct := by
    intro a b tail
    change some (flag (decide ((encodeValue .int a).toInt < (encodeValue .int b).toInt)) :: tail) = some (flag (decide (a.val < b.val)) :: tail)
    rw [encode_int_toInt, encode_int_toInt]

/-- `int` gt preserves the intrinsic comparison at every input. -/
def intGt : BinaryCertificate .gt .int rfl where
  code := [.op .SGT]
  correct := by
    intro a b tail
    change some (flag (decide ((encodeValue .int b).toInt < (encodeValue .int a).toInt)) :: tail) = some (flag (decide (b.val < a.val)) :: tail)
    rw [encode_int_toInt, encode_int_toInt]

/-- `int` le preserves the intrinsic comparison at every input. -/
def intLe : BinaryCertificate .le .int rfl where
  code := [.op .SGT , .op .ISZERO]
  correct := by
    intro a b tail
    change some (flag (flag (decide ((encodeValue .int b).toInt < (encodeValue .int a).toInt)) == 0) :: tail) = some (flag (decide (a.val ≤ b.val)) :: tail)
    rw [encode_int_toInt, encode_int_toInt]
    rw [flag_not_lt]

/-- `int` ge preserves the intrinsic comparison at every input. -/
def intGe : BinaryCertificate .ge .int rfl where
  code := [.op .SLT , .op .ISZERO]
  correct := by
    intro a b tail
    change some (flag (flag (decide ((encodeValue .int a).toInt < (encodeValue .int b).toInt)) == 0) :: tail) = some (flag (decide (b.val ≤ a.val)) :: tail)
    rw [encode_int_toInt, encode_int_toInt]
    rw [flag_not_lt]

/-- ISZERO on a canonical Boolean word implements Boolean complement. -/
theorem flag_iszero (b : Bool) : flag (flag b == 0) = flag (!b) := by
  cases b <;> rfl

theorem encode_uint_beq (a b : PrimTy.uint.Denote) :
    (encodeValue .uint a == encodeValue .uint b) = decide (a.val = b.val) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    exact congrArg Subtype.val (encode_uint_injective h)
  · intro h
    exact congrArg (encodeValue .uint) (Subtype.ext h)

theorem encode_int_beq (a b : PrimTy.int.Denote) :
    (encodeValue .int a == encodeValue .int b) = decide (a.val = b.val) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    exact congrArg Subtype.val (encode_int_injective h)
  · intro h
    exact congrArg (encodeValue .int) (Subtype.ext h)

/-- Equality selection at every existing intrinsic primitive type. -/
def scalarEq (p : PrimTy) : BinaryCertificate .eqB p (by cases p <;> rfl) where
  code := [.op .EQ]
  correct := by
    intro a b tail
    cases p with
    | bool => exact booleanEq.correct a b tail
    | uint =>
      change some (flag (encodeValue .uint a == encodeValue .uint b) :: tail) = some (flag (decide (a.val = b.val)) :: tail)
      rw [encode_uint_beq]
    | int =>
      change some (flag (encodeValue .int a == encodeValue .int b) :: tail) = some (flag (decide (a.val = b.val)) :: tail)
      rw [encode_int_beq]

/-- Equality selection at every existing intrinsic primitive type. -/
def scalarNe (p : PrimTy) : BinaryCertificate .neB p (by cases p <;> rfl) where
  code := [.op .EQ, .op .ISZERO]
  correct := by
    intro a b tail
    cases p with
    | bool => exact booleanNe.correct a b tail
    | uint =>
      change some (flag (flag (encodeValue .uint a == encodeValue .uint b) == 0) :: tail) = some (flag (!decide (a.val = b.val)) :: tail)
      rw [encode_uint_beq, flag_iszero]
    | int =>
      change some (flag (flag (encodeValue .int a == encodeValue .int b) == 0) :: tail) = some (flag (!decide (a.val = b.val)) :: tail)
      rw [encode_int_beq, flag_iszero]

/-- Signed ordering must not accidentally use unsigned LT. -/
example : run uintLt.code [BitVec.ofInt 256 (-1), 0] = some [0] := by decide +kernel
example : run intLt.code [BitVec.ofInt 256 (-1), 0] = some [1] := by decide +kernel
example : run intLe.code [7, 7, 99] = some [1, 99] := by decide +kernel


/-- info: 'Solidity.Backend.Scalar.uintLt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms uintLt
/-- info: 'Solidity.Backend.Scalar.uintGt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms uintGt
/-- info: 'Solidity.Backend.Scalar.uintLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms uintLe
/-- info: 'Solidity.Backend.Scalar.uintGe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms uintGe
/-- info: 'Solidity.Backend.Scalar.intLt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms intLt
/-- info: 'Solidity.Backend.Scalar.intGt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms intGt
/-- info: 'Solidity.Backend.Scalar.intLe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms intLe
/-- info: 'Solidity.Backend.Scalar.intGe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms intGe


#print axioms scalarEq
#print axioms scalarNe

end Solidity.Backend.Scalar
