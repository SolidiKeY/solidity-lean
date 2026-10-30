import Solidity.Backend.Scalar.Slice
import Solidity.Semantics.Ops

/-!
# Typed scalar selection certificates

Certificates refer directly to the existing intrinsic operation denotations.
Operands are already evaluated values: the binary Boolean certificates do not
justify eager evaluation of short-circuiting source expressions. The target
relation is the independent numeric slice, not the old symbolic EVM machine.
-/
namespace Solidity.Backend.Scalar

/-- Preserve the existing ABI-word observation, including signed two's complement. -/
def encodeValue : (p : PrimTy) → p.Denote → Word
  | .bool, b => flag b
  | .uint, v => BitVec.ofInt 256 v.val
  | .int, v => BitVec.ofInt 256 v.val

def ValueRel (p : PrimTy) (v : p.Denote) (w : Word) : Prop :=
  w = encodeValue p v

theorem uint_range (v : PrimTy.uint.Denote) :
    0 ≤ v.val ∧ v.val < ((2 ^ 256 : Nat) : Int) := by
  have h : PrimTy.uint.inRange v.val = true := v.property
  simpa only [PrimTy.inRange, decide_eq_true_eq] using h

theorem int_range (v : PrimTy.int.Denote) :
    -((2 ^ 255 : Nat) : Int) ≤ v.val ∧ v.val < ((2 ^ 255 : Nat) : Int) := by
  have h : PrimTy.int.inRange v.val = true := v.property
  simpa only [PrimTy.inRange, decide_eq_true_eq] using h

theorem encode_uint_toNat (v : PrimTy.uint.Denote) :
    (encodeValue .uint v).toNat = v.val.toNat := by
  simp only [encodeValue, BitVec.toNat_ofInt,
    Int.emod_eq_of_lt (uint_range v).1 (uint_range v).2]

theorem encode_int_toInt (v : PrimTy.int.Denote) :
    (encodeValue .int v).toInt = v.val := by
  apply BitVec.toInt_ofInt_eq_self (by decide)
  · simpa only [Int.natCast_pow] using (int_range v).1
  · simpa only [Int.natCast_pow] using (int_range v).2

/-- The signed value representation is injective on intrinsic inputs. -/
theorem encode_int_injective {a b : PrimTy.int.Denote}
    (h : encodeValue .int a = encodeValue .int b) : a = b := by
  apply Subtype.ext
  have h' : (encodeValue .int a).toInt = (encodeValue .int b).toInt :=
    congrArg BitVec.toInt h
  simpa only [encode_int_toInt] using h'

theorem encode_uint_injective {a b : PrimTy.uint.Denote}
    (h : encodeValue .uint a = encodeValue .uint b) : a = b := by
  apply Subtype.ext
  have h' : (encodeValue .uint a).toNat = (encodeValue .uint b).toNat :=
    congrArg BitVec.toNat h
  rw [encode_uint_toNat, encode_uint_toNat] at h'
  have ha : 0 ≤ a.val ∧ a.val < ((2 ^ 256 : Nat) : Int) := uint_range a
  have hb : 0 ≤ b.val ∧ b.val < ((2 ^ 256 : Nat) : Int) := uint_range b
  omega

/-- The arithmetic encoding agrees with the existing intrinsic ABI-word
observation; signed negative values do not acquire a second interpretation. -/
theorem encodeValue_toWord (p : PrimTy) (v : p.Denote) :
    encodeValue p v = BitVec.ofInt 256 (PrimTy.toWord v).val := by
  cases p with
  | bool => cases v <;> rfl
  | uint => rfl
  | int =>
    by_cases hn : 0 ≤ v.val
    · simp only [encodeValue, PrimTy.toWord, hn, dite_true]
    · have hW : (2 : Int) ^ 256 = ((2 ^ 256 : Nat) : Int) :=
        (Int.natCast_pow 2 256).symm
      apply BitVec.eq_of_toNat_eq
      simp only [encodeValue, PrimTy.toWord, hn, dite_false, BitVec.toNat_ofInt, hW,
        Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod]

/-- Literal selection, normalized at the typed ABI-word boundary. -/
def literal (p : PrimTy) (v : p.Denote) : Program := [pushWord (encodeValue p v)]

theorem literal_correct (p : PrimTy) (v : p.Denote) (tail : Stack) :
    run (literal p v) tail = some (encodeValue p v :: tail) := by
  rw [literal, run, step_pushWord]
  rfl

/-- Unary operation certificate, with the original source definedness retained. -/
structure UnaryCertificate (op : UnOp) (p : PrimTy) (h : op.accepts p = true) where
  code : Program
  correct : ∀ (v : p.Denote) (tail : Stack),
    run code (encodeValue p v :: tail) =
      (op.evalT h v).map (fun r => encodeValue (op.ret p) r :: tail)

/-- Binary operation certificate: top word is the left source operand. -/
structure BinaryCertificate (op : BinOp) (p : PrimTy) (h : op.accepts p = true) where
  code : Program
  correct : ∀ (a b : p.Denote) (tail : Stack),
    run code (encodeValue p a :: encodeValue p b :: tail) =
      (op.evalT h a b).map (fun r => encodeValue (op.ret p) r :: tail)

/-- Boolean negation lowers to ISZERO on canonical Boolean words. -/
def booleanNot : UnaryCertificate .not .bool rfl where
  code := [.op .ISZERO]
  correct := by
    intro b tail
    cases b <;> rfl

/-- Boolean conjunction on already evaluated values lowers to AND. -/
def booleanAnd : BinaryCertificate .and .bool rfl where
  code := [.op .AND]
  correct := by
    intro a b tail
    cases a <;> cases b <;> rfl

/-- Boolean disjunction on already evaluated values lowers to OR. -/
def booleanOr : BinaryCertificate .or .bool rfl where
  code := [.op .OR]
  correct := by
    intro a b tail
    cases a <;> cases b <;> rfl

/-- Boolean equality preserves the original operation's denotation. -/
def booleanEq : BinaryCertificate .eqB .bool rfl where
  code := [.op .EQ]
  correct := by
    intro a b tail
    cases a <;> cases b <;> rfl

/-- Inequality is EQ followed by ISZERO. -/
def booleanNe : BinaryCertificate .neB .bool rfl where
  code := [.op .EQ, .op .ISZERO]
  correct := by
    intro a b tail
    cases a <;> cases b <;> rfl

/-- Concrete emitted-byte observation, through the real Backend encoder. -/
theorem booleanNe_bytes : Backend.encode booleanNe.code = [0x14, 0x15] := rfl

theorem booleanNot_bytes : Backend.encode booleanNot.code = [0x15] := rfl

/-- Inhabited sequence/tail control combines a literal, equality and negation. -/
example (tail : Stack) :
    run (literal .bool true ++ literal .bool false ++ booleanNe.code) tail =
      some (encodeValue .bool true :: tail) := by
  rw [List.append_assoc, run_append, literal_correct]
  change run (literal .bool false ++ booleanNe.code) (encodeValue .bool true :: tail) = _
  rw [run_append, literal_correct]
  exact booleanNe.correct false true tail

/-- Noncanonical Boolean input does not satisfy the typed value relation. -/
example : ¬ ValueRel .bool true (BitVec.ofNat 256 2) := by
  unfold ValueRel
  decide +kernel

/-- info: 'Solidity.Backend.Scalar.literal_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms literal_correct
/-- info: 'Solidity.Backend.Scalar.booleanNot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms booleanNot
/-- info: 'Solidity.Backend.Scalar.booleanAnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms booleanAnd
/-- info: 'Solidity.Backend.Scalar.booleanOr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms booleanOr
/-- info: 'Solidity.Backend.Scalar.booleanEq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms booleanEq
/-- info: 'Solidity.Backend.Scalar.booleanNe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms booleanNe


/-- info: 'Solidity.Backend.Scalar.encode_uint_toNat' depends on axioms: [propext] -/
#guard_msgs in #print axioms encode_uint_toNat
/-- info: 'Solidity.Backend.Scalar.encode_int_toInt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms encode_int_toInt
/-- info: 'Solidity.Backend.Scalar.encode_int_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms encode_int_injective
/-- info: 'Solidity.Backend.Scalar.encode_uint_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms encode_uint_injective


#print axioms encodeValue_toWord

end Solidity.Backend.Scalar
