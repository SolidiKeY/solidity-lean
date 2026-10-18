import Solidity.Calculus.LinearCountermodel
import Solidity.Semantics.Value

/-!
# Exact scalar codes for arithmetic assignments

The solver assigns natural numbers, whereas Solidity has booleans,
unsigned words and signed words. Codes range over two booleans or 2^256
word values. Signed values are translated by 2^255; decoding checks the
code's range before producing a typed value. No out-of-range solver value
is silently converted to a default or wrapped machine word.
-/

namespace Solidity.Linear

namespace ScalarCode

/-- The size of each primitive value domain. -/
def bound : PrimTy → Nat
  | .bool => 2
  | .uint | .int => 2 ^ 256

/-- A finite natural code retains the primitive type's domain. -/
abbrev Code (p : PrimTy) := Fin (bound p)

/-- Encode typed values, shifting a signed word into a nonnegative code. -/
def encode : (p : PrimTy) → p.Denote → Code p
  | .bool, b => ⟨if b = true then 1 else 0, by cases b <;> decide⟩
  | .uint, v => ⟨v.val.toNat, by
      have h := v.property
      simp only [PrimTy.inRange, decide_eq_true_eq] at h
      change v.val.toNat < 2 ^ 256
      omega⟩
  | .int, v => ⟨(v.val + ((2 ^ 255 : Nat) : Int)).toNat, by
      have h := v.property
      simp only [PrimTy.inRange, decide_eq_true_eq] at h
      have hp : ((2 ^ 256 : Nat) : Int) = 2 * ((2 ^ 255 : Nat) : Int) := by decide +kernel
      change (v.val + ((2 ^ 255 : Nat) : Int)).toNat < 2 ^ 256
      omega⟩

/-- Decode a range-checked code directly into an intrinsic typed value. -/
def decode : (p : PrimTy) → Code p → p.Denote
  | .bool, n => decide (n.val = 1)
  | .uint, n => ⟨(n.val : Int), by
      simp only [PrimTy.inRange, decide_eq_true_eq]
      have h := n.isLt
      change n.val < 2 ^ 256 at h
      omega⟩
  | .int, n => ⟨(n.val : Int) - ((2 ^ 255 : Nat) : Int), by
      simp only [PrimTy.inRange, decide_eq_true_eq]
      have h := n.isLt
      change n.val < 2 ^ 256 at h
      have hp : ((2 ^ 256 : Nat) : Int) = 2 * ((2 ^ 255 : Nat) : Int) := by decide +kernel
      omega⟩

/-- Decoding an encoded typed value is exact at every primitive type. -/
theorem decode_encode (p : PrimTy) (v : p.Denote) : decode p (encode p v) = v := by
  cases p with
  | bool => cases v <;> rfl
  | uint =>
    apply Subtype.ext
    change (v.val.toNat : Int) = v.val
    have h := v.property
    simp only [PrimTy.inRange, decide_eq_true_eq] at h
    omega
  | int =>
    apply Subtype.ext
    change ((v.val + ((2 ^ 255 : Nat) : Int)).toNat : Int) - ((2 ^ 255 : Nat) : Int) = v.val
    have h := v.property
    simp only [PrimTy.inRange, decide_eq_true_eq] at h
    omega

/-- Every code represents a distinct typed value; no bounded value is lost. -/
theorem encode_decode (p : PrimTy) (n : Code p) : encode p (decode p n) = n := by
  cases p with
  | bool =>
    apply Fin.ext
    change (if decide (n.val = 1) = true then 1 else 0) = n.val
    have h : n.val < 2 := n.isLt
    split <;> simp_all only [decide_eq_true_eq]
    all_goals omega
  | uint =>
    apply Fin.ext
    rfl
  | int =>
    apply Fin.ext
    change ((n.val : Int) - ((2 ^ 255 : Nat) : Int) + ((2 ^ 255 : Nat) : Int)).toNat = n.val
    omega

/-- Equality of primitive values is exactly equality of their scalar codes. -/
theorem encode_val_eq_iff (p : PrimTy) (a b : p.Denote) :
    (encode p a).val = (encode p b).val ↔ a = b := by
  constructor
  · intro h
    have he : encode p a = encode p b := Fin.ext h
    have hd : decode p (encode p a) = decode p (encode p b) := congrArg (decode p) he
    simpa only [decode_encode] using hd
  · rintro rfl; rfl

/-- An untrusted arithmetic assignment must pass the type's range test. -/
def decode? (p : PrimTy) (n : Nat) : Option p.Denote :=
  if h : n < bound p then some (decode p ⟨n, h⟩) else none

theorem decode?_isSome (p : PrimTy) (n : Nat) :
    (decode? p n).isSome = true ↔ n < bound p := by
  unfold decode?
  split <;> simp_all only [Option.isSome_some, Option.isSome_none, Bool.false_eq_true]

/-- Encoding any typed value supplies an accepted arithmetic assignment. -/
theorem decode?_encode (p : PrimTy) (v : p.Denote) :
    decode? p (encode p v).val = some v := by
  rw [decode?, dif_pos (encode p v).isLt, decode_encode]

/-- A successful decode identifies the exact original natural assignment. -/
theorem encode_of_decode? (p : PrimTy) (n : Nat) (v : p.Denote)
    (h : decode? p n = some v) : (encode p v).val = n := by
  unfold decode? at h
  split at h
  · cases h
    exact congrArg Fin.val (encode_decode p _)
  · cases h

end ScalarCode

/-- A numbered variable as a linear coefficient vector. -/
def Lin.basis : Nat → Lin
  | 0 => [1]
  | k + 1 => 0 :: Lin.basis k

theorem Lin.eval_basis (k : Nat) (x : Nat → Nat) : (Lin.basis k).eval x = (x k : Int) := by
  induction k generalizing x with
  | zero => simp only [basis, eval, Int.one_mul, Int.add_zero]
  | succ k ih =>
    rw [basis, eval, Int.zero_mul, Int.zero_add, ih]
    rfl

/-- The exact domain constraint for one typed arithmetic variable. -/
def ScalarCode.range (p : PrimTy) (k : Nat) : AFml :=
  .le (Lin.basis k) ((ScalarCode.bound p : Int) - 1)

theorem ScalarCode.range_holds_iff (p : PrimTy) (k : Nat) (x : Nat → Nat) :
    (range p k).holds x ↔ x k < bound p := by
  rw [range, AFml.holds, Lin.eval_basis]
  omega

/-- Domain constraints are precisely successful typed decoding, not an
approximation to the bounded domain. -/
theorem ScalarCode.range_decode_iff (p : PrimTy) (k : Nat) (x : Nat → Nat) :
    (range p k).holds x ↔ (decode? p (x k)).isSome = true :=
  (range_holds_iff p k x).trans (decode?_isSome p (x k)).symm

end Solidity.Linear
