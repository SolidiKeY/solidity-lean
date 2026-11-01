import Solidity.Backend.Scalar.Typed
import Solidity.Backend.Scalar.Widths

/-! Wrapping arithmetic certificates against existing intrinsic operations.
Narrow cleanup composition is separate from the frontend's width-expansion
proof, which is not asserted here. -/
namespace Solidity.Backend.Scalar

/-- Source reduction modulo the word bound always produces an intrinsic uint;
encoding it preserves the mathematical result modulo exactly that bound. -/
theorem encoded_mod (n : Int) (tail : Stack) :
    (PrimTy.uint.ofInt? (n % Semantics.uintBound)).map
      (fun v => encodeValue .uint v :: tail) = some (BitVec.ofInt 256 n :: tail) := by
  have hp : (0 : Int) < Semantics.uintBound := by decide
  have hn : PrimTy.uint.inRange (n % Semantics.uintBound) = true := by
    apply decide_eq_true
    exact ⟨Int.emod_nonneg n (by omega), Int.emod_lt_of_pos n hp⟩
  simp only [PrimTy.ofInt?, hn, dite_true, Option.map_some, encodeValue]
  have he : BitVec.ofInt 256 (n % Semantics.uintBound) = BitVec.ofInt 256 n := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofInt, Semantics.uintBound, Int.emod_emod]
  rw [he]

/-- `addW` lowers to the actual Osaka ADD, including word overflow. -/
def wrappingAdd : BinaryCertificate .addW .uint rfl where
  code := [.op .ADD]
  correct := by
    intro a b tail
    change some ((BitVec.ofInt 256 a.val + BitVec.ofInt 256 b.val) :: tail) =
      (PrimTy.uint.ofInt? ((a.val + b.val) % Semantics.uintBound)).map
        (fun v => encodeValue .uint v :: tail)
    rw [encoded_mod]
    rw [← BitVec.ofInt_add]

/-- `subW` lowers to the actual Osaka SUB, including word overflow. -/
def wrappingSub : BinaryCertificate .subW .uint rfl where
  code := [.op .SUB]
  correct := by
    intro a b tail
    change some ((BitVec.ofInt 256 a.val - BitVec.ofInt 256 b.val) :: tail) =
      (PrimTy.uint.ofInt? ((a.val - b.val) % Semantics.uintBound)).map
        (fun v => encodeValue .uint v :: tail)
    rw [encoded_mod]
    rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

/-- `mulW` lowers to the actual Osaka MUL, including word overflow. -/
def wrappingMul : BinaryCertificate .mulW .uint rfl where
  code := [.op .MUL]
  correct := by
    intro a b tail
    change some ((BitVec.ofInt 256 a.val * BitVec.ofInt 256 b.val) :: tail) =
      (PrimTy.uint.ofInt? ((a.val * b.val) % Semantics.uintBound)).map
        (fun v => encodeValue .uint v :: tail)
    rw [encoded_mod]
    rw [← BitVec.ofInt_mul]

/-- The source word-preserving unsigned cast after wrapping can be followed
by cleanup at every intrinsic byte width, with the same untouched tail. -/
theorem wrappingAdd_narrow (w : Fin 32) (a b : Word) (tail : Stack) :
    run (wrappingAdd.code ++ unsignedCode w) (a :: b :: tail) =
      some (unsignedClean w (a + b) :: tail) := by
  exact run_comp (p := wrappingAdd.code) (q := unsignedCode w)
    (t := (a + b) :: tail) rfl (unsigned_correct w (a + b) tail)

theorem wrappingAdd_signed (w : Fin 32) (a b : Word) (tail : Stack) :
    run (wrappingAdd.code ++ signedCode w) (a :: b :: tail) =
      some (signedClean w (a + b) :: tail) := by
  exact run_comp (p := wrappingAdd.code) (q := signedCode w)
    (t := (a + b) :: tail) rfl (signed_correct w (a + b) tail)

example : run (wrappingAdd.code ++ unsignedCode ⟨0, by decide⟩) [255, 1, 99] =
    some [0, 99] := by decide +kernel
example : run wrappingAdd.code [255, 1, 99] ≠ some [0, 99] := by decide +kernel
example : run (wrappingAdd.code ++ signedCode ⟨0, by decide⟩) [127, 1, 99] =
    some [BitVec.ofInt 256 (-128), 99] := by decide +kernel

/-- info: 'Solidity.Backend.Scalar.encoded_mod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms encoded_mod
/-- info: 'Solidity.Backend.Scalar.wrappingAdd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms wrappingAdd
/-- info: 'Solidity.Backend.Scalar.wrappingSub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms wrappingSub
/-- info: 'Solidity.Backend.Scalar.wrappingMul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms wrappingMul

end Solidity.Backend.Scalar
