import Solidity.Backend.PrimitivePackets.SignedCast.Selected
import Solidity.Backend.Passes.ValueCertificate
import Solidity.Backend.Scalar.ArithmeticWidths

/-! Complete selected compiler state and a distinct SIGNEXTEND slice. The
compiler expands the typed conditional; it is not claimed to emit SIGNEXTEND. -/
namespace Solidity.Backend.PrimitivePackets.SignedCast
open Evm Evm.Memory Solidity.Lowering.V07

theorem target_success (fromBits bits : Nat) (hf : Valid fromBits) (ht : Valid bits)
    {C : Contract} {Γ : Ctx} (s : State C Γ) (i : Idx Γ (.val .int))
    (x : Int) (hx : (ty fromBits hf).lo ≤ x ∧ x ≤ (ty fromBits hf).hi)
    (read : TEnv.get i s.env = integerValue (ty fromBits hf) x hx)
    {offset L frame : Nat} {F : Frag Γ} {base : Nat → Fin W} {m : Machine}
    (represented : StateRepr L offset frame F s base m) (tail : List Word) :
    ∃ word, ReprV .int (integerValue (ty bits ht) ((ty bits ht).wrap x)
        ((ty bits ht).wrap_mem x)) word ∧
      run (selected (C:=C) bits ht offset F i).code {m with stack := tail} =
        .ok ({m with stack := tail}.push word) 0 := by
  have actual := SignedWidthCasts.value_run fromBits hf s bits ht
    (.simple (.local i)) x hx (by
      change Except.ok (TEnv.get i s.env) = _
      rw [read])
  exact Backend.Passes.value_success_tail (selected (C:=C) bits ht offset F i)
    represented actual tail

/-- Actual native scalar SIGNEXTEND execution, including arbitrary saved tail. -/
theorem signextend (width : Fin 32) (x : Int) (tail : Backend.Scalar.Stack) :
    Backend.Scalar.run (Backend.Scalar.signedCode width) (BitVec.ofInt 256 x :: tail) =
      some (Backend.Scalar.wrapSigned width x :: tail) := by
  simp only [Backend.Scalar.signed_correct, Backend.Scalar.clean_ofInt_signed]

/-- SIGNEXTEND's word is exactly the existing Source wrap, not merely another
normalization function with a similar name. -/
theorem signextend_source (w : Fin 32) (valid : Valid (Backend.Scalar.widthBits w))
    (x : Int) (tail : Backend.Scalar.Stack) :
    Backend.Scalar.run (Backend.Scalar.signedCode w) (BitVec.ofInt 256 x :: tail) =
      some (BitVec.ofInt 256 ((ty (Backend.Scalar.widthBits w) valid).wrap x) :: tail) := by
  rw [signextend]
  have nonneg : 0 ≤ x % ((2 ^ Backend.Scalar.widthBits w : Nat) : Int) :=
    Int.emod_nonneg x (by
      have h : 0 < (2 ^ Backend.Scalar.widthBits w : Nat) := Nat.pow_pos (by decide)
      omega)
  have same : Backend.Scalar.wrapSigned w x =
      BitVec.ofInt 256 ((ty (Backend.Scalar.widthBits w) valid).wrap x) := by
    rw [SignedWidthCasts.wrap_eq]
    unfold Backend.Scalar.wrapSigned Backend.Scalar.widthResidue
    dsimp only
    apply congrArg (BitVec.ofInt 256)
    split <;> split <;> omega
  rw [same]

#print axioms target_success
#print axioms signextend_source
end Solidity.Backend.PrimitivePackets.SignedCast
