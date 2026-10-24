import SolidityBridge.Arith.Shifts
import SolidityBridge.Arith.NarrowBitwise

namespace Solidity.Bridge.Arith
open Widths

/-- Logical right shift keeps the full unsigned count, independently of the base width. -/
theorem uint_shr_all_widths {n : Nat} (hn : n ≤ 256) (x : BitVec n)
    (y : PrimTy.uint.Denote) :
    (BinOp.shr.evalT rfl (unsignedN hn x) y).map Subtype.val =
      some ((x >>> y.val.toNat).toNat : Int) := by
  rw [uint_shr_bitvec, unsignedN_word, ← BitVec.setWidth_ushiftRight hn, unsignedN_extend hn]

/-- Arithmetic right shift uses the core's Int.toNat count policy. -/
theorem int_shr_all_widths {n : Nat} (hn : n ≤ 256) (x : BitVec n)
    (y : PrimTy.int.Denote) :
    (BinOp.shr.evalT rfl (signedN hn x) y).map Subtype.val =
      some ((x.sshiftRight y.val.toNat).toInt) := by
  rw [int_shr_nat_bitvec, signedN_word, BitVec.toInt_sshiftRight,
    BitVec.toInt_signExtend_of_le hn, BitVec.toInt_sshiftRight]

/-- The source's narrow left-shift cut, including all large counts and operand failures. -/
theorem uint_shl_all_widths {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (n : Nat) (hn : n ≤ 256) (v w : Val C Γ .uint) :
    ((cutUInt n (.binop .shl rfl rfl v w)).evalT σ).map Subtype.val =
      (v.evalT σ >>= fun x => w.evalT σ >>= fun y =>
        .ok ((BitVec.ofInt n x.val <<< y.val.toNat).toNat : Int)) := by
  rw [cutUInt_eval σ n hn]
  cases hx : v.evalT σ with
  | error e => simp only [Val.evalT.eq_3, hx, bind, Except.bind]
  | ok x =>
    cases hy : w.evalT σ with
    | error e => simp only [Val.evalT.eq_3, hx, hy, BinOp.shortT, bind, Except.bind]
    | ok y =>
      obtain ⟨r, hr, hv⟩ := uint_value_of_map _ _ (uint_shl_bitvec x y)
      simp only [Val.evalT.eq_3, hx, hy, BinOp.shortT, ok_bind]
      rw [hr]
      simp only [TRes.ofOpt, ok_bind]
      rw [hv, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
        BitVec.setWidth_shiftLeft_of_le hn, setWidth_full_word n hn]

end Solidity.Bridge.Arith

#print axioms Solidity.Bridge.Arith.uint_shr_all_widths
#print axioms Solidity.Bridge.Arith.int_shr_all_widths
#print axioms Solidity.Bridge.Arith.uint_shl_all_widths
