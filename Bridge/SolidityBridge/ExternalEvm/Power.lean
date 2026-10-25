import SolidityBridge.ExternalEvm.WordOps

namespace Solidity.Evm.External

open private EvmYul.UInt256.powAux from EvmYul.UInt256

/-- The upstream exponentiation-by-squaring algorithm computes modular
power. This proves its algorithm, not merely its chosen test vectors. -/
theorem reference_powAux (a c : EvmYul.UInt256) (n : Nat) :
    (EvmYul.UInt256.powAux a c n).val = a.val * c.val ^ n := by
  induction n using Nat.strong_induction_on generalizing a c with
  | h n ih =>
    cases n with
    | zero => simp only [EvmYul.UInt256.powAux, pow_zero, mul_one]
    | succ n =>
      rw [EvmYul.UInt256.powAux]
      have hlt : (n + 1) / 2 < n + 1 := Nat.div_lt_self (by omega) (by decide)
      split
      · rename_i hodd
        have hod : (n + 1) % 2 = 1 := beq_iff_eq.mp hodd
        rw [ih _ hlt]
        change (a.val * c.val) * (c.val * c.val) ^ ((n + 1) / 2) = _
        have hn : n + 1 = 2 * ((n + 1) / 2) + 1 := by omega
        rw [← pow_two, ← pow_mul]
        conv_rhs => rw [hn, pow_succ]
        ac_rfl
      · rename_i heven
        have hne : (n + 1) % 2 ≠ 1 := by
          intro h
          exact heven (beq_iff_eq.mpr h)
        rw [ih _ hlt]
        change a.val * (c.val * c.val) ^ ((n + 1) / 2) = _
        have hn : n + 1 = 2 * ((n + 1) / 2) := by omega
        rw [← pow_two, ← pow_mul]
        conv_rhs => rw [hn]

theorem reference_pow (a b : EvmYul.UInt256) :
    (EvmYul.UInt256.exp a b).val = a.val ^ b.toNat := by
  change (EvmYul.UInt256.powAux ⟨1⟩ a b.toNat).val = _
  rw [reference_powAux]
  exact one_mul _

open scoped Fin.CommRing in
private theorem fin_pow_value {n : Nat} [NeZero n] (a : Fin n) (b : Nat) :
    (a ^ b).val = a.val ^ b % n := by
  have he : (a.val : Fin n) = a := Fin.ofNat_val_eq_self a
  have hp : (a.val : Fin n) ^ b = a ^ b := congrArg (fun x : Fin n => x ^ b) he
  rw [← hp, ← Nat.cast_pow, Fin.val_natCast]

theorem exp_step (m : Machine) (a b : Fin W) (st : List Word) :
    Instr.exp.step {m with stack := .val a :: .val b :: st} =
      m.next (.val (decode (EvmYul.UInt256.exp (encode a) (encode b))) :: st) := by
  apply congrArg (fun v => m.next (.val v :: st))
  apply Fin.ext
  change (a.val ^ b.val) % W = (EvmYul.UInt256.exp (encode a) (encode b)).val.val
  rw [reference_pow, fin_pow_value]
  change (a.val ^ b.val) % W = (a.val ^ b.val) % EvmYul.UInt256.size
  rw [size_eq]

end Solidity.Evm.External
