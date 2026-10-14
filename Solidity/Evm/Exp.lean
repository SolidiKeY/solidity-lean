import Solidity.Evm.Layout

/-!
# Checked exponentiation

`b ** e` on `uint`s is solc's `checked_exp_unsigned`, whose loop
(`checked_exp_helper`) squares the base and halves the exponent until the
exponent is `1`.  The machine has no backward jumps, but the loop does not need
one: an exponent below `2^256` reaches `1` after at most `255` halvings, so
`expLoop 255` (`Evm/Layout.lean`) is the loop unrolled, each round skipping the
rest once it is done.

`exp_tail` is the result: the code computes `b ^ e`, or reverts exactly when
`b ^ e ≥ 2^256`.  The one fact with content is solc's own argument for its
checks: a round reverts when `bs · bs` overflows, and then so does the result,
since it is at least `pw · bs^2` with the exponent at least `2`; and while
`pw ≤ bs` (true at the start, `pw = 1`, and kept by every round) the product
`pw · bs` needs no check of its own.
-/

namespace Solidity
namespace Evm

/-- One round on words: revert if `bs · bs` overflows, else the halved
exponent, the squared base, and `pw` times `bs` when the exponent is odd. -/
theorem expBody_run (m : Machine) (st : List Word) (ex bs pw : Nat) (hbs : 0 < bs)
    (hex : ex < W) (hbW : bs < W) (hpw : pw < W) :
    run expBody { m with stack := w[ex] :: w[bs] :: w[pw] :: st } =
      if bs * bs < W then
        .ok { m with
          stack := w[ex / 2] :: w[bs * bs % W] ::
            w[if ex % 2 = 0 then pw else pw * bs % W] :: st } 0
      else .revert := by
  have hdiv : (W - 1) / bs < bs ↔ ¬ bs * bs < W := by
    rw [Nat.div_lt_iff_lt_mul hbs]; have := W_pos; omega
  have hb0 : bs ≠ 0 := by omega
  have e1 := Nat.mod_eq_of_lt hex
  have e2 := Nat.mod_eq_of_lt hbW
  have e3 := Nat.mod_eq_of_lt hpw
  have e4 : W - 1 < W := by have := W_pos; omega
  have e5 := Nat.mod_eq_of_lt e4
  have e6 : (2 : Nat) % W = 2 := Nat.mod_eq_of_lt (by unfold W; decide)
  by_cases h : bs * bs < W
  · have h1 : ¬ (W - 1) / bs < bs := fun h' => hdiv.1 h' h
    by_cases h2 : ex % 2 = 0
    · simp [run, expBody, assertTop, Instr.step, Machine.next, h, h1, h2, hb0, bword, wMax,
        e1, e2, e3, e5, e6]
      done
    · simp [run, expBody, assertTop, Instr.step, Machine.next, h, h1, h2, hb0, bword, wMax,
        e1, e2, e3, e5, e6]
      done
  · have h1 : (W - 1) / bs < bs := hdiv.2 h
    simp [run, expBody, assertTop, Instr.step, Machine.next, h, h1, hb0, bword, wMax,
      e1, e2, e3, e5, e6]

/-- Squaring the base halves the exponent: `bs^ex = (bs·bs)^(ex/2) · bs^(ex % 2)`. -/
theorem pow_halve (bs ex : Nat) : bs ^ ex = (bs * bs) ^ (ex / 2) * bs ^ (ex % 2) := by
  conv => lhs; rw [← Nat.div_add_mod ex 2]
  rw [Nat.pow_add, Nat.pow_mul, Nat.pow_two]

/-- The unrolled loop: from `pw ≤ bs` and an exponent below `2^(k+1)`, either
it reverts and `pw · bs^ex` overflows, or it stops at exponent `1` with
`pw' · bs'` the same product and `pw' ≤ bs'` still. -/
theorem expLoop_run (m : Machine) (st : List Word) : ∀ (k ex bs pw : Nat), 1 ≤ ex →
    ex < 2 ^ (k + 1) → (_ : ex < W) → 1 ≤ bs → (_ : bs < W) → 1 ≤ pw → (_ : pw ≤ bs) →
    (W ≤ pw * bs ^ ex ∧
        run (expLoop k) { m with stack := w[ex] :: w[bs] :: w[pw] :: st } = .revert) ∨
      (∃ bs' pw' : Fin W, pw'.1 ≤ bs'.1 ∧ pw'.1 * bs'.1 = pw * bs ^ ex ∧ 1 ≤ pw'.1 ∧
        run (expLoop k) { m with stack := w[ex] :: w[bs] :: w[pw] :: st } =
          .ok { m with stack := w[1] :: .val bs' :: .val pw' :: st } 0)
  | 0, ex, bs, pw, h1, h2, hexW, hb1, hbW, hp1, hpb => by
    obtain rfl : ex = 1 := by simp at h2; omega
    exact .inr ⟨⟨bs, hbW⟩, ⟨pw, by omega⟩, hpb, by simp, hp1, rfl⟩
  | k + 1, ex, bs, pw, h1, h2, hexW, hb1, hbW, hp1, hpb => by
    have guard : run [.push (w[1]), .dup 2, .gt, .iszero,
        .jumpi (expBody.length + (expLoop k).length)]
        { m with stack := w[ex] :: w[bs] :: w[pw] :: st } =
        .ok { m with stack := w[ex] :: w[bs] :: w[pw] :: st }
          (if ex ≤ 1 then expBody.length + (expLoop k).length else 0) := by
      by_cases hex : ex ≤ 1
      · simp [run, Instr.step, Machine.next, bword, hex, show ¬ 1 < ex by omega]
      · simp [run, Instr.step, Machine.next, bword, hex, show 1 < ex by omega]
    rw [expLoop, List.append_assoc, run_append_skip guard]
    by_cases hex : ex ≤ 1
    · obtain rfl : ex = 1 := by omega
      rw [if_pos hex, ← List.length_append]
      exact .inr ⟨⟨bs, hbW⟩, ⟨pw, by omega⟩, hpb, by simp, hp1, exec_length _ _⟩
    · rw [if_neg hex]
      have hb := expBody_run m st ex bs pw (by omega) hexW hbW (by omega)
      simp only [run] at hb
      rw [exec_append, hb]
      by_cases hsq : bs * bs < W
      · simp only [if_pos hsq, Out.ok_bind]
        have hpw : (if ex % 2 = 0 then pw else pw * bs % W) = if ex % 2 = 0 then pw else pw * bs := by
          split
          · rfl
          · rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right bs hpb) hsq)]
        simp only [hpw, Nat.mod_eq_of_lt hsq]
        have hprod : (if ex % 2 = 0 then pw else pw * bs) * (bs * bs) ^ (ex / 2) = pw * bs ^ ex := by
          rw [pow_halve bs ex]
          split
          · rename_i h; rw [h, Nat.pow_zero, Nat.mul_one]
          · rename_i h
            rw [show ex % 2 = 1 by omega, Nat.pow_one, Nat.mul_comm ((bs * bs) ^ (ex / 2)) bs,
              ← Nat.mul_assoc]
        have hle : (if ex % 2 = 0 then pw else pw * bs) ≤ bs * bs := by
          split
          · exact Nat.le_trans hpb (Nat.le_mul_of_pos_left bs (by omega))
          · exact Nat.mul_le_mul_right bs hpb
        have hge : 1 ≤ (if ex % 2 = 0 then pw else pw * bs) := by
          split
          · exact hp1
          · exact Nat.mul_pos hp1 (by omega)
        have hk : ex / 2 < 2 ^ (k + 1) := by
          rw [Nat.pow_succ] at h2; omega
        rcases expLoop_run m st k (ex / 2) (bs * bs) _ (by omega) hk (by omega) (Nat.mul_pos hb1 hb1) hsq
          hge hle with ⟨hW, hrun⟩ | ⟨bs', pw', h2', he, h1', hrun⟩
        · exact .inl ⟨by rw [← hprod]; exact hW, hrun⟩
        · exact .inr ⟨bs', pw', h2', he.trans hprod, h1', hrun⟩
      · simp only [if_neg hsq, Out.revert_bind]
        refine .inl ⟨?_, trivial⟩
        have : bs ^ 2 ≤ bs ^ ex := Nat.pow_le_pow_right (by omega) (by omega)
        rw [Nat.pow_two] at this
        have := Nat.le_mul_of_pos_left (bs ^ ex) (show 0 < pw by omega)
        omega

/-- The last multiplication, checked: `pw > (2^256 - 1) / bs` reverts. -/
theorem expLast_run (m : Machine) (st : List Word) (bs pw : Nat) (hbs : 0 < bs) (hbW : bs < W)
    (hpw : pw < W) :
    run ([.pop, .dup 1, .push (.val wMax), .div, .dup 3, .gt, .iszero] ++ (assertTop ++ [.mul]))
      { m with stack := w[1] :: w[bs] :: w[pw] :: st } =
      if _ : pw * bs < W then .ok { m with stack := w[pw * bs] :: st } 0 else .revert := by
  have hdiv : (W - 1) / bs < pw ↔ ¬ pw * bs < W := by
    rw [Nat.div_lt_iff_lt_mul hbs]; have := W_pos; omega
  have hb0 : bs ≠ 0 := by omega
  by_cases h : pw * bs < W
  · have h1 : ¬ (W - 1) / bs < pw := fun h' => hdiv.1 h' h
    simp [run, assertTop, Instr.step, Machine.next, h, h1, hb0, bword]
    rw [Nat.mul_comm, Nat.mod_eq_of_lt h]
  · have h1 : (W - 1) / bs < pw := hdiv.2 h
    simp [run, assertTop, Instr.step, Machine.next, h, h1, hb0, bword]

/-- `b ** e` for a nonzero base and exponent: the loop and the last
multiplication. -/
theorem expGeneral_run (m : Machine) (st : List Word) {a b : Nat} (ha : 1 ≤ a) (haW : a < W)
    (hb : 1 ≤ b) (hbW : b < W) :
    run expGeneral { m with stack := w[b] :: w[a] :: st } =
      if _ : a ^ b < W then .ok { m with stack := w[a ^ b] :: st } 0 else .revert := by
  simp only [expGeneral, List.append_assoc]
  rw [run_append_ok (m' := { m with stack := w[b] :: w[a] :: w[1] :: st }) rfl]
  rcases expLoop_run m st 255 b a 1 hb (by unfold W at hbW; exact hbW) hbW ha haW (Nat.le_refl 1) ha
    with ⟨hW, hrun⟩ | ⟨⟨bs', h3⟩, ⟨pw', hpw'⟩, h2, he, h1, hrun⟩
  · rw [run_append_revert hrun, dif_neg (by omega)]
  · rw [run_append_ok hrun, expLast_run m st bs' pw' (by simp only at h1 h2; omega) h3 hpw']
    simp only at he
    simp only [he, Nat.one_mul]

/-- `b ** e` for `e ≥ 1`: `0` for a zero base. -/
theorem expNonzero_run (m : Machine) (st : List Word) {a b : Nat} (haW : a < W)
    (hb : 1 ≤ b) (hbW : b < W) :
    run expNonzero { m with stack := w[b] :: w[a] :: st } =
      if _ : a ^ b < W then .ok { m with stack := w[a ^ b] :: st } 0 else .revert := by
  by_cases ha : a = 0
  · subst ha
    simp only [Nat.zero_pow (show 0 < b by omega), dif_pos W_pos]
    rw [expNonzero, List.append_assoc,
      run_append_skip (m' := { m with stack := w[b] :: w[0] :: st })
        (k := expGeneral.length + 1) (by simp [run, Instr.step, Machine.next, bword]),
      exec_skip_append]
    rfl
  · rw [expNonzero, List.append_assoc,
      run_append_ok (m' := { m with stack := w[b] :: w[a] :: st })
        (by simp [run, Instr.step, Machine.next, bword, ha])]
    have hg := expGeneral_run m st (by omega) haW hb hbW
    by_cases h : a ^ b < W
    · rw [dif_pos h] at hg ⊢; rw [run_append_ok hg]; rfl
    · rw [dif_neg h] at hg ⊢; exact run_append_revert hg

/-- **`a ** b` is solc's checked exponentiation**: `a ^ b`, or a revert exactly
when it overflows.  `2 ** 255` fits, `2 ** 256` reverts, `0 ** 0` is `1`. -/
theorem exp_tail (m : Machine) (st : List Word) {a b : Nat} (haW : a < W) (hbW : b < W) :
    run (uTail .pow) { m with stack := w[b] :: w[a] :: st } =
      if _ : a ^ b < W then .ok { m with stack := w[a ^ b] :: st } 0 else .revert := by
  show run expCode _ = _
  by_cases hb : b = 0
  · subst hb
    simp only [Nat.pow_zero, dif_pos (show 1 < W by unfold W; decide)]
    rw [expCode, List.append_assoc,
      run_append_skip (m' := { m with stack := w[0] :: w[a] :: st })
        (k := expNonzero.length + 1) (by simp [run, Instr.step, Machine.next, bword]),
      exec_skip_append]
    rfl
  · rw [expCode, List.append_assoc,
      run_append_ok (m' := { m with stack := w[b] :: w[a] :: st })
        (by simp [run, Instr.step, Machine.next, bword, hb])]
    have hg := expNonzero_run m st haW (by omega) hbW
    by_cases h : a ^ b < W
    · rw [dif_pos h] at hg ⊢; rw [run_append_ok hg]; rfl
    · rw [dif_neg h] at hg ⊢; exact run_append_revert hg

end Evm
end Solidity
