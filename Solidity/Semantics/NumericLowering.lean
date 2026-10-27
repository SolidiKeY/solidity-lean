import Solidity.Semantics.Ops
import Solidity.Syntax.Numeric
import Solidity.Semantics.Run

/-! Arithmetic justification of signed numeric lowering through existing typed
word operations. These lemmas concern numbers, not source/compiler equivalence. -/
namespace Solidity.NumericLowering

theorem neg_pow (m : Int) (n : Nat) :
    (-m)^n = if n % 2 = 0 then m^n else -(m^n) := by
  induction n with
  | zero => simp only [Int.pow_zero, Nat.zero_mod, if_true]
  | succ n ih =>
    rw [Int.pow_succ, ih, Int.pow_succ]
    have hmod := Nat.mod_lt n (by decide : 0 < 2)
    have hsucc := Nat.mod_lt (n+1) (by decide : 0 < 2)
    by_cases h : n % 2 = 0
    · have hs : ¬ (n+1) % 2 = 0 := by omega
      simp only [h, hs, if_true, if_false, Int.mul_neg]
    · have hs : (n+1) % 2 = 0 := by omega
      simp only [h, hs, if_true, if_false, Int.neg_mul_neg]

theorem power_sign (a : Int) (n : Nat) :
    a^n = if a < 0 ∧ n % 2 = 1 then -((a.natAbs : Int)^n) else (a.natAbs : Int)^n := by
  by_cases ha : a < 0
  · conv => lhs; rw [Int.eq_neg_natAbs_of_nonpos (Int.le_of_lt ha)]
    rw [neg_pow]
    have hm := Nat.mod_lt n (by decide : 0 < 2)
    by_cases he : n % 2 = 0
    · have ho : ¬ n % 2 = 1 := by omega
      simp only [ha, true_and, he, Nat.zero_ne_one, if_true, if_false]
    · have ho : n % 2 = 1 := by omega
      simp only [ha, true_and, ho, Nat.one_ne_zero, if_true, if_false]
  · have he := Int.eq_natAbs_of_nonneg (Int.le_of_not_gt ha)
    conv => lhs; rw [he]
    simp only [ha, false_and, if_false]

def signedPower (a : Int) (n : Nat) : Option Int :=
  let m := (a.natAbs : Int)^n
  if a < 0 ∧ n % 2 = 1 then
    if m ≤ Semantics.intBound then some (-m) else none
  else if m < Semantics.intBound then some m else none

theorem signedPower_sound (a : Int) (n : Nat) :
    signedPower a n =
      if -Semantics.intBound ≤ a^n ∧ a^n < Semantics.intBound then some (a^n) else none := by
  have hm : 0 ≤ (a.natAbs : Int)^n := Int.pow_nonneg (Int.natCast_nonneg _)
  have hb : 0 < Semantics.intBound := by decide
  rw [power_sign]
  unfold signedPower
  by_cases h : a < 0 ∧ n % 2 = 1
  · simp only [h, and_self, if_true]
    by_cases hr : (a.natAbs : Int)^n ≤ Semantics.intBound
    · have hs : -Semantics.intBound ≤ -((a.natAbs : Int)^n) ∧
          -((a.natAbs : Int)^n) < Semantics.intBound := by omega
      simp only [hr, hs, and_self, if_true]
    · have hs : ¬ (-Semantics.intBound ≤ -((a.natAbs : Int)^n) ∧
          -((a.natAbs : Int)^n) < Semantics.intBound) := by omega
      simp only [hr, hs, if_false]
  · simp only [h, if_false]
    by_cases hr : (a.natAbs : Int)^n < Semantics.intBound
    · have hs : -Semantics.intBound ≤ (a.natAbs : Int)^n ∧
          (a.natAbs : Int)^n < Semantics.intBound := by omega
      simp only [hr, hs, and_self, if_true]
    · have hs : ¬ (-Semantics.intBound ≤ (a.natAbs : Int)^n ∧
          (a.natAbs : Int)^n < Semantics.intBound) := by omega
      simp only [hr, and_false, if_false]

theorem shr_clamp (a n : Int) :
    BinOp.arithInt .shr a (if n < 256 then n else 256) = BinOp.arithInt .shr a n := by
  by_cases h : n < 256
  · simp only [h, if_true]
  · simp only [h, if_false, BinOp.arithInt, show ¬ (256 : Int) < 256 by decide]

/-- Folding a literal count retains the saturated signed shift exactly. -/
theorem shr_literal (a n : Int) :
    BinOp.arithInt .shr a (min n 256) = BinOp.arithInt .shr a n := by
  have hm : min n (256 : Int) = if n < 256 then n else 256 := by
    split <;> omega
  rw [hm]
  exact shr_clamp a n

theorem shl_word (a n : Int) :
    BinOp.arithInt .shl (a % Semantics.uintBound) n = BinOp.arithInt .shl a n := by
  simp only [BinOp.arithInt]
  by_cases h : n < 256
  · simp only [h, if_true]
    congr 1
    rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
  · simp only [h, if_false]
end Solidity.NumericLowering
namespace Solidity.NumericLowering

theorem abs_word (a : Int)
    (ha : -Semantics.intBound ≤ a ∧ a < Semantics.intBound) :
    (if a < 0 then (0 - a % Semantics.uintBound) % Semantics.uintBound
      else a % Semantics.uintBound) = (a.natAbs : Int) := by
  by_cases h : a < 0
  · have he := Int.ofNat_natAbs_of_nonpos (Int.le_of_lt h)
    simp only [h, if_true, he]
    unfold Semantics.intBound at ha
    unfold Semantics.uintBound
    omega
  · have he := Int.natAbs_of_nonneg (Int.le_of_not_gt h)
    simp only [h, if_false, he]
    unfold Semantics.intBound at ha
    unfold Semantics.uintBound
    omega

theorem positive_cast (m : Int) (hm : 0 ≤ m ∧ m < Semantics.intBound) :
    (if m < Semantics.intBound then m else m - Semantics.uintBound) = m := by
  rw [if_pos hm.2]

theorem negative_cast (m : Int) (hm : 0 ≤ m ∧ m ≤ Semantics.intBound) :
    (if (0-m) % Semantics.uintBound < Semantics.intBound then
      (0-m) % Semantics.uintBound else (0-m) % Semantics.uintBound - Semantics.uintBound) = -m := by
  unfold Semantics.intBound at hm ⊢
  unfold Semantics.uintBound
  split <;> omega
end Solidity.NumericLowering
namespace Solidity.NumericLowering

/-- Arithmetic form of the unsigned-magnitude lowering, including its word
range guard and the conversions used for either result sign. -/
def powerLowering (a : Int) (n : Nat) : Option Int :=
  let m := (a.natAbs : Int)^n
  if m < Semantics.uintBound then
    if a < 0 ∧ n % 2 = 1 then
      if m ≤ Semantics.intBound then
        some (if (0-m) % Semantics.uintBound < Semantics.intBound then
          (0-m) % Semantics.uintBound else (0-m) % Semantics.uintBound - Semantics.uintBound)
      else none
    else if m < Semantics.intBound then
      some (if m < Semantics.intBound then m else m - Semantics.uintBound)
    else none
  else none

theorem powerLowering_sound (a : Int) (n : Nat) :
    powerLowering a n = signedPower a n := by
  have hm : 0 ≤ (a.natAbs : Int)^n := Int.pow_nonneg (Int.natCast_nonneg _)
  have hb : Semantics.intBound < Semantics.uintBound := by decide
  unfold powerLowering signedPower
  by_cases hw : (a.natAbs : Int)^n < Semantics.uintBound
  · simp only [hw, if_true]
    by_cases hs : a < 0 ∧ n % 2 = 1
    · simp only [hs, and_self, if_true]
      by_cases hr : (a.natAbs : Int)^n ≤ Semantics.intBound
      · simp only [hr, if_true, negative_cast _ ⟨hm, hr⟩]
      · simp only [hr, if_false]
    · simp only [hs, if_false]
      by_cases hr : (a.natAbs : Int)^n < Semantics.intBound
      · simp only [hr, if_true]
      · simp only [hr, if_false]
  · have hle : ¬ (a.natAbs : Int)^n ≤ Semantics.intBound := by omega
    have hlt : ¬ (a.natAbs : Int)^n < Semantics.intBound := by omega
    simp only [hw, hle, hlt, if_false]
    split <;> rfl

theorem powerLowering_correct (a : Int) (n : Nat) :
    powerLowering a n =
      if -Semantics.intBound ≤ a^n ∧ a^n < Semantics.intBound then some (a^n) else none := by
  rw [powerLowering_sound, signedPower_sound]

end Solidity.NumericLowering

namespace Solidity.NumericLowering

/-- Saturated counts fit the identity branch of the unsigned-to-signed cast. -/
theorem shift_count_cast (n : Int) (hn : 0 ≤ n) :
    let m := if n < 256 then n else 256
    (if m < Semantics.intBound then m else m - Semantics.uintBound) = m := by
  have hb : (256 : Int) < Semantics.intBound := by decide
  dsimp
  split
  · apply positive_cast
    constructor <;> omega
  · rfl
end Solidity.NumericLowering

/-! The emitted intrinsic value tree, over arbitrary typed states and operands. -/
namespace Solidity.NumericLowering
private theorem wordRange (a : Int) : PrimTy.uint.inRange (a % Semantics.uintBound) = true := by
  have hp : 0 < Semantics.uintBound := by decide
  simp only [PrimTy.inRange, decide_eq_true_eq]
  exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hp⟩
private theorem absRange (a : PrimTy.int.Denote) : PrimTy.uint.inRange (a.val.natAbs : Int) = true := by
  have har : -Semantics.intBound ≤ a.val ∧ a.val < Semantics.intBound := by
    simpa only [PrimTy.inRange, decide_eq_true_eq] using a.property
  rw [← abs_word a.val har]
  split <;> exact wordRange _

theorem signedMagnitude_eval {C : Contract} {Γ : Ctx} (σ : State C Γ) (av : Val C Γ .int)
    (a : PrimTy.int.Denote) (ha : av.evalT σ = .ok a) :
    (Val.signedMagnitude av).evalT σ = .ok ⟨(a.val.natAbs : Int), absRange a⟩ := by
  have har : -Semantics.intBound ≤ a.val ∧ a.val < Semantics.intBound := by
    simpa only [PrimTy.inRange, decide_eq_true_eq] using a.property
  have hm := abs_word a.val har
  have hw := wordRange a.val
  have hs := wordRange (0-a.val % Semantics.uintBound)
  simp only [Val.signedMagnitude, Val.evalT, ha, Bind.bind, Except.bind, Simple.evalT, PrimTy.ofLit,
    BinOp.shortT, BinOp.evalT, BinOp.evalNum, BinOp.ret, BinOp.isArith,
    BinOp.arithInt, UnOp.evalT, TRes.ofOpt, boolT, PrimTy.ofInt?, hw, hs, dite_true, Option.bind_some]
  by_cases h : a.val < 0
  · simp only [h, decide_true, if_true] at hm ⊢
    congr 1
    apply Subtype.ext
    exact hm
  · simp only [h, decide_false, Bool.false_eq_true, if_false] at hm ⊢
    congr 1
    apply Subtype.ext
    exact hm

private theorem unit_power (m : Int) (hm : 0 ≤ m ∧ m ≤ 1) (n : Nat) :
    m^n = if n = 0 then 1 else m := by
  have h : m = 0 ∨ m = 1 := by omega
  rcases h with rfl | rfl
  · by_cases hn : n = 0
    · simp only [hn, Int.pow_zero, if_true]
    · simp only [hn, Int.zero_pow hn, if_false]
  · simp only [Int.one_pow]
    split <;> rfl

theorem magnitudePower_eval {C : Contract} {Γ : Ctx} (σ : State C Γ) (mv bv : Val C Γ .uint)
    (m b : PrimTy.uint.Denote) (hm : mv.evalT σ = .ok m) (hb : bv.evalT σ = .ok b) :
    (Val.magnitudePower mv bv).evalT σ = TRes.ofOpt (PrimTy.uint.ofInt? (m.val^b.val.toNat)) := by
  have hbr : 0 ≤ b.val ∧ b.val < Semantics.uintBound := by
    simpa only [PrimTy.inRange, decide_eq_true_eq] using b.property
  have hmr : 0 ≤ m.val ∧ m.val < Semantics.uintBound := by
    simpa only [PrimTy.inRange, decide_eq_true_eq] using m.property
  simp only [Val.magnitudePower, Val.evalT, hm, hb, Bind.bind, Except.bind,
    Simple.evalT, PrimTy.ofLit, BinOp.shortT, BinOp.evalT, BinOp.evalNum,
    BinOp.ret, BinOp.isArith, BinOp.arithInt, TRes.ofOpt, boolT, Option.bind_some,
    show ¬ b.val < 0 by omega, if_false]
  by_cases hu : m.val ≤ 1
  · simp only [hu, decide_true, if_true]
    rw [unit_power _ ⟨hmr.1, hu⟩]
    by_cases hz : b.val = 0
    · have hn : b.val.toNat = 0 := by omega
      simp only [hz, PrimTy.ofInt?]
      rfl
    · have hn : ¬ b.val.toNat = 0 := by omega
      simp only [hz, hn, decide_false, Bool.false_eq_true, if_false, PrimTy.ofInt?, m.property, dite_true]
      rfl
  · simp only [hu, decide_false, Bool.false_eq_true, if_false]
    rfl
end Solidity.NumericLowering
namespace Solidity.NumericLowering

theorem powerNegative_eval {C : Contract} {Γ : Ctx} (σ : State C Γ) (av : Val C Γ .int) (bv : Val C Γ .uint)
    (a : PrimTy.int.Denote) (b : PrimTy.uint.Denote)
    (ha : av.evalT σ = .ok a) (hb : bv.evalT σ = .ok b) :
    (Val.powerNegative av bv).evalT σ = .ok (decide (a.val < 0 ∧ b.val.toNat % 2 = 1)) := by
  have hbr : 0 ≤ b.val ∧ b.val < Semantics.uintBound := by
    simpa only [PrimTy.inRange, decide_eq_true_eq] using b.property
  have hp : b.val.tmod 2 = ((b.val.toNat % 2 : Nat) : Int) := by
    rw [Int.tmod_eq_emod_of_nonneg hbr.1]
    omega
  have hr : PrimTy.uint.inRange (b.val.tmod 2) = true := by
    simp only [PrimTy.inRange, decide_eq_true_eq]
    rw [hp]
    have := Nat.mod_lt b.val.toNat (by decide : 0 < 2)
    constructor <;> unfold Semantics.uintBound at * <;> omega
  simp only [Val.powerNegative, Val.evalT, ha, hb, Bind.bind, Except.bind,
    Simple.evalT, PrimTy.ofLit, BinOp.shortT, BinOp.evalT, BinOp.evalNum, BinOp.evalBool,
    BinOp.ret, BinOp.isArith, BinOp.arithInt, TRes.ofOpt, boolT, Option.bind_some,
    show ¬ (2 : Int) = 0 by decide, if_false, PrimTy.ofInt?, hr, dite_true]
  by_cases hn : a.val < 0 <;> by_cases he : b.val.toNat % 2 = 1 <;>
    simp_all only [decide_true, decide_false, and_true, and_false]
  · simp_all only [Int.cast_ofNat_Int, Bool.false_eq_true, ↓dreduceIte, ↓reduceIte,
      decide_true, Bool.and_self]
  · simp_all only [Int.natCast_emod, Int.ofNat_toNat, Int.cast_ofNat_Int,
      Nat.mod_two_not_eq_one, Bool.false_eq_true, ↓dreduceIte, ↓reduceIte, Int.reduceEq, decide_false,
      Bool.and_false]
  · simp_all only [Int.cast_ofNat_Int, Int.not_lt, Bool.false_eq_true, ↓dreduceIte,
      ↓reduceIte, Pure.pure, Except.pure]
  · simp_all only [Int.natCast_emod, Int.ofNat_toNat, Int.cast_ofNat_Int, Int.not_lt,
      Nat.mod_two_not_eq_one, Bool.false_eq_true, ↓dreduceIte, ↓reduceIte, Pure.pure, Except.pure]
end Solidity.NumericLowering
namespace Solidity.NumericLowering

private theorem toInt_sub (p : PrimTy.uint.Denote) :
    @UnOp.evalT .toInt (BinOp.subW.ret .uint) rfl p =
      PrimTy.int.ofInt? (if p.val < Semantics.intBound then p.val else p.val-Semantics.uintBound) := by
  change @UnOp.evalT .toInt .uint rfl p = _
  rfl

theorem signedPowerResult_eval {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (nv : Val C Γ .bool) (pv : Val C Γ .uint) (negative : Bool) (p : PrimTy.uint.Denote)
    (hn : nv.evalT σ = .ok negative) (hp : pv.evalT σ = .ok p) :
    ((Val.signedPowerResult nv pv).evalT σ).toOption.map (·.val) =
      if negative then (if p.val ≤ Semantics.intBound then some (-p.val) else none)
      else (if p.val < Semantics.intBound then some p.val else none) := by
  have hpr : 0 ≤ p.val ∧ p.val < Semantics.uintBound := by
    simpa only [PrimTy.inRange, decide_eq_true_eq] using p.property
  have hw := wordRange (0-p.val)
  have hb : (0 : Int) < Semantics.intBound := by decide
  simp only [Val.signedPowerResult, Val.evalT, hn, hp, Bind.bind, Except.bind, Simple.evalT, PrimTy.ofLit, BinOp.shortT, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, toInt_sub, TRes.ofOpt, boolT, Option.bind_some, PrimTy.ofInt?, hw, dite_true]
  have eB : ((2^255 : Nat) : Int) = Semantics.intBound := rfl
  simp only [eB]
  have hfail : PrimTy.int.inRange (((2^255-1 : Nat) : Int)+1) = false := by decide
  cases negative
  · simp only [Bool.false_eq_true, if_false]
    by_cases hr : p.val < Semantics.intBound
    · have hi : PrimTy.int.inRange p.val = true := by
        simp only [PrimTy.inRange, decide_eq_true_eq]
        exact ⟨by omega, hr⟩
      simp only [hr, decide_true, if_true, hi, dite_true, Except.toOption, Option.map, eq_self]
    · simp only [hr, decide_false, Bool.false_eq_true, if_false]
      rfl
  · simp only [if_true]
    by_cases hr : p.val ≤ Semantics.intBound
    · have hc := negative_cast p.val ⟨hpr.1, hr⟩
      have hi : PrimTy.int.inRange (-p.val) = true := by
        simp only [PrimTy.inRange, decide_eq_true_eq]
        change -Semantics.intBound ≤ -p.val ∧ -p.val < Semantics.intBound
        constructor <;> omega
      simp only [hr, decide_true, if_true, hc, hi, dite_true, Except.toOption, Option.map, eq_self]
    · simp only [hr, decide_false, Bool.false_eq_true, if_false, hfail, dite_false, Except.toOption, Option.map]
end Solidity.NumericLowering
namespace Solidity.NumericLowering

theorem signedPowerResult_error {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (nv : Val C Γ .bool) (pv : Val C Γ .uint) (negative : Bool) (e : THalt)
    (hn : nv.evalT σ = .ok negative) (hp : pv.evalT σ = .error e) :
    (Val.signedPowerResult nv pv).evalT σ = .error e := by
  cases negative <;>
    simp only [Val.signedPowerResult, Val.evalT, hn, hp, Bind.bind, Except.bind,
      boolT, Bool.false_eq_true, eq_self, if_true, if_false]

theorem checkedSignedPower_eval {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (av : Val C Γ .int) (bv : Val C Γ .uint) (a : PrimTy.int.Denote) (b : PrimTy.uint.Denote)
    (ha : av.evalT σ = .ok a) (hb : bv.evalT σ = .ok b) :
    ((Val.checkedSignedPower av bv).evalT σ).toOption.map (·.val) =
      signedPower a.val b.val.toNat := by
  let m : PrimTy.uint.Denote := ⟨(a.val.natAbs : Int), absRange a⟩
  have hm := signedMagnitude_eval σ av a ha
  have hpow := magnitudePower_eval σ (Val.signedMagnitude av) bv m b hm hb
  have hneg := powerNegative_eval σ av bv a b ha hb
  have hm0 : 0 ≤ (a.val.natAbs : Int)^b.val.toNat := Int.pow_nonneg (Int.natCast_nonneg _)
  have hBW : Semantics.intBound < Semantics.uintBound := by decide
  by_cases hr : PrimTy.uint.inRange ((a.val.natAbs : Int)^b.val.toNat) = true
  · have hp : (Val.magnitudePower (Val.signedMagnitude av) bv).evalT σ =
        .ok ⟨(a.val.natAbs : Int)^b.val.toNat, hr⟩ := by
      simpa only [m, PrimTy.ofInt?, hr, dite_true, TRes.ofOpt] using hpow
    rw [Val.checkedSignedPower, signedPowerResult_eval σ _ _ _ _ hneg hp]
    unfold signedPower
    by_cases hs : a.val < 0 ∧ b.val.toNat % 2 = 1
    · simp only [hs, and_self, decide_true, if_true]
    · simp only [hs, decide_false, Bool.false_eq_true, if_false]
  · have hp : (Val.magnitudePower (Val.signedMagnitude av) bv).evalT σ = .error .revert := by
      simpa only [m, PrimTy.ofInt?, hr, dite_false, TRes.ofOpt] using hpow
    rw [Val.checkedSignedPower, signedPowerResult_error σ _ _ _ _ hneg hp]
    simp only [Except.toOption, Option.map]
    have hge : ¬ (a.val.natAbs : Int)^b.val.toNat < Semantics.uintBound := by
      simp only [PrimTy.inRange, decide_eq_true_eq] at hr
      exact fun hlt => hr ⟨hm0, hlt⟩
    have hle : ¬ (a.val.natAbs : Int)^b.val.toNat ≤ Semantics.intBound := by omega
    have hlt : ¬ (a.val.natAbs : Int)^b.val.toNat < Semantics.intBound := by omega
    unfold signedPower
    simp only [hle, hlt, if_false]
    split <;> rfl

theorem checkedSignedPower_correct {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (av : Val C Γ .int) (bv : Val C Γ .uint) (a : PrimTy.int.Denote) (b : PrimTy.uint.Denote)
    (ha : av.evalT σ = .ok a) (hb : bv.evalT σ = .ok b) :
    ((Val.checkedSignedPower av bv).evalT σ).toOption.map (·.val) =
      if -Semantics.intBound ≤ a.val^b.val.toNat ∧ a.val^b.val.toNat < Semantics.intBound
      then some (a.val^b.val.toNat) else none := by
  rw [checkedSignedPower_eval σ av bv a b ha hb, signedPower_sound]
end Solidity.NumericLowering
