import SolidityBridge.Arith.Checked
import SolidityBridge.Arith.NarrowWrapping

namespace Solidity.Bridge.Arith
open Widths

theorem uint_roundtrip_width (n : Nat) (z : Int) :
    z = ((BitVec.ofInt n z).toNat : Int) ↔ 0 ≤ z ∧ z < (2 : Int) ^ n := by
  constructor
  · intro h
    rw [h]
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast (BitVec.ofInt n z).isLt⟩
  · rintro ⟨hz, hb⟩
    symm
    simp only [BitVec.toNat_ofInt, Nat.cast_pow, Nat.cast_ofNat,
      Int.emod_eq_of_lt hz hb, Int.toNat_of_nonneg hz]

theorem int_roundtrip_width (n : Nat) (hn : 0 < n) (z : Int) :
    z = (BitVec.ofInt n z).toInt ↔ -(2 ^ (n - 1)) ≤ z ∧ z < (2 : Int) ^ (n - 1) := by
  constructor
  · intro h
    rw [h]
    exact ⟨BitVec.le_toInt _, BitVec.toInt_lt⟩
  · rintro ⟨hz, hb⟩
    exact (BitVec.toInt_ofInt_eq_self hn hz hb).symm

theorem uint_max_range (n : Nat) (hn : n ≤ 256) :
    PrimTy.uint.inRange (2 ^ n - 1 : Nat) = true := by
  simp only [PrimTy.inRange, decide_eq_true_eq]
  have hp : (2 : Nat) ^ n ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) hn
  have hz : 0 < (2 : Nat) ^ n := Nat.two_pow_pos n
  exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr (by omega)⟩

/-- Exact typed term produced by the unsigned inTyCond checker. -/
def uintGuard {C : Contract} {Γ : Ctx} (n : Nat) (hn : n ≤ 256)
    (v : Val C Γ .uint) : Val C Γ .bool :=
  .binop .le rfl rfl v (.simple (.lit (2 ^ n - 1 : Nat) (uint_max_range n hn)))

theorem check_uint_guard {C : Contract} {Γ : NCtx} (e : RawExpr) (v : Val C Γ.ctx .uint)
    (n : Nat) (hn : n ≤ 256) (hc : e.constRat? = none) (hl : e.isLit = false)
    (hs : Solidity.synth C Γ e = .ok (.val .uint v))
    (hv : Solidity.check C Γ .uint e = .ok v) :
    Solidity.check C Γ .bool (inTyCond .uint n e) = .ok (uintGuard n hn v) := by
  rw [inTyCond, if_neg (by decide)]
  exact check_bin_literal .uint e v .le (2 ^ n - 1) rfl (uint_max_range n hn) hc hl hs hv (by intro h; cases h)

theorem uintGuard_eval {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (n : Nat) (hn : n ≤ 256) (v : Val C Γ .uint) :
    (uintGuard n hn v).evalT σ =
      (v.evalT σ >>= fun x => .ok (decide (x.val < (2 : Int) ^ n))) := by
  cases h : v.evalT σ with
  | error e => simp only [uintGuard, Val.evalT.eq_3, h, bind, Except.bind]
  | ok x =>
    simp only [uintGuard, Val.evalT.eq_3, Val.evalT.eq_1, Simple.evalT, h,
      BinOp.shortT, ok_bind, BinOp.evalT, BinOp.evalNum, PrimTy.ofLit, TRes.ofOpt]
    congr 2
    have hp : (0 : Nat) < 2 ^ n := Nat.two_pow_pos n
    have he : x.val ≤ ((2 ^ n - 1 : Nat) : Int) ↔ x.val < (2 : Int) ^ n := by
      have he : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by
        simp only [Nat.cast_pow, Nat.cast_ofNat]
      rw [← he]
      omega
    exact propext he

/-- The actual assert/require runners applied to the checked guard retain the exact halt kind. -/
theorem uintGuard_assert {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (n : Nat) (hn : n ≤ 256) (v : Val C Γ .uint) :
    (Stmt.assert (uintGuard n hn v)).run σ =
      (v.evalT σ >>= fun x => if x.val < (2 : Int) ^ n then
        .ok ⟨σ, List.prefix_refl _⟩ else .error .panic) := by
  rw [Stmt.run, Stmt.runR_eq]
  simp only [Stmt.runC, TRun.assert, uintGuard_eval, bind_assoc]
  congr 1
  funext x
  simp only [ok_bind, boolT, decide_eq_true_eq, pure, Except.pure]

theorem uintGuard_require {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (n : Nat) (hn : n ≤ 256) (v : Val C Γ .uint) :
    (Stmt.require (uintGuard n hn v)).run σ =
      (v.evalT σ >>= fun x => if x.val < (2 : Int) ^ n then
        .ok ⟨σ, List.prefix_refl _⟩ else .error .revert) := by
  rw [Stmt.run, Stmt.runR_eq]
  simp only [Stmt.runC, TRun.require, uintGuard_eval, bind_assoc]
  congr 1
  funext x
  simp only [ok_bind, boolT, decide_eq_true_eq, pure, Except.pure]

theorem int_half_range (n : Nat) (hn : n ≤ 256) :
    PrimTy.int.inRange (-((2 ^ (n - 1) : Nat) : Int)) = true ∧
      PrimTy.int.inRange (2 ^ (n - 1) - 1 : Nat) = true := by
  have hp : (2 : Nat) ^ (n - 1) ≤ 2 ^ 255 :=
    Nat.pow_le_pow_right (by decide) (show n - 1 ≤ 255 by omega)
  have hz : 0 < (2 : Nat) ^ (n - 1) := Nat.two_pow_pos _
  simp only [PrimTy.inRange, decide_eq_true_eq]
  omega

/-- Both comparisons of the signed inTyCond, at the primitive int type. -/
def intGuard {C : Contract} {Γ : Ctx} (n : Nat) (hn : n ≤ 256)
    (v : Val C Γ .int) : Val C Γ .bool :=
  .binop .and rfl rfl
    (.binop .le rfl rfl (.simple (.lit (-((2 ^ (n - 1) : Nat) : Int)) (int_half_range n hn).1)) v)
    (.binop .le rfl rfl v (.simple (.lit (2 ^ (n - 1) - 1 : Nat) (int_half_range n hn).2)))

theorem intGuard_eval {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (n : Nat) (hn : n ≤ 256) (v : Val C Γ .int) :
    (intGuard n hn v).evalT σ =
      (v.evalT σ >>= fun x => .ok (decide (-(2 ^ (n - 1)) ≤ x.val ∧
        x.val < (2 : Int) ^ (n - 1)))) := by
  cases h : v.evalT σ with
  | error e =>
    simp only [intGuard, Val.evalT.eq_3, Val.evalT.eq_1, Simple.evalT, h,
      BinOp.shortT, bind, Except.bind]
  | ok x =>
    simp only [intGuard, Val.evalT.eq_3, Val.evalT.eq_1, Simple.evalT, h,
      BinOp.shortT, ok_bind, BinOp.evalT, BinOp.evalNum, PrimTy.ofLit, TRes.ofOpt]
    dsimp only [BinOp.ret, BinOp.isArith]
    have hp : (0 : Nat) < 2 ^ (n - 1) := Nat.two_pow_pos _
    have he : ((2 ^ (n - 1) : Nat) : Int) = (2 : Int) ^ (n - 1) := by
      simp only [Nat.cast_pow, Nat.cast_ofNat]
    have hu : x.val ≤ ((2 ^ (n - 1) - 1 : Nat) : Int) ↔
        x.val < (2 : Int) ^ (n - 1) := by rw [← he]; omega
    simp only [BinOp.ret, BinOp.isArith, hu, he, boolT, BinOp.evalBool, pure, Except.pure]
    by_cases hs : -(2 ^ (n - 1) : Int) ≤ x.val
    · simp only [hs, decide_true, true_and]
      rfl
    · simp only [hs, decide_false, false_and]
      rfl


theorem check_neg_literal {C : Contract} {Γ : NCtx} (k : Nat)
    (hk : PrimTy.int.inRange (-(k : Int)) = true) :
    Solidity.check C Γ .int (.unop .neg (.num k)) = .ok (.simple (.lit (-(k : Int)) hk)) := by
  rw [Solidity.check.eq_2, if_pos rfl, litAt_of_range .int (-(k : Int)) hk]
  rfl

theorem synth_int_lower {C : Contract} {Γ : NCtx} (e : RawExpr) (v : Val C Γ.ctx .int)
    (k : Nat) (hk : PrimTy.int.inRange (-(k : Int)) = true)
    (hc : e.constRat? = none) (hs : Solidity.synth C Γ e = .ok (.val .int v))
    (hv : Solidity.check C Γ .int e = .ok v) :
    Solidity.synth C Γ (.binop .le (.unop .neg (.num k)) e) =
      .ok (.val .bool (.binop .le rfl rfl (.simple (.lit (-(k : Int)) hk)) v)) := by
  unfold Solidity.synth
  simp only [RawExpr.constRat?, hc, bind, Option.bind, RawExpr.isLit, if_true,
    pure, Except.pure, Except.bind]
  rw [hs]
  simp only [TExpr.toVal?, Bool.false_eq_true]
  rw [check_neg_literal k hk, hv]
  rfl

theorem check_int_lower {C : Contract} {Γ : NCtx} (e : RawExpr) (v : Val C Γ.ctx .int)
    (k : Nat) (hk : PrimTy.int.inRange (-(k : Int)) = true)
    (hc : e.constRat? = none)
    (hs : Solidity.synth C Γ e = .ok (.val .int v))
    (hv : Solidity.check C Γ .int e = .ok v) :
    Solidity.check C Γ .bool (.binop .le (.unop .neg (.num k)) e) =
      .ok (.binop .le rfl rfl (.simple (.lit (-(k : Int)) hk)) v) := by
  rw [Solidity.check.eq_3]
  simp only [RawExpr.constRat?, hc, bind, Option.bind, BinOp.isArith,
    Bool.and_false, Bool.false_eq_true, if_false, pure, Except.pure, Except.bind]
  unfold checkVia
  rw [synth_int_lower e v k hk hc hs hv]
  rfl

theorem check_int_guard {C : Contract} {Γ : NCtx} (e : RawExpr) (v : Val C Γ.ctx .int)
    (n : Nat) (hn : n ≤ 256) (hc : e.constRat? = none) (hl : e.isLit = false)
    (hs : Solidity.synth C Γ e = .ok (.val .int v))
    (hv : Solidity.check C Γ .int e = .ok v) :
    Solidity.check C Γ .bool (inTyCond .int n e) = .ok (intGuard n hn v) := by
  let a : RawExpr := .binop .le (.unop .neg (.num (2 ^ (n - 1)))) e
  let b : RawExpr := .binop .le e (.num (2 ^ (n - 1) - 1))
  let va : Val C Γ.ctx .bool := .binop .le rfl rfl
    (.simple (.lit (-((2 ^ (n - 1) : Nat) : Int)) (int_half_range n hn).1)) v
  let vb : Val C Γ.ctx .bool := .binop .le rfl rfl v
    (.simple (.lit (2 ^ (n - 1) - 1 : Nat) (int_half_range n hn).2))
  have hsa : Solidity.synth C Γ a = .ok (.val .bool va) :=
    synth_int_lower e v _ (int_half_range n hn).1 hc hs hv
  have hva : Solidity.check C Γ .bool a = .ok va :=
    check_int_lower e v _ (int_half_range n hn).1 hc hs hv
  have hvb : Solidity.check C Γ .bool b = .ok vb :=
    check_bin_literal .int e v .le _ rfl (int_half_range n hn).2 hc hl hs hv (by intro _ h; cases h)
  have hca : a.constRat? = none := by
    simp only [a, RawExpr.constRat?, hc, bind, Option.bind]
  rw [inTyCond, if_pos rfl]
  exact check_binary .bool a b va vb .and rfl hca rfl hsa hva hvb (by intro h; cases h)

/-- Observation after the primitive evaluator and the core's unsigned width guard.
`failure` is panic for explicit checked mode and revert for the default narrow guard. -/
def uintWidthResult (n : Nat) (failure : THalt) (r : TRes PrimTy.uint.Denote) : TRes Int := do
  let x ← r
  if x.val < (2 : Int) ^ n then .ok x.val else .error failure

def intWidthResult (n : Nat) (failure : THalt) (r : TRes PrimTy.int.Denote) : TRes Int := do
  let x ← r
  if -(2 ^ (n - 1)) ≤ x.val ∧ x.val < (2 : Int) ^ (n - 1) then .ok x.val else .error failure

theorem uint_checked_width (n : Nat) (hn : n ≤ 256) (failure : THalt) (z : Int) :
    uintWidthResult n failure (TRes.ofOpt (PrimTy.uint.ofInt? z)) =
      if z = ((BitVec.ofInt n z).toNat : Int) then .ok z else
      if z = ((BitVec.ofInt 256 z).toNat : Int) then .error failure else .error .revert := by
  have hp : (2 : Int) ^ n ≤ 2 ^ 256 := by
    have hp' : (2 : Nat) ^ n ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) hn
    exact_mod_cast hp'
  simp only [uint_roundtrip_width]
  cases h : PrimTy.uint.ofInt? z with
  | none =>
    have he : (PrimTy.uint.ofInt? z).map Subtype.val =
        if 0 ≤ z ∧ z < (2 : Int) ^ 256 then some z else none := uint_check z
    rw [h, Option.map_none] at he
    have hf : ¬ (0 ≤ z ∧ z < 2 ^ 256) := by
      intro hz
      rw [if_pos hz] at he
      cases he
    have hnf : ¬ (0 ≤ z ∧ z < (2 : Int) ^ n) := by omega
    simp only [uintWidthResult, TRes.ofOpt, bind, Except.bind, if_neg hf, if_neg hnf]
  | some x =>
    have he : (PrimTy.uint.ofInt? z).map Subtype.val =
        if 0 ≤ z ∧ z < (2 : Int) ^ 256 then some z else none := uint_check z
    rw [h, Option.map_some] at he
    split at he
    · rename_i hz
      have hx : x.val = z := Option.some.inj he
      simp only [uintWidthResult, TRes.ofOpt, ok_bind, hx, if_pos hz]
      by_cases hnz : z < (2 : Int) ^ n
      · rw [if_pos hnz, if_pos ⟨hz.1, hnz⟩]
      · rw [if_neg hnz, if_neg (by omega)]
    · cases he

theorem int_checked_width (n : Nat) (hn0 : 0 < n) (hn : n ≤ 256)
    (failure : THalt) (z : Int) :
    intWidthResult n failure (TRes.ofOpt (PrimTy.int.ofInt? z)) =
      if z = (BitVec.ofInt n z).toInt then .ok z else
      if z = (BitVec.ofInt 256 z).toInt then .error failure else .error .revert := by
  have hp : (2 : Int) ^ (n - 1) ≤ 2 ^ 255 := by
    have hp' : (2 : Nat) ^ (n - 1) ≤ 2 ^ 255 :=
      Nat.pow_le_pow_right (by decide) (show n - 1 ≤ 255 by omega)
    exact_mod_cast hp'
  simp only [int_roundtrip_width n hn0, int_roundtrip]
  cases h : PrimTy.int.ofInt? z with
  | none =>
    have he : (PrimTy.int.ofInt? z).map Subtype.val =
        if -(2 ^ 255) ≤ z ∧ z < (2 : Int) ^ 255 then some z else none := int_check z
    rw [h, Option.map_none] at he
    have hf : ¬ (-(2 ^ 255) ≤ z ∧ z < 2 ^ 255) := by
      intro hz
      rw [if_pos hz] at he
      cases he
    have hnf : ¬ (-(2 ^ (n - 1)) ≤ z ∧ z < (2 : Int) ^ (n - 1)) := by omega
    simp only [intWidthResult, TRes.ofOpt, bind, Except.bind, if_neg hf, if_neg hnf]
  | some x =>
    have he : (PrimTy.int.ofInt? z).map Subtype.val =
        if -(2 ^ 255) ≤ z ∧ z < (2 : Int) ^ 255 then some z else none := int_check z
    rw [h, Option.map_some] at he
    split at he
    · rename_i hz
      have hx : x.val = z := Option.some.inj he
      simp only [intWidthResult, TRes.ofOpt, ok_bind, hx, if_pos hz]
    · cases he

def WrapOp.checkedUint : WrapOp → PrimTy.uint.Denote → PrimTy.uint.Denote → Option PrimTy.uint.Denote
  | .add => BinOp.add.evalT rfl | .sub => BinOp.sub.evalT rfl
  | .mul => BinOp.mul.evalT rfl | .pow => BinOp.pow.evalT rfl

theorem WrapOp.checkedUint_eq (op : WrapOp) (x y : PrimTy.uint.Denote) :
    op.checkedUint x y = PrimTy.uint.ofInt? (op.ideal x.val y.val) := by
  cases op
  · rfl
  · rfl
  · rfl
  · change (if y.val < 0 then none else some (x.val ^ y.val.toNat)).bind _ = _
    rw [if_neg (not_lt.mpr (PrimTy.uint_nonneg y)), Option.bind_some]
    rfl

/-- All checked uint arithmetic, all widths: exact successful result and exact failure source. -/
theorem uint_checked_all_widths (op : WrapOp) (n : Nat) (hn : n ≤ 256)
    (failure : THalt) (x y : PrimTy.uint.Denote) :
    uintWidthResult n failure (TRes.ofOpt (op.checkedUint x y)) =
      if op.ideal x.val y.val =
          ((op.word (BitVec.ofInt n x.val) (BitVec.ofInt n y.val) y.val.toNat).toNat : Int)
      then .ok (op.ideal x.val y.val) else
      if op.ideal x.val y.val = ((BitVec.ofInt 256 (op.ideal x.val y.val)).toNat : Int)
      then .error failure else .error .revert := by
  rw [op.checkedUint_eq, uint_checked_width n hn, op.encode]

def WrapOp.checkedInt : WrapOp → PrimTy.int.Denote → PrimTy.int.Denote → Option PrimTy.int.Denote
  | .add => BinOp.add.evalT rfl | .sub => BinOp.sub.evalT rfl
  | .mul => BinOp.mul.evalT rfl | .pow => fun _ _ => none

/-- Signed checked power is not admitted; the three admitted binary ring operations are covered. -/
theorem int_checked_all_widths (op : WrapOp) (hop : op ≠ .pow)
    (n : Nat) (hn0 : 0 < n) (hn : n ≤ 256) (failure : THalt) (x y : PrimTy.int.Denote) :
    intWidthResult n failure (TRes.ofOpt (op.checkedInt x y)) =
      if op.ideal x.val y.val =
          (op.word (BitVec.ofInt n x.val) (BitVec.ofInt n y.val) y.val.toNat).toInt
      then .ok (op.ideal x.val y.val) else
      if op.ideal x.val y.val = (BitVec.ofInt 256 (op.ideal x.val y.val)).toInt
      then .error failure else .error .revert := by
  have he : op.checkedInt x y = PrimTy.int.ofInt? (op.ideal x.val y.val) := by
    cases op
    · rfl
    · rfl
    · rfl
    · exact False.elim (hop rfl)
  rw [he, int_checked_width n hn0 hn, op.encode]

theorem int_neg_checked_all_widths (n : Nat) (hn0 : 0 < n) (hn : n ≤ 256)
    (failure : THalt) (x : PrimTy.int.Denote) :
    intWidthResult n failure (TRes.ofOpt (UnOp.neg.evalT rfl x)) =
      if -x.val = (-BitVec.ofInt n x.val).toInt then .ok (-x.val) else
      if -x.val = (-BitVec.ofInt 256 x.val).toInt then .error failure else .error .revert := by
  change intWidthResult n failure (TRes.ofOpt (PrimTy.int.ofInt? (-x.val))) = _
  rw [int_checked_width n hn0 hn, BitVec.ofInt_neg, BitVec.ofInt_neg]

theorem intGuard_assert {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (n : Nat) (hn : n ≤ 256) (v : Val C Γ .int) :
    (Stmt.assert (intGuard n hn v)).run σ =
      (v.evalT σ >>= fun x => if -(2 ^ (n - 1)) ≤ x.val ∧ x.val < (2 : Int) ^ (n - 1) then
        .ok ⟨σ, List.prefix_refl _⟩ else .error .panic) := by
  rw [Stmt.run, Stmt.runR_eq]
  simp only [Stmt.runC, TRun.assert, intGuard_eval, bind_assoc]
  congr 1
  funext x
  simp only [ok_bind, boolT, decide_eq_true_eq, pure, Except.pure]

theorem intGuard_require {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (n : Nat) (hn : n ≤ 256) (v : Val C Γ .int) :
    (Stmt.require (intGuard n hn v)).run σ =
      (v.evalT σ >>= fun x => if -(2 ^ (n - 1)) ≤ x.val ∧ x.val < (2 : Int) ^ (n - 1) then
        .ok ⟨σ, List.prefix_refl _⟩ else .error .revert) := by
  rw [Stmt.run, Stmt.runR_eq]
  simp only [Stmt.runC, TRun.require, intGuard_eval, bind_assoc]
  congr 1
  funext x
  simp only [ok_bind, boolT, decide_eq_true_eq, pure, Except.pure]

end Solidity.Bridge.Arith

#print axioms Solidity.Bridge.Arith.uint_roundtrip_width
#print axioms Solidity.Bridge.Arith.int_roundtrip_width
#print axioms Solidity.Bridge.Arith.check_uint_guard
#print axioms Solidity.Bridge.Arith.uintGuard_eval
#print axioms Solidity.Bridge.Arith.uintGuard_assert

#print axioms Solidity.Bridge.Arith.uintGuard_require
#print axioms Solidity.Bridge.Arith.intGuard_eval
#print axioms Solidity.Bridge.Arith.uint_checked_width
#print axioms Solidity.Bridge.Arith.int_checked_width

#print axioms Solidity.Bridge.Arith.uint_checked_all_widths
#print axioms Solidity.Bridge.Arith.int_checked_all_widths
#print axioms Solidity.Bridge.Arith.int_neg_checked_all_widths
#print axioms Solidity.Bridge.Arith.intGuard_assert
#print axioms Solidity.Bridge.Arith.intGuard_require

#print axioms Solidity.Bridge.Arith.check_int_guard
