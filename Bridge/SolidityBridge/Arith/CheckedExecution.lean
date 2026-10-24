import SolidityBridge.Arith.OverflowGuards

set_option maxRecDepth 2048

namespace Solidity.Bridge.Arith

/-- The core value guard and checking-mode assert, before the guarded evaluation. -/
def guardedValue {C : Contract} {Γ : Ctx} {p : PrimTy} (σ : State C Γ)
    (v : Val C Γ p) : TRes p.Denote :=
  match v.guard with
  | none => v.evalT σ
  | some g => do
    let b ← g.evalT σ
    if boolT b then v.evalT σ else .error .panic

theorem guardedValue_eq {C : Contract} {Γ : Ctx} {p : PrimTy} (σ : State C Γ)
    (v : Val C Γ p) (b : Bool)
    (h : v.guard.map (fun g => g.evalT σ) = some (.ok b)) :
    guardedValue σ v = if b then v.evalT σ else .error .panic := by
  cases hg : v.guard with
  | none => rw [hg, Option.map_none] at h; cases h
  | some g =>
    rw [hg, Option.map_some] at h
    unfold guardedValue
    rw [hg]
    change (g.evalT σ >>= fun b => if boolT b then v.evalT σ else .error .panic) = _
    rw [Option.some.inj h]
    simp only [ok_bind, boolT]

/-- The checking prefix is the actual core assert runner, followed by evaluation in its returned state. -/
theorem guardedValue_assert_then {C : Contract} {Γ : Ctx} {p : PrimTy} (σ : State C Γ)
    (v : Val C Γ p) (g : Val C Γ .bool) (hg : v.guard = some g) :
    guardedValue σ v = ((Stmt.assert g).run σ >>= fun o => v.evalT o.st) := by
  unfold guardedValue
  rw [hg, Stmt.run, Stmt.runR_eq]
  simp only [Stmt.runC, TRun.assert, bind_assoc]
  congr 1
  funext b
  cases b <;> rfl

inductive RingOp where | add | sub | mul

def RingOp.bin : RingOp → BinOp
  | .add => .add | .sub => .sub | .mul => .mul

def RingOp.wrap : RingOp → WrapOp
  | .add => .add | .sub => .sub | .mul => .mul

def RingOp.ideal (op : RingOp) (x y : Int) : Int := op.wrap.ideal x y

def RingOp.uintTerm {C : Contract} {Γ : Ctx} : RingOp → PrimTy.uint.Denote → PrimTy.uint.Denote → Val C Γ .uint
  | .add, x, y => .binop .add rfl rfl (litUInt x) (litUInt y)
  | .sub, x, y => .binop .sub rfl rfl (litUInt x) (litUInt y)
  | .mul, x, y => .binop .mul rfl rfl (litUInt x) (litUInt y)

def RingOp.intTerm {C : Contract} {Γ : Ctx} : RingOp → PrimTy.int.Denote → PrimTy.int.Denote → Val C Γ .int
  | .add, x, y => .binop .add rfl rfl (litInt x) (litInt y)
  | .sub, x, y => .binop .sub rfl rfl (litInt x) (litInt y)
  | .mul, x, y => .binop .mul rfl rfl (litInt x) (litInt y)

theorem RingOp.uint_eval {C : Contract} {Γ : Ctx} (σ : State C Γ) (op : RingOp)
    (x y : PrimTy.uint.Denote) :
    (op.uintTerm x y).evalT σ = TRes.ofOpt (PrimTy.uint.ofInt? (op.ideal x.val y.val)) := by
  cases op <;> rfl

theorem RingOp.int_eval {C : Contract} {Γ : Ctx} (σ : State C Γ) (op : RingOp)
    (x y : PrimTy.int.Denote) :
    (op.intTerm x y).evalT σ = TRes.ofOpt (PrimTy.int.ofInt? (op.ideal x.val y.val)) := by
  cases op <;> rfl

theorem RingOp.uint_guard {C : Contract} {Γ : Ctx} (σ : State C Γ) (op : RingOp)
    (x y : PrimTy.uint.Denote) :
    (op.uintTerm x y).guard.map (fun g => g.evalT σ) =
      some (.ok (decide (op.ideal x.val y.val = ((BitVec.ofInt 256 (op.ideal x.val y.val)).toNat : Int)))) := by
  cases op
  · simpa only [RingOp.uintTerm, RingOp.ideal, RingOp.wrap, WrapOp.ideal, BitVec.ofInt_add] using uint_add_guard σ x y
  · simpa only [RingOp.uintTerm, RingOp.ideal, RingOp.wrap, WrapOp.ideal, ofInt_sub] using uint_sub_guard σ x y
  · simpa only [RingOp.uintTerm, RingOp.ideal, RingOp.wrap, WrapOp.ideal, BitVec.ofInt_mul] using uint_mul_guard σ x y

theorem RingOp.int_guard {C : Contract} {Γ : Ctx} (σ : State C Γ) (op : RingOp)
    (x y : PrimTy.int.Denote) :
    (op.intTerm x y).guard.map (fun g => g.evalT σ) =
      some (.ok (decide (op.ideal x.val y.val = (BitVec.ofInt 256 (op.ideal x.val y.val)).toInt))) := by
  cases op
  · simpa only [RingOp.intTerm, RingOp.ideal, RingOp.wrap, WrapOp.ideal, BitVec.ofInt_add] using int_add_guard σ x y
  · simpa only [RingOp.intTerm, RingOp.ideal, RingOp.wrap, WrapOp.ideal, ofInt_sub] using int_sub_guard σ x y
  · simpa only [RingOp.intTerm, RingOp.ideal, RingOp.wrap, WrapOp.ideal, BitVec.ofInt_mul] using int_mul_guard σ x y

theorem uint_preguard_width (n : Nat) (hn : n ≤ 256) (z : Int) :
    (if z = ((BitVec.ofInt 256 z).toNat : Int) then
      uintWidthResult n .panic (TRes.ofOpt (PrimTy.uint.ofInt? z)) else .error .panic) =
      if z = ((BitVec.ofInt n z).toNat : Int) then .ok z else .error .panic := by
  have hp : (2 : Int) ^ n ≤ 2 ^ 256 := by
    have hp' : (2 : Nat) ^ n ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) hn
    exact_mod_cast hp'
  rw [uint_checked_width n hn]
  by_cases hnz : z = ((BitVec.ofInt n z).toNat : Int)
  · have hr : 0 ≤ z ∧ z < (2 : Int) ^ n := (uint_roundtrip_width n z).mp hnz
    have hf : z = ((BitVec.ofInt 256 z).toNat : Int) := (uint_roundtrip z).mpr (by omega)
    rw [if_pos hnz, if_pos hnz, if_pos hf]
  · rw [if_neg hnz, if_neg hnz]
    by_cases hf : z = ((BitVec.ofInt 256 z).toNat : Int)
    · rw [if_pos hf, if_pos hf]
    · rw [if_neg hf]

theorem int_preguard_width (n : Nat) (hn0 : 0 < n) (hn : n ≤ 256) (z : Int) :
    (if z = (BitVec.ofInt 256 z).toInt then
      intWidthResult n .panic (TRes.ofOpt (PrimTy.int.ofInt? z)) else .error .panic) =
      if z = (BitVec.ofInt n z).toInt then .ok z else .error .panic := by
  have hp : (2 : Int) ^ (n - 1) ≤ 2 ^ 255 := by
    have hp' : (2 : Nat) ^ (n - 1) ≤ 2 ^ 255 :=
      Nat.pow_le_pow_right (by decide) (show n - 1 ≤ 255 by omega)
    exact_mod_cast hp'
  rw [int_checked_width n hn0 hn]
  by_cases hnz : z = (BitVec.ofInt n z).toInt
  · have hr : -(2 ^ (n - 1)) ≤ z ∧ z < (2 : Int) ^ (n - 1) := (int_roundtrip_width n hn0 z).mp hnz
    have hf : z = (BitVec.ofInt 256 z).toInt := (int_roundtrip z).mpr (by omega)
    rw [if_pos hnz, if_pos hnz, if_pos hf]
  · rw [if_neg hnz, if_neg hnz]
    by_cases hf : z = (BitVec.ofInt 256 z).toInt
    · rw [if_pos hf, if_pos hf]
    · rw [if_neg hf]

/-- Explicit checked +,-,*: real preguard, primitive, then the real width predicate. -/
theorem uint_explicit_checked_all_widths {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (op : RingOp) (n : Nat) (hn : n ≤ 256) (x y : PrimTy.uint.Denote) :
    uintWidthResult n .panic (guardedValue σ (op.uintTerm x y)) =
      if op.ideal x.val y.val = ((BitVec.ofInt n (op.ideal x.val y.val)).toNat : Int)
      then .ok (op.ideal x.val y.val) else .error .panic := by
  rw [guardedValue_eq σ _ _ (op.uint_guard σ x y)]
  by_cases hf : op.ideal x.val y.val = ((BitVec.ofInt 256 (op.ideal x.val y.val)).toNat : Int)
  · have hb : decide (op.ideal x.val y.val = ((BitVec.ofInt 256 (op.ideal x.val y.val)).toNat : Int)) = true :=
      decide_eq_true hf
    rw [if_pos hb, op.uint_eval]
    simpa only [if_pos hf] using uint_preguard_width n hn (op.ideal x.val y.val)
  · have hb : ¬ decide (op.ideal x.val y.val = ((BitVec.ofInt 256 (op.ideal x.val y.val)).toNat : Int)) = true := by
      simpa only [decide_eq_true_eq] using hf
    rw [if_neg hb]
    change Except.error THalt.panic = _
    simpa only [if_neg hf] using uint_preguard_width n hn (op.ideal x.val y.val)

theorem int_explicit_checked_all_widths {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (op : RingOp) (n : Nat) (hn0 : 0 < n) (hn : n ≤ 256) (x y : PrimTy.int.Denote) :
    intWidthResult n .panic (guardedValue σ (op.intTerm x y)) =
      if op.ideal x.val y.val = (BitVec.ofInt n (op.ideal x.val y.val)).toInt
      then .ok (op.ideal x.val y.val) else .error .panic := by
  rw [guardedValue_eq σ _ _ (op.int_guard σ x y)]
  by_cases hf : op.ideal x.val y.val = (BitVec.ofInt 256 (op.ideal x.val y.val)).toInt
  · have hb : decide (op.ideal x.val y.val = (BitVec.ofInt 256 (op.ideal x.val y.val)).toInt) = true :=
      decide_eq_true hf
    rw [if_pos hb, op.int_eval]
    simpa only [if_pos hf] using int_preguard_width n hn0 hn (op.ideal x.val y.val)
  · have hb : ¬ decide (op.ideal x.val y.val = (BitVec.ofInt 256 (op.ideal x.val y.val)).toInt) = true := by
      simpa only [decide_eq_true_eq] using hf
    rw [if_neg hb]
    change Except.error THalt.panic = _
    simpa only [if_neg hf] using int_preguard_width n hn0 hn (op.ideal x.val y.val)

theorem int_guarded_width {C : Contract} {Γ : Ctx} (σ : State C Γ) (v : Val C Γ .int)
    (n : Nat) (hn0 : 0 < n) (hn : n ≤ 256) (z : Int)
    (he : v.evalT σ = TRes.ofOpt (PrimTy.int.ofInt? z))
    (hg : v.guard.map (fun g => g.evalT σ) = some (.ok (decide (z = (BitVec.ofInt 256 z).toInt)))) :
    intWidthResult n .panic (guardedValue σ v) =
      if z = (BitVec.ofInt n z).toInt then .ok z else .error .panic := by
  rw [guardedValue_eq σ v _ hg]
  simp only [decide_eq_true_eq, he]
  by_cases hf : z = (BitVec.ofInt 256 z).toInt
  · rw [if_pos hf]
    simpa only [if_pos hf] using int_preguard_width n hn0 hn z
  · rw [if_neg hf]
    change Except.error THalt.panic = _
    simpa only [if_neg hf] using int_preguard_width n hn0 hn z

theorem int_neg_explicit_checked_all_widths {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (n : Nat) (hn0 : 0 < n) (hn : n ≤ 256) (x : PrimTy.int.Denote) :
    intWidthResult n .panic (guardedValue σ (.unop .neg rfl rfl (litInt x))) =
      if -x.val = (-BitVec.ofInt n x.val).toInt then .ok (-x.val) else .error .panic := by
  have he : (Val.unop .neg rfl rfl (litInt x)).evalT σ = TRes.ofOpt (PrimTy.int.ofInt? (-x.val)) := rfl
  have hg : (Val.unop .neg rfl rfl (litInt x)).guard.map (fun g => g.evalT σ) =
      some (.ok (decide (-x.val = (BitVec.ofInt 256 (-x.val)).toInt))) := by
    simpa only [BitVec.ofInt_neg] using int_neg_guard σ x
  simpa only [BitVec.ofInt_neg] using int_guarded_width σ _ n hn0 hn (-x.val) he hg

theorem int_div_explicit_checked_all_widths {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (n : Nat) (hn0 : 0 < n) (hn : n ≤ 256) (x y : PrimTy.int.Denote) :
    intWidthResult n .panic (guardedValue σ (.binop .div rfl rfl (litInt x) (litInt y))) =
      if y.val = 0 then .error .revert else
      if x.val.tdiv y.val = (BitVec.ofInt n (x.val.tdiv y.val)).toInt
      then .ok (x.val.tdiv y.val) else .error .panic := by
  by_cases hz : y.val = 0
  · rw [if_pos hz]
    have hcond : ¬ (x.val = Checked.minI ∧ y.val = -1) := by omega
    have hg : (Val.binop .div rfl rfl (litInt x) (litInt y)).guard.map (fun g => g.evalT σ) =
        some (.ok true) := by
      simpa only [hcond, decide_true] using int_div_guard σ x y
    rw [guardedValue_eq σ _ true hg, if_pos rfl]
    have he : (Val.binop .div rfl rfl (litInt x) (litInt y)).evalT σ = .error .revert := by
      simp only [Val.evalT.eq_3, litInt_eval, BinOp.shortT, ok_bind, BinOp.evalT,
        BinOp.evalNum, BinOp.arithInt, if_pos hz, Option.bind_none, TRes.ofOpt]
    rw [he]
    rfl
  · rw [if_neg hz]
    have he : (Val.binop .div rfl rfl (litInt x) (litInt y)).evalT σ =
        TRes.ofOpt (PrimTy.int.ofInt? (x.val.tdiv y.val)) := by
      simp only [Val.evalT.eq_3, litInt_eval, BinOp.shortT, ok_bind, BinOp.evalT,
        BinOp.evalNum, BinOp.arithInt, if_neg hz, Option.bind_some]
    have hcond : (¬ (x.val = Checked.minI ∧ y.val = -1)) ↔
        x.val.tdiv y.val = (BitVec.ofInt 256 (x.val.tdiv y.val)).toInt := by
      rw [int_roundtrip]
      have hbound : -(2 ^ 255) ≤ x.val ∧ x.val < (2 : Int) ^ 255 := core_int_bounds x
      have hiff : (¬ (x.val = -(2 : Int) ^ 255 ∧ y.val = -1)) ↔
          (-(2 ^ 255) ≤ x.val.tdiv y.val ∧ x.val.tdiv y.val ≤ (2 : Int) ^ 255 - 1) :=
        Checked.div_int_exact (by decide : (0 : Int) < 2 ^ 255) hbound hz
      rw [minI_value]
      omega
    have hg : (Val.binop .div rfl rfl (litInt x) (litInt y)).guard.map (fun g => g.evalT σ) =
        some (.ok (decide (x.val.tdiv y.val = (BitVec.ofInt 256 (x.val.tdiv y.val)).toInt))) := by
      simpa only [hcond] using int_div_guard σ x y
    exact int_guarded_width σ _ n hn0 hn _ he hg

/-- Power has no full-width preguard; this equation preserves its actual revert-before-width-check behavior. -/
theorem uint_pow_explicit_checked_all_widths {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (n : Nat) (hn : n ≤ 256) (x y : PrimTy.uint.Denote) :
    uintWidthResult n .panic (guardedValue σ (.binop .pow rfl rfl (litUInt x) (litUInt y))) =
      if x.val ^ y.val.toNat = (((BitVec.ofInt n x.val) ^ y.val.toNat).toNat : Int)
      then .ok (x.val ^ y.val.toNat) else
      if x.val ^ y.val.toNat = (((BitVec.ofInt 256 x.val) ^ y.val.toNat).toNat : Int)
      then .error .panic else .error .revert := by
  have hg : (Val.binop (C := C) (Γ := Γ) .pow rfl rfl (litUInt x) (litUInt y)).guard = none := by
    simp only [Val.guard, litUInt, Checked.andO, Option.isSome_none, Bool.false_and,
      Bool.false_eq_true, if_false, BinOp.isArith, if_true, Checked.range, Checked.rangeU]
  unfold guardedValue
  rw [hg]
  have he : (Val.binop .pow rfl rfl (litUInt x) (litUInt y)).evalT σ =
      TRes.ofOpt (WrapOp.pow.checkedUint x y) := rfl
  rw [he]
  simpa only [WrapOp.ideal, WrapOp.word, ofInt_pow] using
    uint_checked_all_widths .pow n hn .panic x y

/-- The checked signed quotient reference on genuine n-bit operands is sdiv. -/
theorem int_div_explicit_checked_words {C : Contract} {Γ : Ctx} (σ : State C Γ)
    {n : Nat} (hn0 : 0 < n) (hn : n ≤ 256) (x y : BitVec n) :
    intWidthResult n .panic (guardedValue σ
      (.binop .div rfl rfl (litInt (signedN hn x)) (litInt (signedN hn y)))) =
      if y.toInt = 0 then .error .revert else
      if x.toInt.tdiv y.toInt = (x.sdiv y).toInt then .ok (x.toInt.tdiv y.toInt) else .error .panic := by
  rw [int_div_explicit_checked_all_widths σ n hn0 hn]
  simp only [signedN, BitVec.toInt_ofInt, BitVec.toInt_sdiv]

end Solidity.Bridge.Arith

#print axioms Solidity.Bridge.Arith.RingOp.uint_guard
#print axioms Solidity.Bridge.Arith.RingOp.int_guard
#print axioms Solidity.Bridge.Arith.uint_explicit_checked_all_widths
#print axioms Solidity.Bridge.Arith.int_explicit_checked_all_widths

#print axioms Solidity.Bridge.Arith.int_neg_explicit_checked_all_widths
#print axioms Solidity.Bridge.Arith.int_div_explicit_checked_all_widths
#print axioms Solidity.Bridge.Arith.uint_pow_explicit_checked_all_widths

#print axioms Solidity.Bridge.Arith.guardedValue_assert_then
#print axioms Solidity.Bridge.Arith.int_div_explicit_checked_words
