import SolidityBridge.Arith.SignedDivision
import Solidity.Syntax.CheckedExact

set_option maxRecDepth 2048

namespace Solidity.Bridge.Arith

/-- An arbitrary core operand as a pure typed value, not a range-restricted test sample. -/
def litUInt {C : Contract} {Γ : Ctx} (x : PrimTy.uint.Denote) : Val C Γ .uint :=
  .simple (.lit x.val x.property)
def litInt {C : Contract} {Γ : Ctx} (x : PrimTy.int.Denote) : Val C Γ .int :=
  .simple (.lit x.val x.property)

theorem litUInt_eval {C : Contract} {Γ : Ctx} (σ : State C Γ) (x : PrimTy.uint.Denote) :
    (litUInt x).evalT σ = .ok x := rfl

theorem litInt_eval {C : Contract} {Γ : Ctx} (σ : State C Γ) (x : PrimTy.int.Denote) :
    (litInt x).evalT σ = .ok x := rfl

/-- The actual uint addition guard evaluates exactly to the BitVec overflow test. -/
theorem uint_add_guard {C : Contract} {Γ : Ctx} (σ : State C Γ) (x y : PrimTy.uint.Denote) :
    (Checked.rangeU .add (litUInt x) (litUInt y)).map (fun g => g.evalT σ) =
      some (.ok (decide (x.val + y.val =
        ((BitVec.ofInt 256 x.val + BitVec.ofInt 256 y.val).toNat : Int)))) := by
  obtain ⟨r, hr, hv⟩ := Widths.uint_value_of_map _ _ (uint_mod (x.val + y.val))
  have he : BinOp.addW.evalT rfl x y = some r := hr
  simp only [Checked.rangeU, Checked.cmpU, Checked.arU, Option.map_some,
    Val.evalT.eq_3, litUInt_eval, BinOp.shortT, ok_bind, he]
  simp only [TRes.ofOpt, ok_bind, BinOp.evalT, BinOp.evalNum]
  rw [hv]
  have hx : 0 ≤ x.val := PrimTy.uint_nonneg x
  have hy : 0 ≤ y.val := PrimTy.uint_nonneg y
  have hxb : x.val < Semantics.uintBound := by
    simpa only [PrimTy.inRange, decide_eq_true_eq] using (show 0 ≤ x.val ∧ x.val < Semantics.uintBound from by
      simpa only [PrimTy.inRange, decide_eq_true_eq] using x.property).2
  have hyb : y.val < Semantics.uintBound := by
    simpa only [PrimTy.inRange, decide_eq_true_eq] using (show 0 ≤ y.val ∧ y.val < Semantics.uintBound from by
      simpa only [PrimTy.inRange, decide_eq_true_eq] using y.property).2
  have hg : x.val ≤ (x.val + y.val) % Semantics.uintBound ↔
      x.val + y.val = ((BitVec.ofInt 256 x.val + BitVec.ofInt 256 y.val).toNat : Int) := by
    rw [Checked.add_uint_exact hx hxb hy hyb, ← BitVec.ofInt_add,
      uint_roundtrip]
    simp only [Semantics.uintBound, Nat.cast_pow, Nat.cast_ofNat] at *
    omega
  simp only [hg]

theorem uint_sub_guard {C : Contract} {Γ : Ctx} (σ : State C Γ) (x y : PrimTy.uint.Denote) :
    (Checked.rangeU .sub (litUInt x) (litUInt y)).map (fun g => g.evalT σ) =
      some (.ok (decide (x.val - y.val =
        ((BitVec.ofInt 256 x.val - BitVec.ofInt 256 y.val).toNat : Int)))) := by
  simp only [Checked.rangeU, Checked.cmpU, Option.map_some, Val.evalT.eq_3,
    litUInt_eval, BinOp.shortT, ok_bind, BinOp.evalT, BinOp.evalNum, TRes.ofOpt]
  have hx : 0 ≤ x.val ∧ x.val < (2 : Int) ^ 256 := by
    simpa only [PrimTy.inRange, decide_eq_true_eq, Nat.cast_pow, Nat.cast_ofNat] using x.property
  have hy : 0 ≤ y.val := PrimTy.uint_nonneg y
  have he : y.val ≤ x.val ↔ x.val - y.val =
      ((BitVec.ofInt 256 x.val - BitVec.ofInt 256 y.val).toNat : Int) := by
    rw [← ofInt_sub, uint_roundtrip]
    omega
  simp only [he]

theorem int_neg_guard {C : Contract} {Γ : Ctx} (σ : State C Γ) (x : PrimTy.int.Denote) :
    (Checked.negRange .int (litInt x)).map (fun g => g.evalT σ) =
      some (.ok (decide (-x.val = (-BitVec.ofInt 256 x.val).toInt))) := by
  simp only [Checked.negRange, Checked.cmpI, Checked.litI, Option.map_some,
    Val.evalT.eq_3, Val.evalT.eq_1, Simple.evalT, litInt_eval, BinOp.shortT,
    ok_bind, BinOp.evalT, BinOp.evalNum, PrimTy.ofLit, TRes.ofOpt]
  have hx : -(2 ^ 255) ≤ x.val ∧ x.val < (2 : Int) ^ 255 := by
    simpa only [PrimTy.inRange, decide_eq_true_eq, Nat.cast_pow, Nat.cast_ofNat] using x.property
  have he : x.val ≠ Checked.minI ↔ -x.val = (-BitVec.ofInt 256 x.val).toInt := by
    rw [← BitVec.ofInt_neg, int_roundtrip]
    simp only [Checked.minI, Nat.cast_pow, Nat.cast_ofNat]
    omega
  simp only [ne_eq, decide_not, ← he]

/-- This guard rejects signed overflow; division by zero is left to the evaluator. -/
theorem int_div_guard {C : Contract} {Γ : Ctx} (σ : State C Γ) (x y : PrimTy.int.Denote) :
    (Checked.rangeI .div (litInt x) (litInt y)).map (fun g => g.evalT σ) =
      some (.ok (decide (¬ (x.val = Checked.minI ∧ y.val = -1)))) := by
  simp only [Checked.rangeI, Checked.notB, Checked.andB, Checked.cmpI, Checked.litI,
    Option.map_some, Val.evalT.eq_3, Val.evalT.eq_4, Val.evalT.eq_1, Simple.evalT,
    litInt_eval, BinOp.shortT, ok_bind, BinOp.evalT, BinOp.evalNum, PrimTy.ofLit,
    TRes.ofOpt, BinOp.ret, BinOp.isArith, boolT, BinOp.evalBool, UnOp.evalT,
    decide_not]
  by_cases hx : x.val = Checked.minI <;>
    simp only [hx, decide_true, decide_false, Bool.false_eq_true, if_false, if_true,
      Bool.true_and, true_and, false_and, pure, Except.pure, ok_bind]

theorem core_int_bounds (x : PrimTy.int.Denote) :
    -(2 ^ 255) ≤ x.val ∧ x.val < (2 : Int) ^ 255 := by
  simpa only [PrimTy.inRange, decide_eq_true_eq, Nat.cast_pow, Nat.cast_ofNat] using x.property

theorem core_int_result (z : Int) (hz : -(2 ^ 255) ≤ z ∧ z < (2 : Int) ^ 255) :
    ∃ r : PrimTy.int.Denote, PrimTy.int.ofInt? z = some r ∧ r.val = z := by
  have he : (PrimTy.int.ofInt? z).map Subtype.val = some z := by rw [int_check, if_pos hz]
  cases h : PrimTy.int.ofInt? z with
  | none => rw [h] at he; cases he
  | some r =>
    rw [h, Option.map_some] at he
    exact ⟨r, rfl, Option.some.inj he⟩

theorem maxI_value : Checked.maxI = (2 : Int) ^ 255 - 1 := by
  simp only [Checked.maxI, Nat.cast_sub (by decide : 1 ≤ (2 : Nat) ^ 255),
    Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
theorem minI_value : Checked.minI = -(2 : Int) ^ 255 := by
  simp only [Checked.minI, Nat.cast_pow, Nat.cast_ofNat]

theorem int_add_guard {C : Contract} {Γ : Ctx} (σ : State C Γ) (x y : PrimTy.int.Denote) :
    (Checked.rangeI .add (litInt x) (litInt y)).map (fun g => g.evalT σ) =
      some (.ok (decide (x.val + y.val =
        (BitVec.ofInt 256 x.val + BitVec.ofInt 256 y.val).toInt))) := by
  have hx : -(2 ^ 255) ≤ x.val ∧ x.val < (2 : Int) ^ 255 := core_int_bounds x
  have hy : -(2 ^ 255) ≤ y.val ∧ y.val < (2 : Int) ^ 255 := core_int_bounds y
  have hg : (if 0 ≤ y.val then x.val ≤ Checked.maxI - y.val else Checked.minI - y.val ≤ x.val) ↔
      x.val + y.val = (BitVec.ofInt 256 x.val + BitVec.ofInt 256 y.val).toInt := by
    rw [maxI_value, minI_value, Checked.add_int_exact hx, ← BitVec.ofInt_add, int_roundtrip]
    omega
  by_cases hs : 0 ≤ y.val
  · obtain ⟨r, hr, hv⟩ := core_int_result (Checked.maxI - y.val) (by rw [maxI_value]; omega)
    simp only [Checked.rangeI, Checked.cmpI, Checked.arI, Checked.litI, Option.map_some,
      Val.evalT, Simple.evalT, litInt, BinOp.shortT, ok_bind, PrimTy.ofLit,
      BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Option.bind_some, hr, TRes.ofOpt, boolT, decide_eq_true_eq, if_pos hs]
    rw [hv]
    have he : x.val ≤ Checked.maxI - y.val ↔
        x.val + y.val = (BitVec.ofInt 256 x.val + BitVec.ofInt 256 y.val).toInt := by
      simpa only [if_pos hs] using hg
    simp only [he]
  · obtain ⟨r, hr, hv⟩ := core_int_result (Checked.minI - y.val) (by rw [minI_value]; omega)
    simp only [Checked.rangeI, Checked.cmpI, Checked.arI, Checked.litI, Option.map_some,
      Val.evalT, Simple.evalT, litInt, BinOp.shortT, ok_bind, PrimTy.ofLit,
      BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Option.bind_some, hr, TRes.ofOpt, boolT, decide_eq_true_eq, if_neg hs]
    rw [hv]
    have he : Checked.minI - y.val ≤ x.val ↔
        x.val + y.val = (BitVec.ofInt 256 x.val + BitVec.ofInt 256 y.val).toInt := by
      simpa only [if_neg hs] using hg
    simp only [he]

theorem int_sub_guard {C : Contract} {Γ : Ctx} (σ : State C Γ) (x y : PrimTy.int.Denote) :
    (Checked.rangeI .sub (litInt x) (litInt y)).map (fun g => g.evalT σ) =
      some (.ok (decide (x.val - y.val =
        (BitVec.ofInt 256 x.val - BitVec.ofInt 256 y.val).toInt))) := by
  have hx : -(2 ^ 255) ≤ x.val ∧ x.val < (2 : Int) ^ 255 := core_int_bounds x
  have hy : -(2 ^ 255) ≤ y.val ∧ y.val < (2 : Int) ^ 255 := core_int_bounds y
  have hg : (if 0 ≤ y.val then Checked.minI + y.val ≤ x.val else x.val ≤ Checked.maxI + y.val) ↔
      x.val - y.val = (BitVec.ofInt 256 x.val - BitVec.ofInt 256 y.val).toInt := by
    rw [maxI_value, minI_value, Checked.sub_int_exact hx, ← ofInt_sub, int_roundtrip]
    omega
  by_cases hs : 0 ≤ y.val
  · obtain ⟨r, hr, hv⟩ := core_int_result (Checked.minI + y.val) (by rw [minI_value]; omega)
    simp only [Checked.rangeI, Checked.cmpI, Checked.arI, Checked.litI, Option.map_some,
      Val.evalT, Simple.evalT, litInt, BinOp.shortT, ok_bind, PrimTy.ofLit,
      BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Option.bind_some, hr, TRes.ofOpt, boolT, decide_eq_true_eq, if_pos hs]
    rw [hv]
    have he : Checked.minI + y.val ≤ x.val ↔
        x.val - y.val = (BitVec.ofInt 256 x.val - BitVec.ofInt 256 y.val).toInt := by
      simpa only [if_pos hs] using hg
    simp only [he]
  · obtain ⟨r, hr, hv⟩ := core_int_result (Checked.maxI + y.val) (by rw [maxI_value]; omega)
    simp only [Checked.rangeI, Checked.cmpI, Checked.arI, Checked.litI, Option.map_some,
      Val.evalT, Simple.evalT, litInt, BinOp.shortT, ok_bind, PrimTy.ofLit,
      BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Option.bind_some, hr, TRes.ofOpt, boolT, decide_eq_true_eq, if_neg hs]
    rw [hv]
    have he : x.val ≤ Checked.maxI + y.val ↔
        x.val - y.val = (BitVec.ofInt 256 x.val - BitVec.ofInt 256 y.val).toInt := by
      simpa only [if_neg hs] using hg
    simp only [he]

theorem uint_mul_guard {C : Contract} {Γ : Ctx} (σ : State C Γ) (x y : PrimTy.uint.Denote) :
    (Checked.rangeU .mul (litUInt x) (litUInt y)).map (fun g => g.evalT σ) =
      some (.ok (decide (x.val * y.val =
        ((BitVec.ofInt 256 x.val * BitVec.ofInt 256 y.val).toNat : Int)))) := by
  have hx : 0 ≤ x.val ∧ x.val < Semantics.uintBound := by
    simpa only [PrimTy.inRange, decide_eq_true_eq] using x.property
  have hy : 0 ≤ y.val ∧ y.val < Semantics.uintBound := by
    simpa only [PrimTy.inRange, decide_eq_true_eq] using y.property
  have hg : (x.val = 0 ∨ (x.val * y.val % Semantics.uintBound).tdiv x.val = y.val) ↔
      x.val * y.val = ((BitVec.ofInt 256 x.val * BitVec.ofInt 256 y.val).toNat : Int) := by
    rw [Checked.mul_uint_exact hx.1 hx.2 hy.1 hy.2, ← BitVec.ofInt_mul, uint_roundtrip]
    simp only [Semantics.uintBound, Nat.cast_pow, Nat.cast_ofNat] at *
    exact ⟨fun h => ⟨Int.mul_nonneg hx.1 hy.1, h⟩, And.right⟩
  by_cases hz : x.val = 0
  · have he : x.val * y.val = ((BitVec.ofInt 256 x.val * BitVec.ofInt 256 y.val).toNat : Int) :=
      hg.mp (Or.inl hz)
    simp only [Checked.rangeU, Checked.orB, Checked.cmpU, Checked.arU, Checked.litU, Option.map_some,
      Val.evalT, Simple.evalT, litUInt, BinOp.shortT, ok_bind, PrimTy.ofLit, BinOp.evalT,
      BinOp.evalNum, TRes.ofOpt, BinOp.ret, BinOp.isArith, hz, decide_true, boolT, if_true, pure,
      Except.pure]
    have he0 : (0 : Int) * y.val = ((BitVec.ofInt 256 0 * BitVec.ofInt 256 y.val).toNat : Int) := by
      simpa only [hz] using he
    simp only [he0, decide_true]
  · obtain ⟨r, hr, hv⟩ := Widths.uint_value_of_map _ _ (uint_mod (x.val * y.val))
    have hdiv : (BinOp.div.evalT rfl r x).map Subtype.val = some (r.val.tdiv x.val) := by
      rw [uint_div_exact, if_neg hz, ← uint_div_word]
    obtain ⟨q, hq, hqv⟩ := Widths.uint_value_of_map _ _ hdiv
    change ((if x.val = 0 then none else some (r.val.tdiv x.val)).bind PrimTy.uint.ofInt?) = some q at hq
    rw [if_neg hz, Option.bind_some] at hq
    have hmul : BinOp.mulW.evalT rfl x y = some r := hr
    simp only [Checked.rangeU, Checked.orB, Checked.cmpU, Checked.arU, Checked.litU, Option.map_some,
      Val.evalT, Simple.evalT, litUInt, BinOp.shortT, ok_bind, PrimTy.ofLit, hq, BinOp.evalT,
      BinOp.evalNum, BinOp.arithInt, Option.bind_some, hr, TRes.ofOpt, BinOp.ret, BinOp.isArith, hz,
      decide_false, boolT, if_false, pure, Except.pure]
    dsimp only [BinOp.ret, BinOp.isArith]
    simp only [Bool.false_eq_true, if_false, BinOp.evalBool]
    rw [hqv, hv]
    have he : (x.val * y.val % Semantics.uintBound).tdiv x.val = y.val ↔
        x.val * y.val = ((BitVec.ofInt 256 x.val * BitVec.ofInt 256 y.val).toNat : Int) := by
      simpa only [hz, false_or] using hg
    simp only [he, Bool.false_or]

/-- Exact checked division range, available for the guard's safe intermediate quotients. -/
theorem core_int_div_result (a b : PrimTy.int.Denote) (hb : b.val ≠ 0)
    (ho : ¬ (a.val = Checked.minI ∧ b.val = -1)) :
    ∃ r : PrimTy.int.Denote, PrimTy.int.ofInt? (a.val.tdiv b.val) = some r ∧
      r.val = a.val.tdiv b.val := by
  have ha : -(2 ^ 255) ≤ a.val ∧ a.val < (2 : Int) ^ 255 := core_int_bounds a
  have hg : -(2 ^ 255) ≤ a.val.tdiv b.val ∧ a.val.tdiv b.val ≤ (2 : Int) ^ 255 - 1 :=
    (Checked.div_int_exact (by decide : (0 : Int) < 2 ^ 255) ha hb).mp
      (by simpa only [minI_value] using ho)
  exact core_int_result _ ⟨hg.1, by omega⟩

/-- The actual nested signed multiplication guard, including its protected intermediate operations. -/
theorem int_mul_guard {C : Contract} {Γ : Ctx} (σ : State C Γ) (x y : PrimTy.int.Denote) :
    (Checked.rangeI .mul (litInt x) (litInt y)).map (fun g => g.evalT σ) =
      some (.ok (decide (x.val * y.val =
        (BitVec.ofInt 256 x.val * BitVec.ofInt 256 y.val).toInt))) := by
  have hx : -(2 ^ 255) ≤ x.val ∧ x.val < (2 : Int) ^ 255 := core_int_bounds x
  have hy : -(2 ^ 255) ≤ y.val ∧ y.val < (2 : Int) ^ 255 := core_int_bounds y
  have hg : (x.val = 0 ∨ y.val = 0 ∨
      (if 0 < x.val then (if 0 < y.val then x.val ≤ Checked.maxI.tdiv y.val else Checked.minI.tdiv x.val ≤ y.val)
       else (if 0 < y.val then Checked.minI.tdiv y.val ≤ x.val
         else (x.val ≠ Checked.minI ∧ y.val ≠ Checked.minI ∧ 0 - x.val ≤ Checked.maxI.tdiv (0 - y.val))))) ↔
      x.val * y.val = (BitVec.ofInt 256 x.val * BitVec.ofInt 256 y.val).toInt := by
    rw [maxI_value, minI_value, Checked.mul_int_exact (by decide : (0 : Int) < 2 ^ 255) hx hy,
      ← BitVec.ofInt_mul, int_roundtrip]
    omega
  simp only [← hg]
  have hmin0 : Checked.minI ≠ 0 := by rw [minI_value]; decide +kernel
  have hminp : ¬ (0 < Checked.minI) := by rw [minI_value]; decide +kernel
  let imax : PrimTy.int.Denote := ⟨Checked.maxI, by decide⟩
  let imin : PrimTy.int.Denote := ⟨Checked.minI, by decide⟩
  by_cases hx0 : x.val = 0
  · simp only [Checked.rangeI, Checked.orB, Checked.andB, Checked.cmpI, Checked.arI, Checked.litI,
    Option.map_some, Val.evalT, Simple.evalT, litInt, BinOp.shortT, ok_bind, PrimTy.ofLit,
    BinOp.evalT, BinOp.evalNum, BinOp.arithInt, BinOp.evalBool, TRes.ofOpt, BinOp.ret, BinOp.isArith,
    boolT, pure, Except.pure, if_true, decide_true, true_or, ne_eq, Option.bind_some, hx0]
  try rfl
  · by_cases hy0 : y.val = 0
    · simp only [Checked.rangeI, Checked.orB, Checked.andB, Checked.cmpI, Checked.arI, Checked.litI,
      Option.map_some, Val.evalT, Simple.evalT, litInt, BinOp.shortT, ok_bind, PrimTy.ofLit,
      BinOp.evalT, BinOp.evalNum, BinOp.arithInt, BinOp.evalBool, TRes.ofOpt, BinOp.ret,
      BinOp.isArith, boolT, pure, Except.pure, Bool.false_eq_true, if_false, if_true, decide_true,
      decide_false, true_or, or_true, Bool.false_or, ne_eq, Option.bind_some, hx0, hy0]
    try rfl
    · by_cases hxp : 0 < x.val
      · by_cases hyp : 0 < y.val
        · obtain ⟨q, hq, hqv⟩ := core_int_div_result imax y hy0 (by
            intro h; have h1 : y.val = -1 := h.2; omega)
          change PrimTy.int.ofInt? (Checked.maxI.tdiv y.val) = some q at hq
          change q.val = Checked.maxI.tdiv y.val at hqv
          simp only [Checked.rangeI, Checked.orB, Checked.andB, Checked.cmpI, Checked.arI, Checked.litI,
            Option.map_some, Val.evalT, Simple.evalT, litInt, BinOp.shortT, ok_bind, PrimTy.ofLit,
            BinOp.evalT, BinOp.evalNum, BinOp.arithInt, BinOp.evalBool, TRes.ofOpt, BinOp.ret,
            BinOp.isArith, boolT, pure, Except.pure, Bool.false_eq_true, if_false, if_true,
            decide_true, decide_false, false_or, Bool.false_or, ne_eq, Option.bind_some, hx0, hy0,
            hxp, hyp, hq, hqv]
          try rfl
        · obtain ⟨q, hq, hqv⟩ := core_int_div_result imin x hx0 (by
            intro h; have h1 : x.val = -1 := h.2; omega)
          change PrimTy.int.ofInt? (Checked.minI.tdiv x.val) = some q at hq
          change q.val = Checked.minI.tdiv x.val at hqv
          simp only [Checked.rangeI, Checked.orB, Checked.andB, Checked.cmpI, Checked.arI, Checked.litI,
            Option.map_some, Val.evalT, Simple.evalT, litInt, BinOp.shortT, ok_bind, PrimTy.ofLit,
            BinOp.evalT, BinOp.evalNum, BinOp.arithInt, BinOp.evalBool, TRes.ofOpt, BinOp.ret,
            BinOp.isArith, boolT, pure, Except.pure, Bool.false_eq_true, if_false, if_true,
            decide_true, decide_false, false_or, Bool.false_or, ne_eq, Option.bind_some, hx0, hy0,
            hxp, hyp, hq, hqv]
          try rfl
      · by_cases hyp : 0 < y.val
        · obtain ⟨q, hq, hqv⟩ := core_int_div_result imin y hy0 (by
            intro h; have h1 : y.val = -1 := h.2; omega)
          change PrimTy.int.ofInt? (Checked.minI.tdiv y.val) = some q at hq
          change q.val = Checked.minI.tdiv y.val at hqv
          simp only [Checked.rangeI, Checked.orB, Checked.andB, Checked.cmpI, Checked.arI, Checked.litI,
            Option.map_some, Val.evalT, Simple.evalT, litInt, BinOp.shortT, ok_bind, PrimTy.ofLit,
            BinOp.evalT, BinOp.evalNum, BinOp.arithInt, BinOp.evalBool, TRes.ofOpt, BinOp.ret,
            BinOp.isArith, boolT, pure, Except.pure, Bool.false_eq_true, if_false, if_true,
            decide_true, decide_false, false_or, Bool.false_or, ne_eq, Option.bind_some, hx0, hy0,
            hxp, hyp, hq, hqv]
          try rfl
        · by_cases hxm : x.val = Checked.minI
          · simp only [Checked.rangeI, Checked.orB, Checked.andB, Checked.cmpI, Checked.arI, Checked.litI,
            Option.map_some, Val.evalT, Simple.evalT, litInt, BinOp.shortT, ok_bind, PrimTy.ofLit,
            BinOp.evalT, BinOp.evalNum, BinOp.arithInt, BinOp.evalBool, TRes.ofOpt, BinOp.ret,
            BinOp.isArith, boolT, pure, Except.pure, Bool.false_eq_true, if_false, decide_true,
            decide_false, false_or, false_and, not_true_eq_false, Bool.false_or, Bool.not_true,
            hmin0, hminp, ne_eq, Option.bind_some, hy0, hyp, hxm]
          try rfl
          · by_cases hym : y.val = Checked.minI
            · simp only [Checked.rangeI, Checked.orB, Checked.andB, Checked.cmpI, Checked.arI, Checked.litI,
              Option.map_some, Val.evalT, Simple.evalT, litInt, BinOp.shortT, ok_bind, PrimTy.ofLit,
              BinOp.evalT, BinOp.evalNum, BinOp.arithInt, BinOp.evalBool, TRes.ofOpt, BinOp.ret,
              BinOp.isArith, boolT, pure, Except.pure, Bool.false_eq_true, if_false, if_true,
              decide_true, decide_false, false_or, false_and, and_false, not_true_eq_false,
              not_false_eq_true, Bool.true_and, Bool.false_or, Bool.not_true, Bool.not_false, hmin0,
              hminp, ne_eq, Option.bind_some, hx0, hxp, hxm, hym]
            try rfl
            · obtain ⟨nx, hnx, hnxv⟩ := core_int_result (0 - x.val) (by rw [minI_value] at hxm; omega)
              obtain ⟨ny, hny, hnyv⟩ := core_int_result (0 - y.val) (by rw [minI_value] at hym; omega)
              obtain ⟨q, hq, hqv⟩ := core_int_div_result imax ny (by rw [hnyv]; omega) (by
                intro h; have h1 : ny.val = -1 := h.2; rw [hnyv] at h1; omega)
              change PrimTy.int.ofInt? (Checked.maxI.tdiv ny.val) = some q at hq
              change q.val = Checked.maxI.tdiv ny.val at hqv
              rw [hnyv] at hq hqv
              have hden : 0 - y.val ≠ 0 := by omega
              simp only [Checked.rangeI, Checked.orB, Checked.andB, Checked.cmpI, Checked.arI, Checked.litI,
                Option.map_some, Val.evalT, Simple.evalT, litInt, BinOp.shortT, ok_bind,
                PrimTy.ofLit, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, BinOp.evalBool, TRes.ofOpt,
                BinOp.ret, BinOp.isArith, boolT, pure, Except.pure, Bool.false_eq_true, if_false,
                if_true, decide_false, false_or, true_and, not_false_eq_true, Bool.true_and,
                Bool.false_or, Bool.not_false, ne_eq, Option.bind_some, hx0, hy0, hxp, hyp, hxm, hym,
                hnx, hny, hq, hnxv, hnyv, hqv, hden]
              try rfl

end Solidity.Bridge.Arith

#print axioms Solidity.Bridge.Arith.uint_add_guard

#print axioms Solidity.Bridge.Arith.uint_sub_guard
#print axioms Solidity.Bridge.Arith.int_neg_guard
#print axioms Solidity.Bridge.Arith.int_div_guard

#print axioms Solidity.Bridge.Arith.int_add_guard

#print axioms Solidity.Bridge.Arith.int_sub_guard

#print axioms Solidity.Bridge.Arith.uint_mul_guard

#print axioms Solidity.Bridge.Arith.int_mul_guard
