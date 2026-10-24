import SolidityBridge.Arith.Widths

namespace Solidity.Bridge.Arith
open Widths

/-- The typed term checked from lowBits, including its full-width identity branch. -/
def cutUInt {C : Contract} {Γ : Ctx} (n : Nat) (v : Val C Γ .uint) : Val C Γ .uint :=
  if h : n < 256 then lowFrom v n (pow_uint_range n h) else v

/-- The typed term checked from signedAt, including the full-width signed cast. -/
def cutInt {C : Contract} {Γ : Ctx} (n : Nat) (v : Val C Γ .uint) : Val C Γ .int :=
  if h : n < 256 then
    signedFrom v n (pow_uint_range (n - 1) (by omega)) (pow_uint_range n h)
  else .unop .toInt rfl rfl v

theorem cutUInt_eval {C : Contract} {Γ : Ctx} (σ : State C Γ) (n : Nat)
    (hn : n ≤ 256) (v : Val C Γ .uint) :
    ((cutUInt n v).evalT σ).map Subtype.val =
      (v.evalT σ >>= fun x => .ok ((BitVec.ofInt n x.val).toNat : Int)) := by
  unfold cutUInt
  split
  · exact lowFrom_eval σ v n ‹n < 256› _
  · have he : n = 256 := by omega
    subst n
    cases h : v.evalT σ with
    | error e => rfl
    | ok x => simp only [Except.map, ok_bind, uint_decode]

theorem cutInt_eval {C : Contract} {Γ : Ctx} (σ : State C Γ) (n : Nat)
    (hn0 : 0 < n) (hn : n ≤ 256) (v : Val C Γ .uint) :
    ((cutInt n v).evalT σ).map Subtype.val =
      (v.evalT σ >>= fun x => .ok (BitVec.ofInt n x.val).toInt) := by
  unfold cutInt
  split
  · exact signedFrom_eval σ v n hn0 ‹n < 256› _ _
  · have he : n = 256 := by omega
    subst n
    cases h : v.evalT σ with
    | error e => simp only [Val.evalT.eq_4, h, bind, Except.bind, Except.map]
    | ok x =>
      simp only [Val.evalT.eq_4, h, ok_bind]
      rw [map_ofOpt, toInt_word]
      rfl

theorem setWidth_full_word (n : Nat) (hn : n ≤ 256) (z : Int) :
    (BitVec.ofInt 256 z).setWidth n = BitVec.ofInt n z := by
  rw [← BitVec.ofNat_toNat n, ← BitVec.ofInt_natCast, BitVec.toNat_ofInt,
    Int.toNat_of_nonneg (Int.emod_nonneg z (by decide))]
  exact cut_full_word z n hn

inductive WrapOp where | add | sub | mul | pow

def WrapOp.bin : WrapOp → BinOp
  | .add => .addW | .sub => .subW | .mul => .mulW | .pow => .powW

def WrapOp.ideal : WrapOp → Int → Int → Int
  | .add, x, y => x + y | .sub, x, y => x - y
  | .mul, x, y => x * y | .pow, x, y => x ^ y.toNat

def WrapOp.word {n : Nat} : WrapOp → BitVec n → BitVec n → Nat → BitVec n
  | .add, x, y, _ => x + y | .sub, x, y, _ => x - y
  | .mul, x, y, _ => x * y | .pow, x, _, k => x ^ k

theorem WrapOp.accepts (op : WrapOp) : op.bin.accepts .uint = true := by cases op <;> rfl

theorem WrapOp.ret (op : WrapOp) : op.bin.ret .uint = .uint := by cases op <;> rfl

def WrapOp.term {C : Contract} {Γ : Ctx} (op : WrapOp) (v w : Val C Γ .uint) :
    Val C Γ .uint := .binop op.bin op.accepts op.ret v w

def WrapOp.eval : WrapOp → PrimTy.uint.Denote → PrimTy.uint.Denote → Option PrimTy.uint.Denote
  | .add => BinOp.addW.evalT rfl | .sub => BinOp.subW.evalT rfl
  | .mul => BinOp.mulW.evalT rfl | .pow => BinOp.powW.evalT rfl

theorem WrapOp.term_eval {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (op : WrapOp) (v w : Val C Γ .uint) :
    (op.term v w).evalT σ = (v.evalT σ >>= fun x => w.evalT σ >>= fun y =>
      TRes.ofOpt (op.eval x y)) := by
  cases op <;> rfl

theorem WrapOp.encode (op : WrapOp) (n : Nat) (x y : Int) :
    BitVec.ofInt n (op.ideal x y) =
      op.word (BitVec.ofInt n x) (BitVec.ofInt n y) y.toNat := by
  cases op
  · exact BitVec.ofInt_add x y
  · exact ofInt_sub n x y
  · exact BitVec.ofInt_mul x y
  · exact ofInt_pow n x y.toNat

theorem WrapOp.value (op : WrapOp) (x y : PrimTy.uint.Denote) :
    ∃ r : PrimTy.uint.Denote, op.eval x y = some r ∧
      r.val = op.ideal x.val y.val % Semantics.uintBound := by
  apply uint_value_of_map
  cases op
  · exact uint_mod _
  · exact uint_mod _
  · exact uint_mod _
  · change ((if y.val < 0 then none else some (x.val ^ y.val.toNat % Semantics.uintBound)).bind
      PrimTy.uint.ofInt?).map Subtype.val = _
    rw [if_neg (not_lt.mpr (PrimTy.uint_nonneg y)), Option.bind_some]
    exact uint_mod _

/-- Actual wrapping primitive followed by the actual width-cut term. No operand-success premise. -/
theorem uint_wrapping_all_widths {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (op : WrapOp) (n : Nat) (hn : n ≤ 256) (v w : Val C Γ .uint) :
    ((cutUInt n (op.term v w)).evalT σ).map Subtype.val =
      (v.evalT σ >>= fun x => w.evalT σ >>= fun y =>
        .ok ((op.word (BitVec.ofInt n x.val) (BitVec.ofInt n y.val) y.val.toNat).toNat : Int)) := by
  rw [cutUInt_eval σ n hn]
  cases hx : v.evalT σ with
  | error e => simp only [WrapOp.term_eval, hx, bind, Except.bind]
  | ok x =>
    cases hy : w.evalT σ with
    | error e =>
      simp only [WrapOp.term_eval, hx, hy, bind, Except.bind]
    | ok y =>
      obtain ⟨r, hr, hv⟩ := op.value x y
      simp only [WrapOp.term_eval, hx, hy, ok_bind]
      rw [hr]
      simp only [TRes.ofOpt, ok_bind]
      rw [hv, cut_full_word _ n hn, op.encode]

/-- The signed wrapping lowering casts both inputs to words, then reads the cut signed. -/
theorem int_wrapping_all_widths {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (op : WrapOp) (hop : op ≠ .pow) (n : Nat) (hn0 : 0 < n) (hn : n ≤ 256) (v w : Val C Γ .int) :
    ((cutInt n (op.term (.unop .toUint rfl rfl v) (.unop .toUint rfl rfl w))).evalT σ).map Subtype.val =
      (v.evalT σ >>= fun x => w.evalT σ >>= fun y =>
        .ok ((BitVec.ofInt n (op.ideal x.val y.val)).toInt)) := by
  rw [cutInt_eval σ n hn0 hn]
  cases hx : v.evalT σ with
  | error e => simp only [WrapOp.term_eval, Val.evalT.eq_4, hx, bind, Except.bind]
  | ok x =>
    obtain ⟨a, ha, hea⟩ := toUint_word x
    cases hy : w.evalT σ with
    | error e =>
      simp only [WrapOp.term_eval, Val.evalT.eq_4, hx, hy, ha, TRes.ofOpt, bind, Except.bind]
    | ok y =>
      obtain ⟨b, hb, heb⟩ := toUint_word y
      obtain ⟨r, hr, hv⟩ := op.value a b
      simp only [WrapOp.term_eval, Val.evalT.eq_4, hx, hy, ha, hb, TRes.ofOpt, ok_bind]
      rw [hr]
      simp only [ok_bind]
      rw [hv, cut_full_word _ n hn]
      have hac : BitVec.ofInt n a.val = BitVec.ofInt n x.val := by
        have he : (BitVec.ofInt 256 a.val).setWidth n = (BitVec.ofInt 256 x.val).setWidth n :=
          congrArg (BitVec.setWidth n) hea
        simpa only [setWidth_full_word n hn] using he
      have hbc : BitVec.ofInt n b.val = BitVec.ofInt n y.val := by
        have he : (BitVec.ofInt 256 b.val).setWidth n = (BitVec.ofInt 256 y.val).setWidth n :=
          congrArg (BitVec.setWidth n) heb
        simpa only [setWidth_full_word n hn] using he
      cases op
      · simp only [WrapOp.ideal, BitVec.ofInt_add, hac, hbc]
      · simp only [WrapOp.ideal, ofInt_sub, hac, hbc]
      · simp only [WrapOp.ideal, BitVec.ofInt_mul, hac, hbc]
      · exact False.elim (hop rfl)

/-- The exponent is uint and is not truncated to the base width. -/
theorem int_powW_all_widths {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (n : Nat) (hn0 : 0 < n) (hn : n ≤ 256) (v : Val C Γ .int) (w : Val C Γ .uint) :
    ((cutInt n (WrapOp.pow.term (.unop .toUint rfl rfl v) w)).evalT σ).map Subtype.val =
      (v.evalT σ >>= fun x => w.evalT σ >>= fun y =>
        .ok (((BitVec.ofInt n x.val) ^ y.val.toNat).toInt)) := by
  rw [cutInt_eval σ n hn0 hn]
  cases hx : v.evalT σ with
  | error e => simp only [WrapOp.term_eval, Val.evalT.eq_4, hx, bind, Except.bind]
  | ok x =>
    obtain ⟨a, ha, hea⟩ := toUint_word x
    cases hy : w.evalT σ with
    | error e =>
      simp only [WrapOp.term_eval, Val.evalT.eq_4, hx, hy, ha, TRes.ofOpt, bind, Except.bind]
    | ok y =>
      obtain ⟨r, hr, hv⟩ := WrapOp.pow.value a y
      simp only [WrapOp.term_eval, Val.evalT.eq_4, hx, hy, ha, TRes.ofOpt, ok_bind]
      rw [hr]
      simp only [ok_bind]
      rw [hv, cut_full_word _ n hn, WrapOp.ideal, ofInt_pow]
      have hac : BitVec.ofInt n a.val = BitVec.ofInt n x.val := by
        have he : (BitVec.ofInt 256 a.val).setWidth n = (BitVec.ofInt 256 x.val).setWidth n :=
          congrArg (BitVec.setWidth n) hea
        simpa only [setWidth_full_word n hn] using he
      rw [hac]

theorem int_negW_all_widths {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (n : Nat) (hn0 : 0 < n) (hn : n ≤ 256) (v : Val C Γ .int) :
    ((cutInt n (WrapOp.sub.term (.simple (.lit 0 rfl)) (.unop .toUint rfl rfl v))).evalT σ).map
      Subtype.val = (v.evalT σ >>= fun x => .ok (-BitVec.ofInt n x.val).toInt) := by
  rw [cutInt_eval σ n hn0 hn]
  cases hx : v.evalT σ with
  | error e =>
    simp only [WrapOp.term_eval, Val.evalT.eq_4, Val.evalT.eq_1, Simple.evalT, hx, bind, Except.bind]
  | ok x =>
    obtain ⟨a, ha, hea⟩ := toUint_word x
    obtain ⟨r, hr, hv⟩ := WrapOp.sub.value (PrimTy.ofLit .uint 0 rfl) a
    simp only [WrapOp.term_eval, Val.evalT.eq_4, Val.evalT.eq_1, Simple.evalT, hx, ha,
      TRes.ofOpt, ok_bind]
    rw [hr]
    simp only [ok_bind]
    rw [hv, cut_full_word _ n hn]
    have hac : BitVec.ofInt n a.val = BitVec.ofInt n x.val := by
      have he : (BitVec.ofInt 256 a.val).setWidth n = (BitVec.ofInt 256 x.val).setWidth n :=
        congrArg (BitVec.setWidth n) hea
      simpa only [setWidth_full_word n hn] using he
    simp only [WrapOp.ideal, PrimTy.ofLit, zero_sub, BitVec.ofInt_neg, hac]

end Solidity.Bridge.Arith

#print axioms Solidity.Bridge.Arith.uint_wrapping_all_widths
#print axioms Solidity.Bridge.Arith.int_wrapping_all_widths

#print axioms Solidity.Bridge.Arith.int_powW_all_widths
#print axioms Solidity.Bridge.Arith.int_negW_all_widths
