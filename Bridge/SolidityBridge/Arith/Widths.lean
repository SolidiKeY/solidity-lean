import SolidityBridge.Arith.SignedWrapping
import SolidityBridge.Arith.WidthsSyntax
import Solidity.Syntax.Elab
import Solidity.Semantics.Run

set_option maxRecDepth 4096

namespace Solidity.Bridge.Arith.Widths

abbrev wordContext : NCtx := [(Var.ofName "x", .val .uint)]

/-- The exact local expression resolved by the core checker. -/
theorem check_word {C : Contract} :
    Solidity.check C wordContext .uint (.name "x") =
      .ok (Val.simple (Simple.local (.here : Idx [.val .uint] (.val .uint)))) := by
  simp only [wordContext, List.map_cons, List.map_nil, Solidity.check, checkVia, bind,
    Except.bind, synth, NCtx.lookupTy, if_true, NCtx.idx, Except.map, NCtx.find,
    dite_true, pure, Except.pure, TExpr.toVal?]

theorem synth_word {C : Contract} :
    Solidity.synth C wordContext (.name "x") =
      .ok (TExpr.val .uint (Val.simple (Simple.local (.here : Idx [.val .uint] (.val .uint))))) := by
  exact WidthsSyntax.synth_head .uint "x" []

/-- The exact modulo expression used by lowBits at a narrow width. -/
def lowVal {C : Contract} (n : Nat) (h : PrimTy.uint.inRange (2 ^ n : Nat) = true) :
    Val C [.val .uint] .uint :=
  .binop .mod rfl rfl (.simple (.local .here)) (.simple (.lit (2 ^ n : Nat) h))

theorem litAt_of_range {C : Contract} {Γ : NCtx} (p : PrimTy) (z : Int)
    (h : p.inRange z = true) : litAt C Γ p z = .ok (Simple.lit z h) := by
  unfold litAt
  split
  · rfl
  · rename_i hf
    rw [h] at hf
    cases hf


theorem synth_binary {C : Contract} {Γ : NCtx} (p : PrimTy) (e b : RawExpr)
    (v w : Val C Γ.ctx p) (op : BinOp) (ha : op.accepts p = true)
    (hc : e.constRat? = none) (hl : e.isLit = false)
    (hs : Solidity.synth C Γ e = .ok (.val p v))
    (hv : Solidity.check C Γ p e = .ok v) (hw : Solidity.check C Γ p b = .ok w) :
    Solidity.synth C Γ (.binop op e b) =
      .ok (.val (op.ret p) (.binop op ha rfl v w)) := by
  rw [synth.eq_6]
  simp only [RawExpr.constRat?, hc, bind, Option.bind, pure, Except.pure, Except.bind,
    hl, Bool.false_eq_true, if_false]
  rw [hs]
  simp only [TExpr.toVal?]
  split
  · rw [hv, hw]
  · rename_i hf
    rw [ha] at hf
    cases hf

theorem check_binary {C : Contract} {Γ : NCtx} (p : PrimTy) (e b : RawExpr)
    (v w : Val C Γ.ctx p) (op : BinOp) (ha : op.accepts p = true)
    (hc : e.constRat? = none) (hl : e.isLit = false)
    (hs : Solidity.synth C Γ e = .ok (.val p v))
    (hv : Solidity.check C Γ p e = .ok v) (hw : Solidity.check C Γ p b = .ok w) :
    Solidity.check C Γ (op.ret p) (.binop op e b) = .ok (.binop op ha rfl v w) := by
  rw [Solidity.check.eq_3]
  simp only [RawExpr.constRat?, hc, hl, Bool.false_and, Bool.false_eq_true, bind,
    Option.bind, Except.bind, pure, Except.pure, if_false]
  unfold checkVia
  rw [synth_binary p e b v w op ha hc hl hs hv hw]
  simp only [bind, Except.bind, TExpr.toVal?, dite_true, pure, Except.pure]

theorem synth_bin_literal {C : Contract} {Γ : NCtx} (p : PrimTy) (e : RawExpr)
    (v : Val C Γ.ctx p) (op : BinOp) (k : Nat)
    (ha : op.accepts p = true) (hk : p.inRange (k : Int) = true)
    (hc : e.constRat? = none) (hl : e.isLit = false)
    (hs : Solidity.synth C Γ e = .ok (.val p v))
    (hv : Solidity.check C Γ p e = .ok v) :
    Solidity.synth C Γ (.binop op e (.num k)) =
      .ok (.val (op.ret p) (.binop op ha rfl v (.simple (.lit k hk)))) := by
  rw [synth.eq_6]
  simp only [RawExpr.constRat?, hc, bind, Option.bind, pure, Except.pure, Except.bind,
    hl, Bool.false_eq_true, if_false]
  rw [hs]
  simp only [TExpr.toVal?]
  split
  · rw [hv, Solidity.check.eq_1, litAt_of_range p (k : Int) hk]
    rfl
  · rename_i hf
    rw [ha] at hf
    cases hf

theorem check_bin_literal {C : Contract} {Γ : NCtx} (p : PrimTy) (e : RawExpr)
    (v : Val C Γ.ctx p) (op : BinOp) (k : Nat)
    (ha : op.accepts p = true) (hk : p.inRange (k : Int) = true)
    (hc : e.constRat? = none) (hl : e.isLit = false)
    (hs : Solidity.synth C Γ e = .ok (.val p v))
    (hv : Solidity.check C Γ p e = .ok v) :
    Solidity.check C Γ (op.ret p) (.binop op e (.num k)) =
      .ok (.binop op ha rfl v (.simple (.lit k hk))) := by
  rw [Solidity.check.eq_3]
  simp only [RawExpr.constRat?, hc, hl, Bool.false_and, Bool.false_eq_true, bind,
    Option.bind, Except.bind, pure, Except.pure, if_false]
  unfold checkVia
  rw [synth_bin_literal p e v op k ha hk hc hl hs hv]
  simp only [bind, Except.bind, TExpr.toVal?, dite_true, pure, Except.pure]

theorem synth_unary {C : Contract} {Γ : NCtx} (p : PrimTy) (e : RawExpr)
    (v : Val C Γ.ctx p) (op : UnOp) (ha : op.accepts p = true)
    (hs : Solidity.synth C Γ e = .ok (.val p v)) :
    Solidity.synth C Γ (.unop op e) =
      .ok (.val (op.ret p) (.unop op ha rfl v)) := by
  exact WidthsSyntax.synth_unary p e v op ha hs

theorem check_unary {C : Contract} {Γ : NCtx} (p : PrimTy) (e : RawExpr)
    (v : Val C Γ.ctx p) (op : UnOp) (ha : op.accepts p = true)
    (hl : e.isLit = false) (hs : Solidity.synth C Γ e = .ok (.val p v)) :
    Solidity.check C Γ (op.ret p) (.unop op e) = .ok (.unop op ha rfl v) := by
  rw [Solidity.check.eq_4]
  · unfold checkVia
    rw [synth_unary p e v op ha hs]
    simp only [bind, Except.bind, TExpr.toVal?, dite_true, pure, Except.pure]
  · intro k h
    cases h
  · intro k h
    cases h
    cases hl
  · intro o a b h
    cases h

theorem check_mod_literal {C : Contract} (k : Nat)
    (h : PrimTy.uint.inRange (k : Int) = true) :
    Solidity.check C wordContext .uint (.binop .mod (.name "x") (.num k)) =
      .ok (Val.binop .mod rfl rfl (.simple (.local (.here : Idx [.val .uint] (.val .uint))))
        (.simple (.lit k h))) :=
  check_bin_literal (Γ := wordContext) .uint (.name "x") (.simple (.local .here)) .mod k rfl h rfl rfl
    synth_word check_word


theorem check_low {C : Contract} (n : Nat) (hn : n < 256)
    (h : PrimTy.uint.inRange (2 ^ n : Nat) = true) :
    Solidity.check C wordContext .uint (lowBits n (.name "x")) = .ok (lowVal n h) := by
  rw [lowBits, if_neg (not_le.mpr hn)]
  exact check_mod_literal (2 ^ n) h


theorem pow_uint_range (n : Nat) (hn : n < 256) :
    PrimTy.uint.inRange (2 ^ n : Nat) = true := by
  simp only [PrimTy.inRange, decide_eq_true_eq]
  exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr (Nat.pow_lt_pow_right (by decide) hn)⟩

/-- The actual core range conversion after reduction, uniform in all widths. -/
theorem truncate_check (x : Int) (n : Nat) (hn : n ≤ 256) :
    (PrimTy.uint.ofInt? (x % ((2 ^ n : Nat) : Int))).map Subtype.val =
      some ((BitVec.ofInt n x).toNat : Int) := by
  have hp : 0 < ((2 ^ n : Nat) : Int) := Int.natCast_pos.mpr (Nat.two_pow_pos n)
  have hb : ((2 ^ n : Nat) : Int) ≤ (2 : Int) ^ 256 := by
    have hpow : (2 : Nat) ^ n ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) hn
    exact_mod_cast hpow
  rw [BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hp)), uint_check, if_pos]
  exact ⟨Int.emod_nonneg _ (ne_of_gt hp), (Int.emod_lt_of_pos _ hp).trans_le hb⟩

theorem map_ofOpt {α β : Type} (r : Option α) (f : α → β) :
    (TRes.ofOpt r).map f = TRes.ofOpt (r.map f) := by
  cases r <;> rfl

theorem lowVal_eval {C : Contract} (σ : State C [.val .uint]) (n : Nat) (hn : n < 256)
    (h : PrimTy.uint.inRange (2 ^ n : Nat) = true) :
    ((lowVal n h).evalT σ).map Subtype.val =
      .ok ((BitVec.ofInt n (TEnv.get .here σ.env).val).toNat : Int) := by
  simp only [lowVal, Val.evalT, Simple.evalT, BinOp.shortT, bind, Except.bind]
  change (TRes.ofOpt ((if ((2 ^ n : Nat) : Int) = 0 then none
      else some ((TEnv.get .here σ.env).val.tmod (2 ^ n : Nat))).bind
      PrimTy.uint.ofInt?)).map Subtype.val = _
  have hp : ((2 ^ n : Nat) : Int) ≠ 0 := ne_of_gt (Int.natCast_pos.mpr (Nat.two_pow_pos n))
  rw [if_neg hp, Option.bind_some, Int.tmod_eq_emod_of_nonneg (PrimTy.uint_nonneg _), map_ofOpt,
    truncate_check _ n (Nat.le_of_lt hn)]
  rfl

/-- Core lowBits -> core type checker -> core expression evaluation, for every width. -/
theorem lowBits_correct {C : Contract} (σ : State C [.val .uint]) (n : Nat) (hn : n ≤ 256) :
    (Solidity.check C wordContext .uint (lowBits n (.name "x"))).map
      (fun v => (v.evalT σ).map Subtype.val) =
      .ok (.ok ((BitVec.ofInt n (TEnv.get .here σ.env).val).toNat : Int)) := by
  by_cases hw : n < 256
  · rw [check_low n hw (pow_uint_range n hw)]
    change Except.ok (((lowVal n (pow_uint_range n hw)).evalT σ).map Subtype.val) = _
    rw [lowVal_eval σ n hw]
  · have he : n = 256 := by omega
    subst n
    rw [lowBits, if_pos (by decide), check_word]
    simp only [Except.map, Val.evalT, Simple.evalT]
    rw [uint_decode]

/-- Casting to a smaller word commutes with the core's full-word reduction. -/
theorem cut_full_word (x : Int) (n : Nat) (hn : n ≤ 256) :
    BitVec.ofInt n (x % Semantics.uintBound) = BitVec.ofInt n x := by
  have hd : ((2 ^ n : Nat) : Int) ∣ Semantics.uintBound := by
    simpa only [Semantics.uintBound, Nat.cast_pow, Nat.cast_ofNat] using pow_dvd_pow (2 : Int) hn
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, Int.emod_emod_of_dvd x hd]

/-- The rotated remainder in the core's signedAt has the exact signed-word reading. -/
theorem rotated_signed (x : Int) (n : Nat) (hn : 0 < n) :
    (x + ((2 ^ (n - 1) : Nat) : Int)) % ((2 ^ n : Nat) : Int) -
      ((2 ^ (n - 1) : Nat) : Int) = (BitVec.ofInt n x).toInt := by
  have hM : ((2 ^ n : Nat) : Int) =
      ((2 ^ (n - 1) : Nat) : Int) + ((2 ^ (n - 1) : Nat) : Int) := by
    exact_mod_cast (Nat.two_pow_pred_add_two_pow_pred hn).symm
  have hp : 0 < ((2 ^ n : Nat) : Int) := Int.natCast_pos.mpr (Nat.two_pow_pos n)
  have h0 : 0 ≤ (x + ((2 ^ (n - 1) : Nat) : Int)) % ((2 ^ n : Nat) : Int) :=
    Int.emod_nonneg _ (ne_of_gt hp)
  have h1 : (x + ((2 ^ (n - 1) : Nat) : Int)) % ((2 ^ n : Nat) : Int) < ((2 ^ n : Nat) : Int) :=
    Int.emod_lt_of_pos _ hp
  have hc : ((2 ^ (n - 1) : Nat) : Int) = (2 : Int) ^ (n - 1) := by
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  have hl : -(2 : Int) ^ (n - 1) ≤
      (x + ((2 ^ (n - 1) : Nat) : Int)) % ((2 ^ n : Nat) : Int) - ((2 ^ (n - 1) : Nat) : Int) := by
    rw [← hc]
    omega
  have hu : (x + ((2 ^ (n - 1) : Nat) : Int)) % ((2 ^ n : Nat) : Int) -
      ((2 ^ (n - 1) : Nat) : Int) < (2 : Int) ^ (n - 1) := by
    rw [← hc]
    omega
  calc
    _ = (BitVec.ofInt n ((x + ((2 ^ (n - 1) : Nat) : Int)) % ((2 ^ n : Nat) : Int) -
        ((2 ^ (n - 1) : Nat) : Int))).toInt :=
      (BitVec.toInt_ofInt_eq_self hn hl hu).symm
    _ = (BitVec.ofInt n x).toInt := by
      rw [BitVec.toInt_ofInt, BitVec.toInt_ofInt, Int.emod_sub_bmod, Int.add_sub_cancel]

/-- The typed expression emitted by signedAt's actual modulo/cast template. -/
def signedVal {C : Contract} (n : Nat)
    (hh : PrimTy.uint.inRange (2 ^ (n - 1) : Nat) = true)
    (hm : PrimTy.uint.inRange (2 ^ n : Nat) = true) : Val C [.val .uint] .int :=
  .unop .toInt rfl rfl
    (.binop .subW rfl rfl
      (.binop .mod rfl rfl
        (.binop .addW rfl rfl (.simple (.local .here)) (.simple (.lit (2 ^ (n - 1) : Nat) hh)))
        (.simple (.lit (2 ^ n : Nat) hm)))
      (.simple (.lit (2 ^ (n - 1) : Nat) hh)))

theorem check_signed {C : Contract} (n : Nat) (hn : n < 256)
    (hh : PrimTy.uint.inRange (2 ^ (n - 1) : Nat) = true)
    (hm : PrimTy.uint.inRange (2 ^ n : Nat) = true) :
    Solidity.check C wordContext .int (signedAt n (.name "x")) = .ok (signedVal n hh hm) := by
  let e0 : RawExpr := .name "x"
  let e1 : RawExpr := .binop .addW e0 (.num (2 ^ (n - 1)))
  let e2 : RawExpr := .binop .mod e1 (.num (2 ^ n))
  let e3 : RawExpr := .binop .subW e2 (.num (2 ^ (n - 1)))
  let v0 : Val C wordContext.ctx .uint := .simple (.local .here)
  let v1 : Val C wordContext.ctx .uint := .binop .addW rfl rfl v0 (.simple (.lit (2 ^ (n - 1) : Nat) hh))
  let v2 : Val C wordContext.ctx .uint := .binop .mod rfl rfl v1 (.simple (.lit (2 ^ n : Nat) hm))
  let v3 : Val C wordContext.ctx .uint := .binop .subW rfl rfl v2 (.simple (.lit (2 ^ (n - 1) : Nat) hh))
  have hs1 : Solidity.synth C wordContext e1 = .ok (.val .uint v1) :=
    synth_bin_literal .uint e0 v0 .addW (2 ^ (n - 1)) rfl hh rfl rfl synth_word check_word
  have hv1 : Solidity.check C wordContext .uint e1 = .ok v1 :=
    check_bin_literal .uint e0 v0 .addW (2 ^ (n - 1)) rfl hh rfl rfl synth_word check_word
  have hs2 : Solidity.synth C wordContext e2 = .ok (.val .uint v2) :=
    synth_bin_literal .uint e1 v1 .mod (2 ^ n) rfl hm rfl rfl hs1 hv1
  have hv2 : Solidity.check C wordContext .uint e2 = .ok v2 :=
    check_bin_literal .uint e1 v1 .mod (2 ^ n) rfl hm rfl rfl hs1 hv1
  have hs3 : Solidity.synth C wordContext e3 = .ok (.val .uint v3) :=
    synth_bin_literal .uint e2 v2 .subW (2 ^ (n - 1)) rfl hh rfl rfl hs2 hv2
  rw [signedAt, if_neg (not_le.mpr hn)]
  exact check_unary .uint e3 v3 .toInt rfl rfl hs3

theorem uint_remainder (x k : PrimTy.uint.Denote) :
    (BinOp.mod.evalT rfl x k).map Subtype.val =
      if k.val = 0 then none else some (x.val % k.val) := by
  rw [uint_mod_exact]
  split
  · rfl
  · rw [← uint_mod_word, Int.tmod_eq_emod_of_nonneg (PrimTy.uint_nonneg x)]

theorem uint_value_of_map (r : Option PrimTy.uint.Denote) (z : Int)
    (h : r.map Subtype.val = some z) : ∃ v, r = some v ∧ v.val = z := by
  cases r with
  | none => cases h
  | some v => exact ⟨v, rfl, Option.some.inj h⟩

/-- Actual primitive operations in the signedAt template, before any observation. -/
def signedWord (n : Nat)
    (hh : PrimTy.uint.inRange (2 ^ (n - 1) : Nat) = true)
    (hm : PrimTy.uint.inRange (2 ^ n : Nat) = true) (x : PrimTy.uint.Denote) :
    Option PrimTy.int.Denote := do
  let a ← BinOp.addW.evalT rfl x ⟨(2 ^ (n - 1) : Nat), hh⟩
  let b ← BinOp.mod.evalT rfl a ⟨(2 ^ n : Nat), hm⟩
  let c ← BinOp.subW.evalT rfl b ⟨(2 ^ (n - 1) : Nat), hh⟩
  UnOp.toInt.evalT rfl c

theorem signedWord_correct (n : Nat) (hn0 : 0 < n) (hn : n < 256)
    (hh : PrimTy.uint.inRange (2 ^ (n - 1) : Nat) = true)
    (hm : PrimTy.uint.inRange (2 ^ n : Nat) = true) (x : PrimTy.uint.Denote) :
    (signedWord n hh hm x).map Subtype.val = some (BitVec.ofInt n x.val).toInt := by
  let H : PrimTy.uint.Denote := ⟨(2 ^ (n - 1) : Nat), hh⟩
  let M : PrimTy.uint.Denote := ⟨(2 ^ n : Nat), hm⟩
  have ha : (BinOp.addW.evalT rfl x H).map Subtype.val =
      some ((x.val + H.val) % Semantics.uintBound) := uint_mod _
  obtain ⟨a, haRun, haVal⟩ := uint_value_of_map _ _ ha
  have hp : M.val ≠ 0 := ne_of_gt (Int.natCast_pos.mpr (Nat.two_pow_pos n))
  have hb : (BinOp.mod.evalT rfl a M).map Subtype.val = some (a.val % M.val) := by
    rw [uint_remainder, if_neg hp]
  obtain ⟨b, hbRun, hbVal⟩ := uint_value_of_map _ _ hb
  have hc : (BinOp.subW.evalT rfl b H).map Subtype.val =
      some ((b.val - H.val) % Semantics.uintBound) := uint_mod _
  obtain ⟨c, hcRun, hcVal⟩ := uint_value_of_map _ _ hc
  have hd : M.val ∣ Semantics.uintBound := by
    simpa only [M, Semantics.uintBound, Nat.cast_pow, Nat.cast_ofNat] using
      pow_dvd_pow (2 : Int) (Nat.le_of_lt hn)
  have hbRot : b.val - H.val = (BitVec.ofInt n x.val).toInt := by
    rw [hbVal, haVal, Int.emod_emod_of_dvd _ hd]
    exact rotated_signed x.val n hn0
  have hpHalf : (2 : Int) ^ (n - 1) ≤ 2 ^ 255 := by
    have hpow : (2 : Nat) ^ (n - 1) ≤ 2 ^ 255 :=
      Nat.pow_le_pow_right (by decide) (show n - 1 ≤ 255 by omega)
    exact_mod_cast hpow
  have hlo : -(2 : Int) ^ 255 ≤ (BitVec.ofInt n x.val).toInt :=
    (neg_le_neg hpHalf).trans (BitVec.le_toInt _)
  have hhi : (BitVec.ofInt n x.val).toInt < (2 : Int) ^ 255 :=
    (BitVec.toInt_lt (x := BitVec.ofInt n x.val)).trans_le hpHalf
  unfold signedWord
  change ((BinOp.addW.evalT rfl x H).bind (fun a => (BinOp.mod.evalT rfl a M).bind
    (fun b => (BinOp.subW.evalT rfl b H).bind (fun c => UnOp.toInt.evalT rfl c)))).map Subtype.val = _
  rw [haRun, Option.bind_some, hbRun, Option.bind_some, hcRun, Option.bind_some,
    toInt_word, hcVal, cut_full_word _ 256 (Nat.le_refl _), hbRot,
    BitVec.toInt_ofInt_eq_self (by decide) hlo hhi]

theorem ofOpt_bind {α β : Type} (r : Option α) (f : α → Option β) :
    (TRes.ofOpt r >>= fun a => TRes.ofOpt (f a)) = TRes.ofOpt (r.bind f) := by
  cases r <;> rfl

theorem signedVal_eval {C : Contract} (σ : State C [.val .uint]) (n : Nat)
    (hn0 : 0 < n) (hn : n < 256)
    (hh : PrimTy.uint.inRange (2 ^ (n - 1) : Nat) = true)
    (hm : PrimTy.uint.inRange (2 ^ n : Nat) = true) :
    ((signedVal n hh hm).evalT σ).map Subtype.val =
      .ok (BitVec.ofInt n (TEnv.get .here σ.env).val).toInt := by
  simp only [signedVal, Val.evalT, Simple.evalT, BinOp.shortT, ok_bind]
  simp only [ofOpt_bind, Option.bind_assoc]
  change (TRes.ofOpt (signedWord n hh hm (TEnv.get .here σ.env))).map Subtype.val = _
  rw [map_ofOpt, signedWord_correct n hn0 hn hh hm]
  rfl

/-- The exact core signedAt source template, checked and evaluated at every narrow width. -/
theorem signedAt_correct {C : Contract} (σ : State C [.val .uint]) (n : Nat)
    (hn0 : 0 < n) (hn : n < 256) :
    (Solidity.check C wordContext .int (signedAt n (.name "x"))).map
      (fun v => (v.evalT σ).map Subtype.val) =
      .ok (.ok (BitVec.ofInt n (TEnv.get .here σ.env).val).toInt) := by
  have hnH : n - 1 < 256 := by omega
  rw [check_signed n hn (pow_uint_range (n - 1) hnH) (pow_uint_range n hn)]
  change Except.ok (((signedVal n _ _).evalT σ).map Subtype.val) = _
  rw [signedVal_eval σ n hn0 hn]

/-- The same core cut applied to any typed operand, with its execution preserved. -/
def lowFrom {C : Contract} {Γ : Ctx} (v : Val C Γ .uint) (n : Nat)
    (hm : PrimTy.uint.inRange (2 ^ n : Nat) = true) : Val C Γ .uint :=
  .binop .mod rfl rfl v (.simple (.lit (2 ^ n : Nat) hm))

def signedFrom {C : Contract} {Γ : Ctx} (v : Val C Γ .uint) (n : Nat)
    (hh : PrimTy.uint.inRange (2 ^ (n - 1) : Nat) = true)
    (hm : PrimTy.uint.inRange (2 ^ n : Nat) = true) : Val C Γ .int :=
  .unop .toInt rfl rfl
    (.binop .subW rfl rfl
      (.binop .mod rfl rfl
        (.binop .addW rfl rfl v (.simple (.lit (2 ^ (n - 1) : Nat) hh)))
        (.simple (.lit (2 ^ n : Nat) hm)))
      (.simple (.lit (2 ^ (n - 1) : Nat) hh)))

theorem lowFrom_eval {C : Contract} {Γ : Ctx} (σ : State C Γ) (v : Val C Γ .uint)
    (n : Nat) (hn : n < 256) (hm : PrimTy.uint.inRange (2 ^ n : Nat) = true) :
    ((lowFrom v n hm).evalT σ).map Subtype.val =
      (v.evalT σ >>= fun x => .ok ((BitVec.ofInt n x.val).toNat : Int)) := by
  cases h : v.evalT σ with
  | error e =>
    simp only [lowFrom, Val.evalT.eq_3, h, bind, Except.bind, Except.map]
  | ok x =>
    simp only [lowFrom, Val.evalT.eq_3, Val.evalT.eq_1, h, ok_bind,
      BinOp.shortT, Simple.evalT]
    change (TRes.ofOpt ((if ((2 ^ n : Nat) : Int) = 0 then none
        else some (x.val.tmod (2 ^ n : Nat))).bind PrimTy.uint.ofInt?)).map Subtype.val = _
    have hp : ((2 ^ n : Nat) : Int) ≠ 0 := ne_of_gt (Int.natCast_pos.mpr (Nat.two_pow_pos n))
    rw [if_neg hp, Option.bind_some, Int.tmod_eq_emod_of_nonneg (PrimTy.uint_nonneg x),
      map_ofOpt, truncate_check _ n (Nat.le_of_lt hn)]
    rfl

theorem signedFrom_eval {C : Contract} {Γ : Ctx} (σ : State C Γ) (v : Val C Γ .uint)
    (n : Nat) (hn0 : 0 < n) (hn : n < 256)
    (hh : PrimTy.uint.inRange (2 ^ (n - 1) : Nat) = true)
    (hm : PrimTy.uint.inRange (2 ^ n : Nat) = true) :
    ((signedFrom v n hh hm).evalT σ).map Subtype.val =
      (v.evalT σ >>= fun x => .ok (BitVec.ofInt n x.val).toInt) := by
  cases h : v.evalT σ with
  | error e =>
    simp only [signedFrom, Val.evalT.eq_3, Val.evalT.eq_4, Val.evalT.eq_1, h,
      bind, Except.bind, Except.map]
  | ok x =>
    simp only [signedFrom, Val.evalT.eq_3, Val.evalT.eq_4, Val.evalT.eq_1, h,
      Simple.evalT, BinOp.shortT, ok_bind]
    simp only [ofOpt_bind, Option.bind_assoc]
    change (TRes.ofOpt (signedWord n hh hm x)).map Subtype.val = _
    rw [map_ofOpt, signedWord_correct n hn0 hn hh hm x]
    rfl

theorem check_low_from {C : Contract} {Γ : NCtx} (e : RawExpr) (v : Val C Γ.ctx .uint)
    (n : Nat) (hn : n < 256) (hm : PrimTy.uint.inRange (2 ^ n : Nat) = true)
    (hc : e.constRat? = none) (hl : e.isLit = false)
    (hs : Solidity.synth C Γ e = .ok (.val .uint v))
    (hv : Solidity.check C Γ .uint e = .ok v) :
    Solidity.check C Γ .uint (lowBits n e) = .ok (lowFrom v n hm) := by
  rw [lowBits, if_neg (not_le.mpr hn)]
  exact check_bin_literal .uint e v .mod (2 ^ n) rfl hm hc hl hs hv

theorem check_signed_from {C : Contract} {Γ : NCtx} (e : RawExpr) (v : Val C Γ.ctx .uint)
    (n : Nat) (hn : n < 256)
    (hh : PrimTy.uint.inRange (2 ^ (n - 1) : Nat) = true)
    (hm : PrimTy.uint.inRange (2 ^ n : Nat) = true)
    (hc : e.constRat? = none) (hl : e.isLit = false)
    (hs : Solidity.synth C Γ e = .ok (.val .uint v))
    (hv : Solidity.check C Γ .uint e = .ok v) :
    Solidity.check C Γ .int (signedAt n e) = .ok (signedFrom v n hh hm) := by
  let e1 : RawExpr := .binop .addW e (.num (2 ^ (n - 1)))
  let e2 : RawExpr := .binop .mod e1 (.num (2 ^ n))
  let e3 : RawExpr := .binop .subW e2 (.num (2 ^ (n - 1)))
  let v1 : Val C Γ.ctx .uint := .binop .addW rfl rfl v (.simple (.lit (2 ^ (n - 1) : Nat) hh))
  let v2 : Val C Γ.ctx .uint := .binop .mod rfl rfl v1 (.simple (.lit (2 ^ n : Nat) hm))
  let v3 : Val C Γ.ctx .uint := .binop .subW rfl rfl v2 (.simple (.lit (2 ^ (n - 1) : Nat) hh))
  have hs1 : Solidity.synth C Γ e1 = .ok (.val .uint v1) :=
    synth_bin_literal .uint e v .addW (2 ^ (n - 1)) rfl hh hc hl hs hv
  have hv1 : Solidity.check C Γ .uint e1 = .ok v1 :=
    check_bin_literal .uint e v .addW (2 ^ (n - 1)) rfl hh hc hl hs hv
  have hc1 : e1.constRat? = none := by simp only [e1, RawExpr.constRat?, hc, bind, Option.bind]
  have hs2 : Solidity.synth C Γ e2 = .ok (.val .uint v2) :=
    synth_bin_literal .uint e1 v1 .mod (2 ^ n) rfl hm hc1 rfl hs1 hv1
  have hv2 : Solidity.check C Γ .uint e2 = .ok v2 :=
    check_bin_literal .uint e1 v1 .mod (2 ^ n) rfl hm hc1 rfl hs1 hv1
  have hc2 : e2.constRat? = none := by simp only [e2, RawExpr.constRat?, hc1, bind, Option.bind]
  have hs3 : Solidity.synth C Γ e3 = .ok (.val .uint v3) :=
    synth_bin_literal .uint e2 v2 .subW (2 ^ (n - 1)) rfl hh hc2 rfl hs2 hv2
  rw [signedAt, if_neg (not_le.mpr hn)]
  exact check_unary .uint e3 v3 .toInt rfl rfl hs3

/-- All widths, all typed operands, and every panic/revert/exhaustion from that operand. -/
theorem lowBits_from_correct {C : Contract} {Γ : NCtx} (σ : State C Γ.ctx)
    (e : RawExpr) (v : Val C Γ.ctx .uint) (n : Nat) (hn : n ≤ 256)
    (hc : e.constRat? = none) (hl : e.isLit = false)
    (hs : Solidity.synth C Γ e = .ok (.val .uint v))
    (hv : Solidity.check C Γ .uint e = .ok v) :
    (Solidity.check C Γ .uint (lowBits n e)).map (fun w => (w.evalT σ).map Subtype.val) =
      .ok (v.evalT σ >>= fun x => .ok ((BitVec.ofInt n x.val).toNat : Int)) := by
  by_cases hw : n < 256
  · rw [check_low_from e v n hw (pow_uint_range n hw) hc hl hs hv]
    change Except.ok (((lowFrom v n _).evalT σ).map Subtype.val) = _
    rw [lowFrom_eval σ v n hw]
  · have he : n = 256 := by omega
    subst n
    rw [lowBits, if_pos (by decide), hv]
    cases h : v.evalT σ with
    | error e => simp only [Except.map, h, bind, Except.bind]
    | ok x =>
      simp only [Except.map, h, bind, Except.bind]
      rw [uint_decode]

theorem signedAt_from_correct {C : Contract} {Γ : NCtx} (σ : State C Γ.ctx)
    (e : RawExpr) (v : Val C Γ.ctx .uint) (n : Nat) (hn0 : 0 < n) (hn : n ≤ 256)
    (hc : e.constRat? = none) (hl : e.isLit = false)
    (hs : Solidity.synth C Γ e = .ok (.val .uint v))
    (hv : Solidity.check C Γ .uint e = .ok v) :
    (Solidity.check C Γ .int (signedAt n e)).map (fun w => (w.evalT σ).map Subtype.val) =
      .ok (v.evalT σ >>= fun x => .ok (BitVec.ofInt n x.val).toInt) := by
  by_cases hw : n < 256
  · have hh : n - 1 < 256 := by omega
    rw [check_signed_from e v n hw (pow_uint_range (n - 1) hh) (pow_uint_range n hw) hc hl hs hv]
    change Except.ok (((signedFrom v n _ _).evalT σ).map Subtype.val) = _
    rw [signedFrom_eval σ v n hn0 hw]
  · have he : n = 256 := by omega
    subst n
    rw [signedAt, if_pos (by decide)]
    have hu : Solidity.check C Γ .int (.unop .toInt e) =
        .ok (Val.unop .toInt rfl rfl v) := check_unary .uint e v .toInt rfl hl hs
    rw [hu]
    change Except.ok (((Val.unop .toInt rfl rfl v).evalT σ).map Subtype.val) = _
    cases h : v.evalT σ with
    | error e =>
      simp only [Except.map, Val.evalT.eq_4, h, bind, Except.bind]
    | ok x =>
      simp only [Val.evalT.eq_4, h, ok_bind]
      rw [map_ofOpt, toInt_word]
      rfl

abbrev headContext (p : PrimTy) (name : String) (Γ : NCtx) : NCtx :=
  (Var.ofName name, .val p) :: Γ

theorem synth_head {C : Contract} (p : PrimTy) (name : String) (Γ : NCtx) :
    Solidity.synth C (headContext p name Γ) (.name name) =
      .ok (.val p (.simple (.local (.here : Idx (.val p :: Γ.ctx) (.val p))))) := by
  exact WidthsSyntax.synth_head p name Γ

theorem check_head {C : Contract} (p : PrimTy) (name : String) (Γ : NCtx) :
    Solidity.check C (headContext p name Γ) p (.name name) =
      .ok (.simple (.local (.here : Idx (.val p :: Γ.ctx) (.val p)))) := by
  rw [Solidity.check.eq_4]
  · unfold checkVia
    rw [synth_head]
    simp only [bind, Except.bind, TExpr.toVal?, dite_true, pure, Except.pure]
  · intro k h
    cases h
  · intro k h
    cases h
  · intro op a b h
    cases h

abbrev intContext : NCtx := headContext .int "x" []

/-- Signed-to-unsigned casts at every target width, through the actual cast template. -/
theorem signed_to_uint_width {C : Contract} (σ : State C intContext.ctx)
    (n : Nat) (hn : n ≤ 256) :
    (Solidity.check C intContext .uint (lowBits n (.unop .toUint (.name "x")))).map
      (fun v => (v.evalT σ).map Subtype.val) =
      .ok (.ok ((BitVec.ofInt n (TEnv.get .here σ.env).val).toNat : Int)) := by
  let v : Val C intContext.ctx .uint := .unop .toUint rfl rfl (.simple (.local .here))
  have hs : Solidity.synth C intContext (.unop .toUint (.name "x")) = .ok (.val .uint v) :=
    synth_unary (Γ := intContext) .int (.name "x") (.simple (.local .here)) .toUint rfl (synth_head .int "x" [])
  have hv : Solidity.check C intContext .uint (.unop .toUint (.name "x")) = .ok v :=
    check_unary (Γ := intContext) .int (.name "x") (.simple (.local .here)) .toUint rfl rfl (synth_head .int "x" [])
  rw [lowBits_from_correct σ (.unop .toUint (.name "x")) v n hn rfl rfl hs hv]
  simp only [v, Val.evalT.eq_4, Val.evalT.eq_1, Simple.evalT, ok_bind]
  have hcast : (UnOp.toUint.evalT rfl (TEnv.get .here σ.env)).map Subtype.val =
      some ((TEnv.get .here σ.env).val % Semantics.uintBound) := uint_mod _
  obtain ⟨a, ha, hav⟩ := uint_value_of_map _ _ hcast
  rw [ha]
  simp only [TRes.ofOpt, ok_bind]
  rw [hav, cut_full_word _ n hn]

/-- Signed-to-signed casts at every target width, via its full word and signedAt. -/
theorem signed_to_int_width {C : Contract} (σ : State C intContext.ctx)
    (n : Nat) (hn0 : 0 < n) (hn : n ≤ 256) :
    (Solidity.check C intContext .int (signedAt n (.unop .toUint (.name "x")))).map
      (fun v => (v.evalT σ).map Subtype.val) =
      .ok (.ok (BitVec.ofInt n (TEnv.get .here σ.env).val).toInt) := by
  let v : Val C intContext.ctx .uint := .unop .toUint rfl rfl (.simple (.local .here))
  have hs : Solidity.synth C intContext (.unop .toUint (.name "x")) = .ok (.val .uint v) :=
    synth_unary (Γ := intContext) .int (.name "x") (.simple (.local .here)) .toUint rfl (synth_head .int "x" [])
  have hv : Solidity.check C intContext .uint (.unop .toUint (.name "x")) = .ok v :=
    check_unary (Γ := intContext) .int (.name "x") (.simple (.local .here)) .toUint rfl rfl (synth_head .int "x" [])
  rw [signedAt_from_correct σ (.unop .toUint (.name "x")) v n hn0 hn rfl rfl hs hv]
  simp only [v, Val.evalT.eq_4, Val.evalT.eq_1, Simple.evalT, ok_bind]
  have hcast : (UnOp.toUint.evalT rfl (TEnv.get .here σ.env)).map Subtype.val =
      some ((TEnv.get .here σ.env).val % Semantics.uintBound) := uint_mod _
  obtain ⟨a, ha, hav⟩ := uint_value_of_map _ _ hcast
  rw [ha]
  simp only [TRes.ofOpt, ok_bind]
  rw [hav, cut_full_word _ n hn]

/-- Unsigned-to-signed conversion at every target width, through the actual source template. -/
theorem unsigned_to_int_width {C : Contract} (σ : State C wordContext.ctx)
    (n : Nat) (hn0 : 0 < n) (hn : n ≤ 256) :
    (Solidity.check C wordContext .int (signedAt n (.name "x"))).map
      (fun v => (v.evalT σ).map Subtype.val) =
      .ok (.ok (BitVec.ofInt n (TEnv.get .here σ.env).val).toInt) := by
  exact signedAt_from_correct σ (.name "x") (.simple (.local .here)) n hn0 hn
    rfl rfl synth_word check_word

/-- Same-sign widening skips the cast template, exactly as zero extension does. -/
theorem unsigned_widen {m n : Nat} (h : m ≤ n) (x : BitVec m) :
    ((BitVec.ofInt n (x.toNat : Int)).toNat : Int) = (x.toNat : Int) := by
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
  exact x.isLt.trans_le (Nat.pow_le_pow_right (by decide) h)

/-- Same-sign signed widening skips the template and preserves the signed value. -/
theorem signed_widen {m n : Nat} (h : m ≤ n) (x : BitVec m) :
    (BitVec.ofInt n x.toInt).toInt = x.toInt :=
  BitVec.toInt_signExtend_of_le h

end Solidity.Bridge.Arith.Widths

#print axioms Solidity.Bridge.Arith.Widths.check_low
#print axioms Solidity.Bridge.Arith.Widths.truncate_check
#print axioms Solidity.Bridge.Arith.Widths.lowBits_correct

#print axioms Solidity.Bridge.Arith.Widths.cut_full_word
#print axioms Solidity.Bridge.Arith.Widths.rotated_signed

#print axioms Solidity.Bridge.Arith.Widths.check_signed

#print axioms Solidity.Bridge.Arith.Widths.signedWord_correct
#print axioms Solidity.Bridge.Arith.Widths.signedAt_correct

#print axioms Solidity.Bridge.Arith.Widths.lowFrom_eval
#print axioms Solidity.Bridge.Arith.Widths.signedFrom_eval
#print axioms Solidity.Bridge.Arith.Widths.lowBits_from_correct
#print axioms Solidity.Bridge.Arith.Widths.signedAt_from_correct

#print axioms Solidity.Bridge.Arith.Widths.signed_to_uint_width
#print axioms Solidity.Bridge.Arith.Widths.signed_to_int_width

#print axioms Solidity.Bridge.Arith.Widths.unsigned_to_int_width
#print axioms Solidity.Bridge.Arith.Widths.unsigned_widen
#print axioms Solidity.Bridge.Arith.Widths.signed_widen

/-- info: 'Solidity.Bridge.Arith.Widths.synth_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Bridge.Arith.Widths.synth_word
/-- info: 'Solidity.Bridge.Arith.Widths.synth_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Bridge.Arith.Widths.synth_head
/-- info: 'Solidity.Bridge.Arith.Widths.synth_unary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Bridge.Arith.Widths.synth_unary
