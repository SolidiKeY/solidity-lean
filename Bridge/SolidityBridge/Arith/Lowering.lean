import SolidityBridge.Arith.SignedDivision

namespace Solidity.Bridge.Arith

/-- The unchanged core capture continuation, including real checking and fresh-name errors. -/
def castTail (C : Contract) (p : PrimTy) (n : Nat) (r : RawExpr) :
    ElabM (SProg C × RawExpr) := do
  let Γn ← nctx
  let v ← checkIn C Γn p r
  let x ← captureAs C "se" (.val p n)
  pure ([.of Γn (.declLocal p x (some v))], .name (toString x))

def castTemplate (p q : PrimTy) (n m : Nat) (e : RawExpr) : RawExpr :=
  if q == p && m ≤ n then e
  else if p == .int then signedAt n (if q == .int then .unop .toUint e else e)
  else lowBits n (if q == .int then .unop .toUint e else e)

/-- The pure preprocessing stage of the actual cast capture. -/
def castPlan (C : Contract) (Γ : ECtx) (f : String) (p : PrimTy) (n : Nat)
    (e : RawExpr) : Except String RawExpr :=
  match intTyOf C Γ e, e.litVal? with
  | _, some _ => do fitCheck C Γ p n e; pure e
  | some (q, m), none => pure (castTemplate p q n m e)
  | none, none =>
    if 256 ≤ n then pure e else if p == .int then
      throw s!"{f}({e.toStr}): a cast of arithmetic on literals alone to a narrow int; write the literal"
    else pure (.binop .mod e (.num (2 ^ n)))

theorem castPlan_typed (C : Contract) (Γ : ECtx) (f : String) (e : RawExpr)
    (p q : PrimTy) (n m : Nat) (ht : intTyOf C Γ e = some (q, m))
    (hl : e.litVal? = none) :
    castPlan C Γ f p n e = .ok (castTemplate p q n m e) := by
  rw [castPlan, ht, hl]
  rfl

theorem ctx_run (scope : ElabScope) (st : ECtx × Nat) (memo : CallMemo) :
    ctx scope st memo = .ok ((st.1, st), memo) := rfl

theorem castCapture_factor (C : Contract) (f : String) (e : RawExpr) (p : PrimTy) (n : Nat)
    (hf : castTy? f = some (p, n)) :
    castCapture C f e = (do
      let Γ ← ctx
      let r ← ElabM.lift (castPlan C Γ f p n e)
      castTail C p n r) := by
  funext scope st memo
  delta castCapture
  rewrite [hf]
  simp only [bind, ReaderT.bind, StateT.bind, ctx_run, Except.bind]
  cases ht : intTyOf C st.1 e with
  | none =>
    cases hl : e.litVal?
    all_goals simp only [castPlan, ht, hl]
    all_goals (try split_ifs) <;> cases hfit : fitCheck C st.1 p n e <;> rfl
  | some t =>
    rcases t with ⟨q, m⟩
    cases hl : e.litVal?
    all_goals simp only [castPlan, castTemplate, ht, hl]
    all_goals (try split_ifs) <;> cases hfit : fitCheck C st.1 p n e <;> rfl

/-- Every source width is carried by an ordinary local. -/
theorem intTyOf_head (C : Contract) (Γ : ECtx) (x : String) (p : PrimTy) (n : Nat) :
    intTyOf C ((x, .val p n) :: Γ) (.name x) = some (p, n) := by
  change (match Semantics.lookupBy x ((x, .val p n) :: Γ) with
    | some (.val p n) => some (p, n)
    | some _ => some (.uint, 256)
    | none => match C.rootType x with
      | some (.prim p) => some (p, (Semantics.lookupBy x C.widths).getD 256)
      | _ => some (.uint, 256)) = _
  rewrite [Semantics.lookupBy, if_pos rfl]
  rfl

/-- Actual unsigned wrapping rewrite, including full width and ordinary nonliteral operands. -/
theorem narrowWrap_uint (C : Contract) (unc : Bool) (Γ : ECtx) (op : WrapOp)
    (a b : RawExpr) (n : Nat) (ha : a.litVal? = none) (hb : b.litVal? = none)
    (ht : intTyOf C Γ (.binop op.bin a b) = some (.uint, n)) :
    narrowWrapNode C unc Γ (.binop op.bin a b) =
      .ok (lowBits n (.binop op.bin a b)) := by
  rw [narrowWrapNode, ht]
  have hp : (PrimTy.uint == PrimTy.int) = false := rfl
  cases op <;>
    simp only [hp, WrapOp.bin, lowBits, ha, hb, Bool.and_false, Bool.false_and, Bool.false_eq_true,
      if_false, if_true, pure, Except.pure, bind, Except.bind, List.forIn_cons, List.forIn_nil]
  all_goals split <;> rfl

/-- Pointwise typed cast equation, preserving both checking and capture errors. -/
theorem castCapture_typed (C : Contract) (scope : ElabScope) (st : ECtx × Nat)
    (memo : CallMemo)
    (f : String) (e : RawExpr) (p q : PrimTy) (n m : Nat)
    (hf : castTy? f = some (p, n)) (ht : intTyOf C st.1 e = some (q, m))
    (hl : e.litVal? = none) :
    castCapture C f e scope st memo =
      castTail C p n (castTemplate p q n m e) scope st memo := by
  rw [castCapture_factor C f e p n hf]
  simp only [bind, ReaderT.bind, StateT.bind, ctx_run, Except.bind]
  rw [castPlan_typed C st.1 f e p q n m ht hl]
  rfl

theorem narrowWrap_int (C : Contract) (unc : Bool) (Γ : ECtx) (op : WrapOp)
    (hop : op ≠ .pow) (a b : RawExpr) (n : Nat)
    (ha : a.litVal? = none) (hb : b.litVal? = none)
    (ht : intTyOf C Γ (.binop op.bin a b) = some (.int, n)) :
    narrowWrapNode C unc Γ (.binop op.bin a b) =
      .ok (.call (tyName .int n) [.binop op.bin (.call "uint" [a]) (.call "uint" [b])]) := by
  rw [narrowWrapNode, ht]
  cases op <;> cases unc <;>
    simp only [WrapOp.bin, ha, hb, beq_self_eq_true, Bool.true_and, Bool.false_and, if_true, pure,
      Except.pure, bind, Except.bind, List.forIn_cons, List.forIn_nil]
  all_goals first | contradiction | rfl

theorem narrowWrap_int_pow (C : Contract) (unc : Bool) (Γ : ECtx)
    (a b : RawExpr) (n : Nat) (ha : a.litVal? = none)
    (ht : intTyOf C Γ (.binop .powW a b) = some (.int, n)) :
    narrowWrapNode C unc Γ (.binop .powW a b) =
      .ok (.call (tyName .int n) [.binop .powW (.call "uint" [a]) b]) := by
  rw [narrowWrapNode, ht]
  cases unc <;> simp only [ha, beq_self_eq_true, Bool.true_and, Bool.false_and, if_true, pure, Except.pure, bind,
    Except.bind]
  all_goals rfl

theorem narrowWrap_uint_bnot (C : Contract) (unc : Bool) (Γ : ECtx)
    (a : RawExpr) (n : Nat) (hn : n < 256)
    (ht : intTyOf C Γ (.unop .bnot a) = some (.uint, n)) :
    narrowWrapNode C unc Γ (.unop .bnot a) =
      .ok (.binop .subW (.num (2 ^ n - 1)) a) := by
  rw [narrowWrapNode, ht]
  have hp : (PrimTy.uint == PrimTy.int) = false := rfl
  simp only [hp, Bool.and_false, Bool.false_eq_true, if_false,
    if_neg (not_le.mpr hn), pure, Except.pure, bind, Except.bind]

theorem narrowWrap_uint_shl (C : Contract) (unc : Bool) (Γ : ECtx)
    (a b : RawExpr) (n : Nat)
    (ht : intTyOf C Γ (.binop .shl a b) = some (.uint, n)) :
    narrowWrapNode C unc Γ (.binop .shl a b) = .ok (lowBits n (.binop .shl a b)) := by
  rw [narrowWrapNode, ht]
  have hp : (PrimTy.uint == PrimTy.int) = false := rfl
  simp only [hp, lowBits, Bool.and_false, Bool.false_and, Bool.false_eq_true,
    if_false, if_true, pure, Except.pure, bind, Except.bind]
  split <;> rfl

/-- The actual unchecked signed-division source strategies (with effectful reads refused upstream). -/
theorem narrowWrap_int_div (C : Contract) (Γ : ECtx) (a b : RawExpr) (n : Nat)
    (hb : b.litVal? = none) (hae : a.hasIncDec = false) (hbe : b.hasIncDec = false)
    (ht : intTyOf C Γ (.binop .div a b) = some (.int, n)) :
    narrowWrapNode C true Γ (.binop .div a b) = .ok
      (if n < 256 then .call (tyName .int n) [.binop .div (.call "int" [a]) (.call "int" [b])]
       else
        let isM1 : RawExpr := .binop .eqB b (.unop .neg (.num 1))
        .call "int" [.binop .mulW
          (.call "uint" [.binop .div a (.ternary isM1 (.unop .neg b) b)])
          (.ternary isM1 (.num (2 ^ 256 - 1)) (.num 1))]) := by
  rw [narrowWrapNode, ht]
  simp only [hb, hae, hbe, beq_self_eq_true, Bool.true_and, Bool.false_or,
    Bool.false_eq_true, if_false, if_true, pure, Except.pure, bind, Except.bind]
  split <;> rfl

theorem nctx_run (scope : ElabScope) (st : ECtx × Nat) (memo : CallMemo) :
    nctx scope st memo = .ok ((st.1.toNCtx, st), memo) := rfl

/-- Exact selection of default require, explicit assert, self-call panic-data, or ignoring guard. -/
theorem narrowCheck_guard (C : Contract) (scope : ElabScope) (st : ECtx × Nat)
    (memo : CallMemo)
    (p : PrimTy) (n : Nat) (hn : n < 256) (e : RawExpr)
    (v : Val C st.1.toNCtx.ctx .bool)
    (hc : Solidity.check C st.1.toNCtx .bool (inTyCond p n e) = .ok v) :
    narrowCheck C p n e scope st memo = .ok
      (([.of st.1.toNCtx (match scope.overflow with
        | some o => o.guardStmt v scope.selfFrame
        | none => if scope.selfFrame then panicStmt 0x11 v else .require v)], st), memo) := by
  delta narrowCheck
  rw [if_neg (not_le.mpr hn)]
  simp only [bind, ReaderT.bind, StateT.bind, nctx_run, Except.bind, pure, ReaderT.pure, StateT.pure, Except.pure]
  simp only [checkIn, ElabM.lift, StateT.lift, hc]
  rfl

theorem narrowCheck_full (C : Contract) (scope : ElabScope) (st : ECtx × Nat)
    (memo : CallMemo)
    (p : PrimTy) (n : Nat) (hn : 256 ≤ n) (e : RawExpr) :
    narrowCheck C p n e scope st memo = .ok (([], st), memo) := by
  delta narrowCheck
  rw [if_pos hn]
  rfl

/-- The actual optimization of a negative literal added to a signed word. -/
theorem narrowWrap_int_add_negative (C : Contract) (unc : Bool) (Γ : ECtx)
    (a b : RawExpr) (n : Nat) (v : Int) (ha : a.litVal? = none) (hb : b.litVal? = some v)
    (hv : v < 0) (hf : (intRange .int n).1 ≤ v ∧ v ≤ (intRange .int n).2)
    (ht : intTyOf C Γ (.binop .addW a b) = some (.int, n)) :
    narrowWrapNode C unc Γ (.binop .addW a b) =
      .ok (.call (tyName .int n) [.binop .subW (.call "uint" [a]) (.num v.natAbs)]) := by
  rw [narrowWrapNode, ht]
  have hfit : (decide ((intRange .int n).1 ≤ v) && decide (v ≤ (intRange .int n).2)) = true := by
    simp only [hf.1, hf.2, decide_true, Bool.true_and]
  cases unc <;> simp only [ha, hb, hfit, if_pos hv, beq_self_eq_true,
    Bool.true_and, Bool.false_and, Bool.false_eq_true, if_true, if_false,
    pure, Except.pure, bind, Except.bind, List.forIn_cons, List.forIn_nil]
  all_goals rfl

theorem narrowWrap_int_sub_negative (C : Contract) (unc : Bool) (Γ : ECtx)
    (a b : RawExpr) (n : Nat) (v : Int) (ha : a.litVal? = none) (hb : b.litVal? = some v)
    (hv : v < 0) (hf : (intRange .int n).1 ≤ v ∧ v ≤ (intRange .int n).2)
    (ht : intTyOf C Γ (.binop .subW a b) = some (.int, n)) :
    narrowWrapNode C unc Γ (.binop .subW a b) =
      .ok (.call (tyName .int n) [.binop .addW (.call "uint" [a]) (.num v.natAbs)]) := by
  rw [narrowWrapNode, ht]
  have hfit : (decide ((intRange .int n).1 ≤ v) && decide (v ≤ (intRange .int n).2)) = true := by
    simp only [hf.1, hf.2, decide_true, Bool.true_and]
  cases unc <;> simp only [ha, hb, hfit, if_pos hv, beq_self_eq_true,
    Bool.true_and, Bool.false_and, Bool.false_eq_true, if_true, if_false,
    pure, Except.pure, bind, Except.bind, List.forIn_cons, List.forIn_nil]
  all_goals rfl

theorem narrowWrap_int_pow_literal (C : Contract) (unc : Bool) (Γ : ECtx)
    (a b : RawExpr) (n : Nat) (v : Int) (ha : a.litVal? = some v)
    (hf : (intRange .int n).1 ≤ v ∧ v ≤ (intRange .int n).2)
    (ht : intTyOf C Γ (.binop .powW a b) = some (.int, n)) :
    narrowWrapNode C unc Γ (.binop .powW a b) =
      .ok (.call (tyName .int n) [.binop .powW (.num (v % ((2 ^ 256 : Nat) : Int)).toNat) b]) := by
  rw [narrowWrapNode, ht]
  have hfit : (decide ((intRange .int n).1 ≤ v) && decide (v ≤ (intRange .int n).2)) = true := by
    simp only [hf.1, hf.2, decide_true, Bool.true_and]
  cases unc <;> simp only [ha, hfit, beq_self_eq_true, Bool.true_and, Bool.false_and,
    Bool.false_eq_true, if_true, if_false, pure, Except.pure, bind, Except.bind]

/-- The optimized literal branches retain exactly the same mathematical operation. -/
theorem negative_literal_add (x v : Int) (hv : v < 0) : x + v = x - (v.natAbs : Int) := by
  have he : (v.natAbs : Int) = -v := Int.ofNat_natAbs_of_nonpos (by omega)
  omega

theorem negative_literal_sub (x v : Int) (hv : v < 0) : x - v = x + (v.natAbs : Int) := by
  have he : (v.natAbs : Int) = -v := Int.ofNat_natAbs_of_nonpos (by omega)
  omega

end Solidity.Bridge.Arith

#print axioms Solidity.Bridge.Arith.castPlan_typed
#print axioms Solidity.Bridge.Arith.castCapture_factor
#print axioms Solidity.Bridge.Arith.intTyOf_head
#print axioms Solidity.Bridge.Arith.narrowWrap_uint

#print axioms Solidity.Bridge.Arith.castCapture_typed
#print axioms Solidity.Bridge.Arith.narrowWrap_int
#print axioms Solidity.Bridge.Arith.narrowWrap_int_pow
#print axioms Solidity.Bridge.Arith.narrowWrap_uint_bnot
#print axioms Solidity.Bridge.Arith.narrowWrap_uint_shl

#print axioms Solidity.Bridge.Arith.narrowWrap_int_div
#print axioms Solidity.Bridge.Arith.narrowCheck_guard
#print axioms Solidity.Bridge.Arith.narrowCheck_full

#print axioms Solidity.Bridge.Arith.narrowWrap_int_add_negative
#print axioms Solidity.Bridge.Arith.narrowWrap_int_sub_negative
#print axioms Solidity.Bridge.Arith.narrowWrap_int_pow_literal
#print axioms Solidity.Bridge.Arith.negative_literal_add
#print axioms Solidity.Bridge.Arith.negative_literal_sub
