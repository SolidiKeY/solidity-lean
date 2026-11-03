import Solidity.Lowering.V07.AssignmentOrder

/-! In-range subtraction is a supported arithmetic clause, not full narrow
wrapping or checked-failure coverage. Numeric bounds are on input integers. -/
namespace Solidity.Lowering.V07

theorem integer_sub_accepts (t : Source.IntTy) : BinOp.sub.accepts (integerPrim t) = true := by
  cases h : t.signed <;> simp only [integerPrim,h,Bool.false_eq_true,if_false,if_true] <;> rfl

theorem integer_sub_eval (t : Source.IntTy) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (hz : t.lo ≤ x-y ∧ x-y ≤ t.hi) :
    BinOp.evalT .sub (integer_sub_accepts t) (integerValue t x hx) (integerValue t y hy) =
      some (integerValue t (x-y) hz) := by
  obtain ⟨sign,bits,valid⟩ := t
  cases sign
  · have hr := integer_range ⟨false,bits,valid⟩ (x-y) hz
    change PrimTy.uint.inRange (x-y) = true at hr
    change (BinOp.arithInt .sub x y).bind PrimTy.uint.ofInt? = some ⟨x-y,hr⟩
    simp only [BinOp.arithInt,Option.bind_some,PrimTy.ofInt?,dif_pos hr]
  · have hr := integer_range ⟨true,bits,valid⟩ (x-y) hz
    change PrimTy.int.inRange (x-y) = true at hr
    change (BinOp.arithInt .sub x y).bind PrimTy.int.ofInt? = some ⟨x-y,hr⟩
    simp only [BinOp.arithInt,Option.bind_some,PrimTy.ofInt?,dif_pos hr]

theorem source_sub_in_range {D : Source.Layout} (t : Source.IntTy) (checked : Bool)
    (x y : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (hz : t.lo ≤ x-y ∧ x-y ≤ t.hi) :
    Source.binVal checked .sub (.int x hx : Source.Val D (.int t)) (.int y hy) =
      .ok (.int (x-y) hz) := by
  simp only [Source.binVal,Source.intBin,Source.intRes,dif_pos hz]
  rfl

theorem sub_not_short (p : PrimTy) (x : p.Denote) : BinOp.shortT .sub x = none := by
  cases p <;> rfl

theorem intrinsic_sub_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (t : Source.IntTy) (left right : Val C Γ (integerPrim t)) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (hz : t.lo ≤ x-y ∧ x-y ≤ t.hi)
    (leftRun : left.evalT target = .ok (integerValue t x hx))
    (rightRun : right.evalT target = .ok (integerValue t y hy)) :
    (Val.binop .sub (integer_sub_accepts t) rfl left right).evalT target =
      .ok (integerValue t (x-y) hz) := by
  rw [Val.evalT,leftRun]
  change (match BinOp.shortT .sub (integerValue t x hx) with
    | some z => Except.ok z
    | none => do
      let y' ← right.evalT target
      TRes.ofOpt (BinOp.evalT .sub (integer_sub_accepts t) (integerValue t x hx) y')) = _
  rw [sub_not_short]
  rw [rightRun]
  change TRes.ofOpt (BinOp.evalT .sub (integer_sub_accepts t)
    (integerValue t x hx) (integerValue t y hy)) = _
  rw [integer_sub_eval t x y hx hy hz]
  rfl

/-- Reached-state composition rule; concrete assignment below supplies the
pair premise from actual operations rather than assuming a final result. -/
theorem source_sub_of_pair {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source mid : Source.EMState E Γ) (t : Source.IntTy)
    (left right : Source.RExpr E Γ (.int t)) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (hz : t.lo ≤ x-y ∧ x-y ≤ t.hi)
    (pair : (Source.evalPair G F fuel left right).run source =
      (.ok (.val (.int x hx),.val (.int y hy)),mid)) :
    (Source.evalE G F (fuel+1) (.binary .sub left right)).run source =
      (.ok (.val (.int (x-y) hz)),mid) := by
  rw [Source.evalE]
  simp only [reduceCtorEq,decide_false,Bool.false_or,Bool.false_eq_true,if_false]
  rw [Source.Hoare.run_bind,pair]
  change (do
    let z ← Source.EM.lift (Source.binVal F.checked .sub
      (.int x hx : Source.Val E.layout (.int t)) (.int y hy))
    pure (Source.RVal.val z)).run mid = _
  rw [source_sub_in_range t F.checked x y hx hy hz]
  rfl

theorem source_assign_sub_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (t : Source.IntTy) (i a : Source.Idx Γ (.int t)) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (readA : source.1.get a = .int x hx) (readI : source.1.get i = .int y hy)
    (hz : t.lo ≤ x-(if G.pipeline = .legacy then y else x) ∧
      x-(if G.pipeline = .legacy then y else x) ≤ t.hi) :
    (Source.evalE G F (fuel+4)
      (.binary .sub (.assign (.local i) (.local a)) (.local i))).run source =
      (.ok (.val (.int (x-(if G.pipeline = .legacy then y else x)) hz)),
        (source.1.set i (.int x hx),source.2)) := by
  have pair := source_assign_read_pair G F fuel source i a (.int x hx) (.int y hy) readA readI
  by_cases order : G.pipeline = .legacy
  · simp only [order,if_true] at pair hz ⊢
    exact source_sub_of_pair G F (fuel+3) source _ t _ _ x y hx hy hz pair
  · simp only [order,if_false] at pair hz ⊢
    exact source_sub_of_pair G F (fuel+3) source _ t _ _ x x hx hx hz pair

end Solidity.Lowering.V07
