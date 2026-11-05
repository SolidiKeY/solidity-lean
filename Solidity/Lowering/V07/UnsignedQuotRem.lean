import Solidity.Lowering.V07.UnsignedAddition
import Solidity.Lowering.V07.AliasRhsSubtraction

/-! Unsigned division/remainder clauses over independent Source execution and
existing intrinsic values. Nonzero results need no width narrowing. Zero
observations are recorded separately without equating their failure payloads. -/
namespace Solidity.Lowering.V07.UnsignedQuotRem
open UnsignedNarrowing (ty)

def calculate (rem : Bool) (x y : Int) : Int := if rem then x.tmod y else x.tdiv y
def sourceOp (rem : Bool) : Source.BinOp := if rem then .mod else .div

def value {C : Contract} {Γ : Ctx} (rem : Bool) (a b : Val C Γ .uint) : Val C Γ .uint :=
  if rem then .binop .mod rfl rfl a b else .binop .div rfl rfl a b

theorem result_range (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (rem : Bool) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi) (hn : y ≠ 0) :
    (ty bits valid).lo ≤ calculate rem x y ∧ calculate rem x y ≤ (ty bits valid).hi := by
  have hx0 : 0 ≤ x := hx.1
  have hy0 : 0 ≤ y := hy.1
  have yp : 0 < y := by omega
  cases rem
  · exact ⟨Int.tdiv_nonneg hx0 hy0,Int.le_trans (Int.tdiv_le_self y hx0) hx.2⟩
  · change 0 ≤ x.tmod y ∧ x.tmod y ≤ _
    rw [Int.tmod_eq_emod_of_nonneg hx0]
    exact ⟨Int.emod_nonneg x (by omega),Int.le_trans (Int.le_of_lt (Int.emod_lt_of_pos x yp)) hy.2⟩

theorem source_value (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {D : Source.Layout} (checked rem : Bool) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi) (hn : y ≠ 0) :
    Source.binVal checked (sourceOp rem) (.int x hx : Source.Val D (.int (ty bits valid))) (.int y hy) =
      .ok (.int (calculate rem x y) (result_range bits valid rem x y hx hy hn)) := by
  cases rem
  · change (if y = 0 then Source.panic .divZero else Source.intRes (ty bits valid) checked (calculate false x y)) = _
    simp only [if_neg hn,Source.intRes,dif_pos (result_range bits valid false x y hx hy hn)]
    rfl
  · change (if y = 0 then Source.panic .divZero else Source.intRes (ty bits valid) checked (calculate true x y)) = _
    simp only [if_neg hn,Source.intRes,dif_pos (result_range bits valid true x y hx hy hn)]
    rfl

theorem source_zero (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {D : Source.Layout} (checked rem : Bool) (x : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi) :
    Source.binVal checked (sourceOp rem) (.int x hx : Source.Val D (.int (ty bits valid)))
      (.int 0 (integer_zero_range (ty bits valid))) = .error (.revert (Source.panicData .divZero)) := by
  cases rem <;> rfl

theorem value_run (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {C : Contract} {Γ : Ctx} (target : State C Γ) (rem : Bool) (a b : Val C Γ .uint)
    (x y : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi) (hn : y ≠ 0)
    (left : a.evalT target = .ok (integerValue (ty bits valid) x hx))
    (right : b.evalT target = .ok (integerValue (ty bits valid) y hy)) :
    (value rem a b).evalT target = .ok (integerValue (ty bits valid) (calculate rem x y)
      (result_range bits valid rem x y hx hy hn)) := by
  cases rem
  · have hr := integer_range (ty bits valid) (calculate false x y) (result_range bits valid false x y hx hy hn)
    change PrimTy.uint.inRange (x.tdiv y) = true at hr
    change (Val.binop .div rfl rfl a b).evalT target = _
    rw [Val.evalT,left]
    change (do
      let v ← b.evalT target
      TRes.ofOpt (BinOp.evalT .div rfl (integerValue (ty bits valid) x hx) v)) = _
    rw [right]
    change TRes.ofOpt ((if y = 0 then none else some (x.tdiv y)).bind PrimTy.uint.ofInt?) = _
    simp only [if_neg hn,Option.bind_some,PrimTy.ofInt?,dif_pos hr]
    rfl
  · have hr := integer_range (ty bits valid) (calculate true x y) (result_range bits valid true x y hx hy hn)
    change PrimTy.uint.inRange (x.tmod y) = true at hr
    change (Val.binop .mod rfl rfl a b).evalT target = _
    rw [Val.evalT,left]
    change (do
      let v ← b.evalT target
      TRes.ofOpt (BinOp.evalT .mod rfl (integerValue (ty bits valid) x hx) v)) = _
    rw [right]
    change TRes.ofOpt ((if y = 0 then none else some (x.tmod y)).bind PrimTy.uint.ofInt?) = _
    simp only [if_neg hn,Option.bind_some,PrimTy.ofInt?,dif_pos hr]
    rfl

theorem value_zero (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {C : Contract} {Γ : Ctx} (target : State C Γ) (rem : Bool) (a b : Val C Γ .uint)
    (x : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (left : a.evalT target = .ok (integerValue (ty bits valid) x hx))
    (right : b.evalT target = .ok (integerValue (ty bits valid) 0 (integer_zero_range (ty bits valid)))) :
    (value rem a b).evalT target = .error .revert := by
  cases rem
  · change (Val.binop .div rfl rfl a b).evalT target = _
    rw [Val.evalT,left]
    change (do
      let v ← b.evalT target
      TRes.ofOpt (BinOp.evalT .div rfl (integerValue (ty bits valid) x hx) v)) = _
    rw [right]
    rfl
  · change (Val.binop .mod rfl rfl a b).evalT target = _
    rw [Val.evalT,left]
    change (do
      let v ← b.evalT target
      TRes.ofOpt (BinOp.evalT .mod rfl (integerValue (ty bits valid) x hx) v)) = _
    rw [right]
    rfl

theorem source_from_pair (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source mid : Source.EMState E Γ) (rem : Bool) (a b : Source.RExpr E Γ (.int (ty bits valid)))
    (x y : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi) (hn : y ≠ 0)
    (pair : (Source.evalPair G F fuel a b).run source = (.ok (.val (.int x hx),.val (.int y hy)),mid)) :
    (Source.evalE G F (fuel+1) (.binary (sourceOp rem) a b)).run source =
      (.ok (.val (.int (calculate rem x y) (result_range bits valid rem x y hx hy hn))),mid) := by
  cases rem
  · rw [Source.evalE]
    simp only [sourceOp,reduceCtorEq,decide_false,Bool.false_or,Bool.false_eq_true,if_false]
    rw [Source.Hoare.run_bind,pair]
    change (do
      let v ← Source.EM.lift (Source.binVal F.checked .div
        (.int x hx : Source.Val E.layout (.int (ty bits valid))) (.int y hy))
      pure (Source.RVal.val v)).run mid = _
    have step := source_value bits valid (D := E.layout) F.checked false x y hx hy hn
    simp only [sourceOp,Bool.false_eq_true,if_false] at step
    rw [step]
    rfl
  · rw [Source.evalE]
    simp only [sourceOp,reduceCtorEq,decide_false,Bool.false_or,Bool.false_eq_true,if_false,if_true]
    rw [Source.Hoare.run_bind,pair]
    change (do
      let v ← Source.EM.lift (Source.binVal F.checked .mod
        (.int x hx : Source.Val E.layout (.int (ty bits valid))) (.int y hy))
      pure (Source.RVal.val v)).run mid = _
    have step := source_value bits valid (D := E.layout) F.checked true x y hx hy hn
    simp only [sourceOp,if_true] at step
    rw [step]
    rfl

theorem source_pair_zero (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source mid : Source.EMState E Γ) (rem : Bool) (a b : Source.RExpr E Γ (.int (ty bits valid)))
    (x : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (pair : (Source.evalPair G F fuel a b).run source =
      (.ok (.val (.int x hx),.val (.int 0 (integer_zero_range (ty bits valid)))),mid)) :
    (Source.evalE G F (fuel+1) (.binary (sourceOp rem) a b)).run source =
      (.error (.revert (Source.panicData .divZero)),mid) := by
  cases rem
  · rw [Source.evalE]
    simp only [sourceOp,reduceCtorEq,decide_false,Bool.false_or,Bool.false_eq_true,if_false]
    rw [Source.Hoare.run_bind,pair]
    change (do
      let v ← Source.EM.lift (Source.binVal F.checked .div
        (.int x hx : Source.Val E.layout (.int (ty bits valid))) (.int 0 (integer_zero_range (ty bits valid))))
      pure (Source.RVal.val v)).run mid = _
    have step := source_zero bits valid (D := E.layout) F.checked false x hx
    simp only [sourceOp,Bool.false_eq_true,if_false] at step
    rw [step]
    rfl
  · rw [Source.evalE]
    simp only [sourceOp,reduceCtorEq,decide_false,Bool.false_or,Bool.false_eq_true,if_false,if_true]
    rw [Source.Hoare.run_bind,pair]
    change (do
      let v ← Source.EM.lift (Source.binVal F.checked .mod
        (.int x hx : Source.Val E.layout (.int (ty bits valid))) (.int 0 (integer_zero_range (ty bits valid))))
      pure (Source.RVal.val v)).run mid = _
    have step := source_zero bits valid (D := E.layout) F.checked true x hx
    simp only [sourceOp,if_true] at step
    rw [step]
    rfl

/-- Initial local alignment derives both successful executions; the output
range is proved above rather than supplied as a preservation premise. -/
theorem locals_transport (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (rem : Bool)
    (si : ι → Source.Idx srcΓ (.int (ty bits valid))) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily (ty bits valid) si ti source.1 target.env) (a b : ι)
    (x y : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi) (hn : y ≠ 0)
    (readA : source.1.get (si a) = .int x hx) (readB : source.1.get (si b) = .int y hy) :
    (Source.evalE G F (fuel+3) (.binary (sourceOp rem) (.local (si a)) (.local (si b)))).run source =
      (.ok (.val (.int (calculate rem x y) (result_range bits valid rem x y hx hy hn))),source) ∧
    (value rem (.simple (.local (ti a))) (.simple (.local (ti b)))).evalT target =
      .ok (integerValue (ty bits valid) (calculate rem x y) (result_range bits valid rem x y hx hy hn)) ∧
    IntValueRel (ty bits valid)
      (.int (calculate rem x y) (result_range bits valid rem x y hx hy hn) : Source.Val E.layout (.int (ty bits valid)))
      (integerValue (ty bits valid) (calculate rem x y) (result_range bits valid rem x y hx hy hn)) := by
  exact ⟨source_from_pair bits valid G F (fuel+2) source source rem _ _ x y hx hy hn
      (source_local_pair G F fuel source (ty bits valid) (si a) (si b) x y hx hy readA readB),
    value_run bits valid target rem _ _ x y hx hy hn
      (congrArg Except.ok (family.read a x hx readA)) (congrArg Except.ok (family.read b y hy readB)),
    integer_related _ _ _⟩

/-- Exact zero observations only: Source retains its panic bytes while the
intrinsic value evaluator returns plain revert. No failure-payload relation is
invented or inferred from their common failure category. -/
theorem locals_zero (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (rem : Bool)
    (si : ι → Source.Idx srcΓ (.int (ty bits valid))) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily (ty bits valid) si ti source.1 target.env) (a b : ι)
    (x : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (readA : source.1.get (si a) = .int x hx)
    (readB : source.1.get (si b) = .int 0 (integer_zero_range (ty bits valid))) :
    (Source.evalE G F (fuel+3) (.binary (sourceOp rem) (.local (si a)) (.local (si b)))).run source =
      (.error (.revert (Source.panicData .divZero)),source) ∧
    (value rem (.simple (.local (ti a))) (.simple (.local (ti b)))).evalT target = .error .revert := by
  exact ⟨source_pair_zero bits valid G F (fuel+2) source source rem _ _ x hx
      (source_local_pair G F fuel source (ty bits valid) (si a) (si b) x 0 hx
        (integer_zero_range (ty bits valid)) readA readB),
    value_zero bits valid target rem _ _ x hx
      (congrArg Except.ok (family.read a x hx readA))
      (congrArg Except.ok (family.read b 0 (integer_zero_range (ty bits valid)) readB))⟩

end Solidity.Lowering.V07.UnsignedQuotRem

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRem.result_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRem.result_range

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRem.source_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRem.source_value

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRem.source_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRem.source_zero

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRem.value_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRem.value_run

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRem.value_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRem.value_zero

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRem.source_from_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRem.source_from_pair

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRem.source_pair_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRem.source_pair_zero

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRem.locals_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRem.locals_transport

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRem.locals_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRem.locals_zero
