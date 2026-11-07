import Solidity.Lowering.V07.IntegerConstantAssignment

/-! Integral rational constants need no denominator-one representation premise.
Existing Source rational meaning and implicit range typing determine the value. -/
namespace Solidity.Lowering.V07.IntegralRationalConstants

theorem allowed (E : Source.Env) (q : Source.Q) (t : Source.IntTy) (h : q.FitsInt t) :
    (Source.STy.rational q).implicit E.isBase E.mapFree (.int t) = true := by
  rw [Source.STy.implicit_rational_int]
  exact decide_eq_true h

theorem numerator (q : Source.Q) (integral : q.isInt = true) :
    q.num = q.toInt * (q.den : Int) := by
  have zero : q.num % (q.den : Int) = 0 := eq_of_beq integral
  exact (Int.ediv_mul_cancel_of_emod_eq_zero zero).symm

theorem eqv_integer (q : Source.Q) (integral : q.isInt = true) :
    q.Eqv (Source.Q.ofInt q.toInt) := by
  change q.num * (1 : Int) = q.toInt * (q.den : Int)
  simpa only [Int.mul_one] using numerator q integral

theorem source_value {D : Source.Layout} (q : Source.Q) (t : Source.IntTy) (h : q.FitsInt t) :
    Source.constVal q (.int t) = .ok (.int q.toInt h.2 : Source.Val D (.int t)) := by
  simp only [Source.constVal,h.1,if_true]
  unfold Source.mkInt
  rw [dif_pos h.2]
  rfl

theorem source_run {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel : Nat) (source : Source.EMState E Γ) (q : Source.Q) (t : Source.IntTy) (h : q.FitsInt t) :
    (Source.evalE G F (fuel+2) (.conv (.const q) (.inl (allowed E q t h)))).run source =
      (.ok (.val (.int q.toInt h.2)),source) := by
  change (Source.convRV F (fuel+1) (.int t) (.const q)).run source = _
  unfold Source.convRV
  rw [dif_neg (by intro impossible; cases impossible)]
  change (do
    let x ← Source.EM.lift (Source.constVal q (.int t))
    pure (Source.RVal.val x)).run source = _
  rw [source_value q t h]
  rfl

theorem transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ)
    (target : State C Γ) (q : Source.Q) (t : Source.IntTy) (h : q.FitsInt t) :
    (Source.evalE G F (fuel+2) (.conv (.const q) (.inl (allowed E q t h)))).run source =
      (.ok (.val (.int q.toInt h.2)),source) ∧
    (IntegerConstants.operand t q.toInt h.2).run target =
      .ok (⟨target,List.prefix_refl _⟩,.prim (integerValue t q.toInt h.2)) ∧
    IntValueRel t (.int q.toInt h.2 : Source.Val E.layout (.int t)) (integerValue t q.toInt h.2) := by
  exact ⟨source_run G F fuel source q t h,
    IntegerConstants.operand_run target t q.toInt h.2,integer_related t q.toInt h.2⟩

theorem source_assignment {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel : Nat) (source : Source.EMState E Γ) (q : Source.Q) (t : Source.IntTy)
    (i : Source.Idx Γ (.int t)) (h : q.FitsInt t) :
    (Source.evalE G F (fuel+3) (.assign (.local i)
      (.conv (.const q) (.inl (allowed E q t h))))).run source =
      (.ok (.val (.int q.toInt h.2)),(source.1.set i (.int q.toInt h.2),source.2)) := by
  rw [Source.evalE,Source.Hoare.run_bind,source_run G F fuel source q t h]
  rfl

theorem assignment_transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ)
    (target : State C Γ) (q : Source.Q) (t : Source.IntTy) (h : q.FitsInt t)
    (si : ι → Source.Idx srcΓ (.int t)) (ti : ι → Idx Γ (.val (integerPrim t)))
    (family : IntegerLocalFamily t si ti source.1 target.env) (i : ι) :
    (Source.evalE G F (fuel+3) (.assign (.local (si i))
      (.conv (.const q) (.inl (allowed E q t h))))).run source =
      (.ok (.val (.int q.toInt h.2)),(source.1.set (si i) (.int q.toInt h.2),source.2)) ∧
    (IntegerConstantAssignment.operand t (ti i) q.toInt h.2).run target =
      .ok (⟨target.setLocal (ti i) (integerValue t q.toInt h.2),List.prefix_refl _⟩,
        .prim (integerValue t q.toInt h.2)) ∧
    IntValueRel t (.int q.toInt h.2 : Source.Val E.layout (.int t)) (integerValue t q.toInt h.2) ∧
    IntegerLocalFamily t si ti (source.1.set (si i) (.int q.toInt h.2))
      (TEnv.set (ti i) (integerValue t q.toInt h.2) target.env) := by
  exact ⟨source_assignment G F fuel source q t (si i) h,
    IntegerConstantAssignment.operand_run target t (ti i) q.toInt h.2,
    integer_related t q.toInt h.2,
    IntegerConstantAssignment.family_write t si ti source.1 target.env family i q.toInt h.2⟩

theorem fractional_refused {D : Source.Layout} (q : Source.Q) (t : Source.IntTy)
    (fractional : q.isInt = false) :
    Source.constVal q (.int t) =
      (.error (.stuck "fractional constant at an integer type") : Source.R (Source.Val D (.int t))) := by
  simp only [Source.constVal,fractional,Bool.false_eq_true,if_false]
  rfl

theorem integral_outside_refused {D : Source.Layout} (q : Source.Q) (t : Source.IntTy)
    (integral : q.isInt = true) (outside : ¬ (t.lo ≤ q.toInt ∧ q.toInt ≤ t.hi)) :
    Source.constVal q (.int t) =
      (.error (.stuck "integer out of range") : Source.R (Source.Val D (.int t))) := by
  simp only [Source.constVal,integral,if_true]
  unfold Source.mkInt
  rw [dif_neg outside]
  rfl

theorem not_allowed (E : Source.Env) (q : Source.Q) (t : Source.IntTy) (refused : ¬ q.FitsInt t) :
    (Source.STy.rational q).implicit E.isBase E.mapFree (.int t) = false := by
  rw [Source.STy.implicit_rational_int]
  exact decide_eq_false refused

/-- info: 'Solidity.Lowering.V07.IntegralRationalConstants.allowed' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegralRationalConstants.allowed

/-- info: 'Solidity.Lowering.V07.IntegralRationalConstants.numerator' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegralRationalConstants.numerator

/-- info: 'Solidity.Lowering.V07.IntegralRationalConstants.eqv_integer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegralRationalConstants.eqv_integer

/-- info: 'Solidity.Lowering.V07.IntegralRationalConstants.source_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegralRationalConstants.source_value

/-- info: 'Solidity.Lowering.V07.IntegralRationalConstants.source_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegralRationalConstants.source_run

/-- info: 'Solidity.Lowering.V07.IntegralRationalConstants.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegralRationalConstants.transport

/-- info: 'Solidity.Lowering.V07.IntegralRationalConstants.source_assignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegralRationalConstants.source_assignment

/-- info: 'Solidity.Lowering.V07.IntegralRationalConstants.assignment_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegralRationalConstants.assignment_transport

/-- info: 'Solidity.Lowering.V07.IntegralRationalConstants.fractional_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegralRationalConstants.fractional_refused

/-- info: 'Solidity.Lowering.V07.IntegralRationalConstants.integral_outside_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegralRationalConstants.integral_outside_refused

/-- info: 'Solidity.Lowering.V07.IntegralRationalConstants.not_allowed' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegralRationalConstants.not_allowed

end Solidity.Lowering.V07.IntegralRationalConstants
