import Solidity.Lowering.V07.Operands

/-! Integer constant conversion and actual fresh native capture. Source literal
conversion evidence follows the existing range judgment, not a new profile guard. -/
namespace Solidity.Lowering.V07.IntegerConstants

theorem fits (t : Source.IntTy) (z : Int) (bound : t.lo ≤ z ∧ z ≤ t.hi) :
    (Source.Q.ofInt z).FitsInt t := by
  simpa only [Source.Q.FitsInt,Source.Q.ofInt,Source.Q.isInt,Source.Q.toInt,Int.emod_one,
    Int.natCast_one,Int.ediv_one,BEq.rfl,true_and] using bound

theorem allowed (E : Source.Env) (t : Source.IntTy) (z : Int) (bound : t.lo ≤ z ∧ z ≤ t.hi) :
    (Source.STy.rational (Source.Q.ofInt z)).implicit E.isBase E.mapFree (.int t) = true := by
  rw [Source.STy.implicit_rational_int]
  exact decide_eq_true (fits t z bound)

theorem source_value {D : Source.Layout} (t : Source.IntTy) (z : Int) (bound : t.lo ≤ z ∧ z ≤ t.hi) :
    Source.constVal (Source.Q.ofInt z) (.int t) = .ok (.int z bound : Source.Val D (.int t)) := by
  simp only [Source.constVal,Source.Q.ofInt,Source.Q.isInt,Source.Q.toInt,Int.emod_one,
    Int.natCast_one,Int.ediv_one,BEq.rfl,if_true]
  unfold Source.mkInt
  rw [dif_pos bound]
  rfl

theorem source_run {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel : Nat) (source : Source.EMState E Γ) (t : Source.IntTy) (z : Int) (bound : t.lo ≤ z ∧ z ≤ t.hi) :
    (Source.evalE G F (fuel+2)
      (.conv (.const (Source.Q.ofInt z)) (.inl (allowed E t z bound)))).run source =
      (.ok (.val (.int z bound)),source) := by
  change (Source.convRV F (fuel+1) (.int t) (.const (Source.Q.ofInt z))).run source = _
  unfold Source.convRV
  rw [dif_neg (by intro h; cases h)]
  change (do
    let x ← Source.EM.lift (Source.constVal (Source.Q.ofInt z) (.int t))
    pure (Source.RVal.val x)).run source = _
  rw [source_value]
  rfl

def value {C : Contract} {Γ : Ctx} (t : Source.IntTy) (z : Int) (bound : t.lo ≤ z ∧ z ≤ t.hi) :
    Val C Γ (integerPrim t) := .simple (.lit z (integer_range t z bound))

theorem value_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (t : Source.IntTy) (z : Int) (bound : t.lo ≤ z ∧ z ≤ t.hi) :
    (value t z bound).evalT target = .ok (integerValue t z bound) := by
  obtain ⟨sign,bits,valid⟩ := t
  cases sign <;> rfl

def code {C : Contract} {Γ : Ctx} (t : Source.IntTy) (z : Int) (bound : t.lo ≤ z ∧ z ≤ t.hi) :
    Prog C Γ (.val (integerPrim t) :: Γ) :=
  .cons (.declLocal (integerPrim t) (.user "v07_integer_constant") (some (value t z bound))) .nil

theorem code_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (t : Source.IntTy) (z : Int) (bound : t.lo ≤ z ∧ z ≤ t.hi) :
    (code t z bound).run target =
      .ok (⟨target.push (t := .val (integerPrim t)) (integerValue t z bound),List.prefix_refl _⟩) := by
  have step : (Stmt.declLocal (integerPrim t) (.user "v07_integer_constant")
      (some (value t z bound))).run target =
      .ok (⟨target.push (t := .val (integerPrim t)) (integerValue t z bound),List.prefix_refl _⟩) := by
    change (do
      let v ← (value t z bound).evalT target
      pure (⟨target.push (t := .val (integerPrim t)) v,List.prefix_refl _⟩ : Out C target.H (.val (integerPrim t) :: Γ))) = _
    rw [value_run]
    rfl
  unfold code
  rw [Prog.run_cons_ok step,Prog.run_nil]
  rfl

def operand {C : Contract} {Γ : Ctx} (t : Source.IntTy) (z : Int) (bound : t.lo ≤ z ∧ z ≤ t.hi) :
    DeferredSource.Operand C Γ (.prim (integerPrim t)) :=
  ⟨_,code t z bound,.val (.simple (.local .here))⟩

theorem operand_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (t : Source.IntTy) (z : Int) (bound : t.lo ≤ z ∧ z ≤ t.hi) :
    (operand t z bound).run target = .ok (⟨target,List.prefix_refl _⟩,.prim (integerValue t z bound)) := by
  unfold operand DeferredSource.Operand.run
  rw [code_run]
  rfl

theorem transport {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ) (target : State C Δ)
    (t : Source.IntTy) (z : Int) (bound : t.lo ≤ z ∧ z ≤ t.hi) :
    (Source.evalE G F (fuel+2)
      (.conv (.const (Source.Q.ofInt z)) (.inl (allowed E t z bound)))).run source =
      (.ok (.val (.int z bound)),source) ∧
    (operand t z bound).run target = .ok (⟨target,List.prefix_refl _⟩,.prim (integerValue t z bound)) ∧
    IntValueRel t (.int z bound : Source.Val E.layout (.int t)) (integerValue t z bound) := by
  exact ⟨source_run G F fuel source t z bound,operand_run target t z bound,integer_related t z bound⟩
theorem source_refused {D : Source.Layout} (t : Source.IntTy) (z : Int)
    (outside : ¬ (t.lo ≤ z ∧ z ≤ t.hi)) :
    Source.constVal (Source.Q.ofInt z) (.int t) =
      (.error (.stuck "integer out of range") : Source.R (Source.Val D (.int t))) := by
  simp only [Source.constVal,Source.Q.ofInt,Source.Q.isInt,Source.Q.toInt,Int.emod_one,
    Int.natCast_one,Int.ediv_one,BEq.rfl,if_true]
  unfold Source.mkInt
  rw [dif_neg outside]
  rfl

theorem not_allowed (E : Source.Env) (t : Source.IntTy) (z : Int)
    (outside : ¬ (t.lo ≤ z ∧ z ≤ t.hi)) :
    (Source.STy.rational (Source.Q.ofInt z)).implicit E.isBase E.mapFree (.int t) = false := by
  rw [Source.STy.implicit_rational_int]
  apply decide_eq_false
  intro h
  apply outside
  simpa only [Source.Q.toInt,Source.Q.ofInt,Int.natCast_one,Int.ediv_one] using h.2

/-- info: 'Solidity.Lowering.V07.IntegerConstants.fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstants.fits

/-- info: 'Solidity.Lowering.V07.IntegerConstants.allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstants.allowed

/-- info: 'Solidity.Lowering.V07.IntegerConstants.source_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstants.source_value

/-- info: 'Solidity.Lowering.V07.IntegerConstants.source_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstants.source_run

/-- info: 'Solidity.Lowering.V07.IntegerConstants.value_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstants.value_run

/-- info: 'Solidity.Lowering.V07.IntegerConstants.code_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstants.code_run

/-- info: 'Solidity.Lowering.V07.IntegerConstants.operand_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstants.operand_run

/-- info: 'Solidity.Lowering.V07.IntegerConstants.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstants.transport

/-- info: 'Solidity.Lowering.V07.IntegerConstants.source_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstants.source_refused

/-- info: 'Solidity.Lowering.V07.IntegerConstants.not_allowed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstants.not_allowed

end Solidity.Lowering.V07.IntegerConstants
