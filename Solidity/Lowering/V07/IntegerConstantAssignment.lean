import Solidity.Lowering.V07.IntegerConstants
import Solidity.Lowering.V07.IntegerLocalFamily

/-! Literal assignment uses existing source locations and intrinsic typed writes.
Family alias reflection is preserved separately from numeric content agreement. -/
namespace Solidity.Lowering.V07.IntegerConstantAssignment

theorem source_run {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel : Nat) (source : Source.EMState E Γ) (t : Source.IntTy)
    (i : Source.Idx Γ (.int t)) (z : Int) (bound : t.lo ≤ z ∧ z ≤ t.hi) :
    (Source.evalE G F (fuel+3) (.assign (.local i)
      (.conv (.const (Source.Q.ofInt z)) (.inl (IntegerConstants.allowed E t z bound))))).run source =
      (.ok (.val (.int z bound)),(source.1.set i (.int z bound),source.2)) := by
  rw [Source.evalE,Source.Hoare.run_bind,IntegerConstants.source_run G F fuel source t z bound]
  rfl

def code {C : Contract} {Γ : Ctx} (t : Source.IntTy) (i : Idx Γ (.val (integerPrim t)))
    (z : Int) (bound : t.lo ≤ z ∧ z ≤ t.hi) : Prog C Γ (.val (integerPrim t) :: Γ) :=
  .cons (.assignLocal i (IntegerConstants.value t z bound))
    (.cons (.declLocal (integerPrim t) (.user "v07_literal_assignment")
      (some (.simple (.local i)))) .nil)

theorem code_run {C : Contract} {Γ : Ctx} (target : State C Γ) (t : Source.IntTy)
    (i : Idx Γ (.val (integerPrim t))) (z : Int) (bound : t.lo ≤ z ∧ z ≤ t.hi) :
    (code t i z bound).run target = .ok (⟨(target.setLocal i (integerValue t z bound)).push
      (t := .val (integerPrim t)) (integerValue t z bound),List.prefix_refl _⟩) := by
  have assign : (Stmt.assignLocal i (IntegerConstants.value t z bound)).run target =
      .ok (⟨target.setLocal i (integerValue t z bound),List.prefix_refl _⟩) := by
    change (do
      let v ← (IntegerConstants.value t z bound).evalT target
      pure (⟨target.setLocal i v,List.prefix_refl _⟩ : Out C target.H Γ)) = _
    rw [IntegerConstants.value_run]
    rfl
  have capture : (Stmt.declLocal (integerPrim t) (.user "v07_literal_assignment")
      (some (.simple (.local i)))).run (target.setLocal i (integerValue t z bound)) =
      .ok (⟨(target.setLocal i (integerValue t z bound)).push
        (t := .val (integerPrim t)) (integerValue t z bound),List.prefix_refl _⟩) := by
    change Except.ok (⟨(target.setLocal i (integerValue t z bound)).push
      (t := .val (integerPrim t)) (TEnv.get i (TEnv.set i (integerValue t z bound) target.env)),
      List.prefix_refl _⟩ : Out C target.H (.val (integerPrim t) :: Γ)) = _
    rw [TEnv.get_set]
  unfold code
  rw [Prog.run_cons_ok assign,Prog.run_cons_ok capture,Prog.run_nil]
  rfl

def operand {C : Contract} {Γ : Ctx} (t : Source.IntTy) (i : Idx Γ (.val (integerPrim t)))
    (z : Int) (bound : t.lo ≤ z ∧ z ≤ t.hi) : DeferredSource.Operand C Γ (.prim (integerPrim t)) :=
  ⟨_,code t i z bound,.val (.simple (.local .here))⟩

theorem operand_run {C : Contract} {Γ : Ctx} (target : State C Γ) (t : Source.IntTy)
    (i : Idx Γ (.val (integerPrim t))) (z : Int) (bound : t.lo ≤ z ∧ z ≤ t.hi) :
    (operand t i z bound).run target = .ok (⟨target.setLocal i (integerValue t z bound),
      List.prefix_refl _⟩,.prim (integerValue t z bound)) := by
  unfold operand DeferredSource.Operand.run
  rw [code_run]
  rfl

theorem family_write {D : Source.Layout} {srcΓ : Source.RCtx} {C : Contract} {H : HTy}
    {Γ : Ctx} {ι : Type} (t : Source.IntTy) (si : ι → Source.Idx srcΓ (.int t))
    (ti : ι → Idx Γ (.val (integerPrim t))) (source : Source.Locals D srcΓ) (target : TEnv C H Γ)
    (family : IntegerLocalFamily t si ti source target) (i : ι) (z : Int) (bound : t.lo ≤ z ∧ z ≤ t.hi) :
    IntegerLocalFamily t si ti (source.set (si i) (.int z bound))
      (TEnv.set (ti i) (integerValue t z bound) target) := by
  refine ⟨?_,family.aliases⟩
  intro k
  by_cases same : (si i).toNat = (si k).toNat
  · have hs := source_idx_injective _ _ same
    have ht := Idx.toNat_inj _ _ ((family.aliases i k).mp same)
    rw [←hs,←ht,source_locals_get_set,TEnv.get_set]
    exact integer_related t z bound
  · have ht : (ti i).toNat ≠ (ti k).toNat := fun e => same ((family.aliases i k).mpr e)
    rw [source_locals_get_set_ne source _ _ _ same,TEnv.get_set_ne _ _ _ target ht]
    exact family.values k

theorem transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ)
    (target : State C Γ) (t : Source.IntTy) (si : ι → Source.Idx srcΓ (.int t))
    (ti : ι → Idx Γ (.val (integerPrim t)))
    (family : IntegerLocalFamily t si ti source.1 target.env) (i : ι)
    (z : Int) (bound : t.lo ≤ z ∧ z ≤ t.hi) :
    (Source.evalE G F (fuel+3) (.assign (.local (si i))
      (.conv (.const (Source.Q.ofInt z)) (.inl (IntegerConstants.allowed E t z bound))))).run source =
      (.ok (.val (.int z bound)),(source.1.set (si i) (.int z bound),source.2)) ∧
    (operand t (ti i) z bound).run target = .ok (⟨target.setLocal (ti i) (integerValue t z bound),
      List.prefix_refl _⟩,.prim (integerValue t z bound)) ∧
    IntValueRel t (.int z bound : Source.Val E.layout (.int t)) (integerValue t z bound) ∧
    IntegerLocalFamily t si ti (source.1.set (si i) (.int z bound))
      (TEnv.set (ti i) (integerValue t z bound) target.env) := by
  exact ⟨source_run G F fuel source t (si i) z bound,
    operand_run target t (ti i) z bound,integer_related t z bound,
    family_write t si ti source.1 target.env family i z bound⟩

/-- info: 'Solidity.Lowering.V07.IntegerConstantAssignment.source_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantAssignment.source_run

/-- info: 'Solidity.Lowering.V07.IntegerConstantAssignment.code_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantAssignment.code_run

/-- info: 'Solidity.Lowering.V07.IntegerConstantAssignment.operand_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantAssignment.operand_run

/-- info: 'Solidity.Lowering.V07.IntegerConstantAssignment.family_write' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantAssignment.family_write

/-- info: 'Solidity.Lowering.V07.IntegerConstantAssignment.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantAssignment.transport

end Solidity.Lowering.V07.IntegerConstantAssignment
