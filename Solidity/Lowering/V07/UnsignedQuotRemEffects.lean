import Solidity.Lowering.V07.UnsignedQuotRemGuard

/-! Assignment/read quotient and remainder with actual Source pipeline order.
Existing capture prefixes and panic guards are composed over typed programs;
no operation AST, evaluator, failure projection or rollback semantics is added. -/
namespace Solidity.Lowering.V07.UnsignedQuotRemEffects
open UnsignedNarrowing (ty)
open UnsignedQuotRem (calculate sourceOp)

def divisor (p : Roadmap.Pipeline) (assigned old : Int) : Int :=
  if p = .legacy then old else assigned

theorem divisor_range (p : Roadmap.Pipeline) (t : Source.IntTy) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi) :
    t.lo ≤ divisor p x y ∧ divisor p x y ≤ t.hi := by
  cases p <;> assumption

def code {C : Contract} {Γ : Ctx} (p : Roadmap.Pipeline) (rem : Bool)
    (i a : Idx Γ (.val .uint)) : Prog C Γ (.val .uint :: .val .uint :: .val .uint :: Γ) :=
  match p with
  | .legacy => (assignReadPrefix p i a).join (UnsignedQuotRemGuard.code rem .here (.there .here))
  | .viaIR => (assignReadPrefix p i a).join (UnsignedQuotRemGuard.code rem (.there .here) .here)

def operand {C : Contract} {Γ : Ctx} (p : Roadmap.Pipeline) (rem : Bool)
    (i a : Idx Γ (.val .uint)) : DeferredSource.Operand C Γ (.prim .uint) :=
  ⟨_,code p rem i a,.val (.simple (.local .here))⟩

theorem source_success (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E Γ) (rem : Bool) (i a : Source.Idx Γ (.int (ty bits valid)))
    (x y : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (hn : divisor G.pipeline x y ≠ 0)
    (readA : source.1.get a = .int x hx) (readI : source.1.get i = .int y hy) :
    (Source.evalE G F (fuel+4) (.binary (sourceOp rem) (.assign (.local i) (.local a)) (.local i))).run source =
      (.ok (.val (.int (calculate rem x (divisor G.pipeline x y))
        (UnsignedQuotRem.result_range bits valid rem x _ hx (divisor_range G.pipeline _ x y hx hy) hn))),
        (source.1.set i (.int x hx),source.2)) := by
  have pair := source_assign_read_pair G F fuel source i a (.int x hx) (.int y hy) readA readI
  by_cases order : G.pipeline = .legacy
  · simp only [order,if_true] at pair
    simp only [divisor,order,if_true] at hn ⊢
    exact UnsignedQuotRem.source_from_pair bits valid G F (fuel+3) source _ rem _ _ x y hx hy hn pair
  · simp only [order,if_false] at pair
    simp only [divisor,order,if_false] at hn ⊢
    exact UnsignedQuotRem.source_from_pair bits valid G F (fuel+3) source _ rem _ _ x x hx hx hn pair

theorem source_zero (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E Γ) (rem : Bool) (i a : Source.Idx Γ (.int (ty bits valid)))
    (x y : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (hz : divisor G.pipeline x y = 0)
    (readA : source.1.get a = .int x hx) (readI : source.1.get i = .int y hy) :
    (Source.evalE G F (fuel+4) (.binary (sourceOp rem) (.assign (.local i) (.local a)) (.local i))).run source =
      (.error (.revert (Source.panicData .divZero)),(source.1.set i (.int x hx),source.2)) := by
  have pair := source_assign_read_pair G F fuel source i a (.int x hx) (.int y hy) readA readI
  by_cases order : G.pipeline = .legacy
  · simp only [order,if_true] at pair
    simp only [divisor,order,if_true] at hz
    subst y
    exact UnsignedQuotRem.source_pair_zero bits valid G F (fuel+3) source _ rem _ _ x hx pair
  · simp only [order,if_false] at pair
    simp only [divisor,order,if_false] at hz
    subst x
    exact UnsignedQuotRem.source_pair_zero bits valid G F (fuel+3) source _ rem _ _ 0 hx pair

/-- Actual target capture prefix, before either the arithmetic guard or result. -/
theorem prefix_run (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {C : Contract} {Γ : Ctx} (target : State C Γ) (p : Roadmap.Pipeline) (i a : Idx Γ (.val .uint))
    (x y : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (readA : TEnv.get a target.env = integerValue (ty bits valid) x hx)
    (readI : TEnv.get i target.env = integerValue (ty bits valid) y hy) :
    (assignReadPrefix p i a).run target =
      .ok (⟨((target.setLocal i (integerValue (ty bits valid) x hx)).push
        (integerValue (ty bits valid) (divisor p x y) (divisor_range p _ x y hx hy))).push
        (integerValue (ty bits valid) x hx),List.prefix_refl _⟩) := by
  cases p
  · exact assign_read_prefix_run .legacy target i a _ _ readA readI
  · exact assign_read_prefix_run .viaIR target i a _ _ readA readI

theorem code_success (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {C : Contract} {Γ : Ctx} (target : State C Γ) (p : Roadmap.Pipeline) (rem : Bool)
    (i a : Idx Γ (.val .uint)) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi) (hn : divisor p x y ≠ 0)
    (readA : TEnv.get a target.env = integerValue (ty bits valid) x hx)
    (readI : TEnv.get i target.env = integerValue (ty bits valid) y hy) :
    (code p rem i a).run target =
      .ok (⟨(((target.setLocal i (integerValue (ty bits valid) x hx)).push
        (integerValue (ty bits valid) (divisor p x y) (divisor_range p _ x y hx hy))).push
        (integerValue (ty bits valid) x hx)).push
        (integerValue (ty bits valid) (calculate rem x (divisor p x y))
          (UnsignedQuotRem.result_range bits valid rem x _ hx (divisor_range p _ x y hx hy) hn)),
        List.prefix_refl _⟩ : Out C target.H (.val .uint :: .val .uint :: .val .uint :: Γ)) := by
  cases p
  · simp only [divisor,if_true] at hn ⊢
    let reached : State C (.val .uint :: .val .uint :: Γ) :=
      ((target.setLocal i (integerValue (ty bits valid) x hx)).push (integerValue (ty bits valid) y hy)).push
        (integerValue (ty bits valid) x hx)
    have pre := assign_read_prefix_run .legacy target i a _ _ readA readI
    have tail := UnsignedQuotRemGuard.code_success bits valid reached rem .here (.there .here) x y hx hy hn rfl rfl
    unfold code
    rw [DeferredSource.join_run]
    simp only [TRun.seq,pre]
    change ((UnsignedQuotRemGuard.code rem .here (.there .here)).run reached).map (fun out => out) = _
    rw [tail]
    rfl
  · simp only [divisor,reduceCtorEq,if_false] at hn ⊢
    let reached : State C (.val .uint :: .val .uint :: Γ) :=
      ((target.setLocal i (integerValue (ty bits valid) x hx)).push (integerValue (ty bits valid) x hx)).push
        (integerValue (ty bits valid) x hx)
    have pre := assign_read_prefix_run .viaIR target i a _ _ readA readI
    have tail := UnsignedQuotRemGuard.code_success bits valid reached rem (.there .here) .here x x hx hx hn rfl rfl
    unfold code
    rw [DeferredSource.join_run]
    simp only [TRun.seq,pre]
    change ((UnsignedQuotRemGuard.code rem (.there .here) .here).run reached).map (fun out => out) = _
    rw [tail]
    rfl

theorem code_zero (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {C : Contract} {Γ : Ctx} (target : State C Γ) (p : Roadmap.Pipeline) (rem : Bool)
    (i a : Idx Γ (.val .uint)) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi) (hz : divisor p x y = 0)
    (readA : TEnv.get a target.env = integerValue (ty bits valid) x hx)
    (readI : TEnv.get i target.env = integerValue (ty bits valid) y hy) :
    (code p rem i a).run target = .error (THalt.ofData (Source.panicData .divZero)) := by
  cases p
  · simp only [divisor,if_true] at hz
    let reached : State C (.val .uint :: .val .uint :: Γ) :=
      ((target.setLocal i (integerValue (ty bits valid) x hx)).push (integerValue (ty bits valid) y hy)).push
        (integerValue (ty bits valid) x hx)
    have pre := assign_read_prefix_run .legacy target i a _ _ readA readI
    have tail := UnsignedQuotRemGuard.code_zero reached rem .here (.there .here) (integerValue (ty bits valid) y hy) rfl hz
    unfold code
    rw [DeferredSource.join_run]
    simp only [TRun.seq,pre]
    change ((UnsignedQuotRemGuard.code rem .here (.there .here)).run reached).map (fun out => out) = _
    rw [tail]
    rfl
  · simp only [divisor,reduceCtorEq,if_false] at hz
    let reached : State C (.val .uint :: .val .uint :: Γ) :=
      ((target.setLocal i (integerValue (ty bits valid) x hx)).push (integerValue (ty bits valid) x hx)).push
        (integerValue (ty bits valid) x hx)
    have pre := assign_read_prefix_run .viaIR target i a _ _ readA readI
    have tail := UnsignedQuotRemGuard.code_zero reached rem (.there .here) .here (integerValue (ty bits valid) x hx) rfl hz
    unfold code
    rw [DeferredSource.join_run]
    simp only [TRun.seq,pre]
    change ((UnsignedQuotRemGuard.code rem (.there .here) .here).run reached).map (fun out => out) = _
    rw [tail]
    rfl

theorem operand_success (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {C : Contract} {Γ : Ctx} (target : State C Γ) (p : Roadmap.Pipeline) (rem : Bool)
    (i a : Idx Γ (.val .uint)) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi) (hn : divisor p x y ≠ 0)
    (readA : TEnv.get a target.env = integerValue (ty bits valid) x hx)
    (readI : TEnv.get i target.env = integerValue (ty bits valid) y hy) :
    (operand p rem i a).run target =
      .ok (⟨target.setLocal i (integerValue (ty bits valid) x hx),List.prefix_refl _⟩,
        .prim (integerValue (ty bits valid) (calculate rem x (divisor p x y))
          (UnsignedQuotRem.result_range bits valid rem x _ hx (divisor_range p _ x y hx hy) hn))) := by
  unfold operand DeferredSource.Operand.run
  rw [code_success bits valid target p rem i a x y hx hy hn readA readI]
  cases p <;> rfl

theorem operand_zero (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {C : Contract} {Γ : Ctx} (target : State C Γ) (p : Roadmap.Pipeline) (rem : Bool)
    (i a : Idx Γ (.val .uint)) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi) (hz : divisor p x y = 0)
    (readA : TEnv.get a target.env = integerValue (ty bits valid) x hx)
    (readI : TEnv.get i target.env = integerValue (ty bits valid) y hy) :
    (operand p rem i a).run target = .error (THalt.ofData (Source.panicData .divZero)) := by
  unfold operand DeferredSource.Operand.run
  rw [code_zero bits valid target p rem i a x y hx hy hz readA readI]
  rfl

/-- The selected denominator is derived from actual Source order; all selected
postbindings come from initial alias correspondence, not a desired result. -/
theorem transport_success (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (rem : Bool)
    (si : ι → Source.Idx srcΓ (.int (ty bits valid))) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily (ty bits valid) si ti source.1 target.env) (i a : ι)
    (x y : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi) (hn : divisor G.pipeline x y ≠ 0)
    (readA : source.1.get (si a) = .int x hx) (readI : source.1.get (si i) = .int y hy) :
    (Source.evalE G F (fuel+4) (.binary (sourceOp rem) (.assign (.local (si i)) (.local (si a))) (.local (si i)))).run source =
      (.ok (.val (.int (calculate rem x (divisor G.pipeline x y))
        (UnsignedQuotRem.result_range bits valid rem x _ hx (divisor_range G.pipeline _ x y hx hy) hn))),
        (source.1.set (si i) (.int x hx),source.2)) ∧
    (operand G.pipeline rem (ti i) (ti a)).run target =
      .ok (⟨target.setLocal (ti i) (integerValue (ty bits valid) x hx),List.prefix_refl _⟩,
        .prim (integerValue (ty bits valid) (calculate rem x (divisor G.pipeline x y))
          (UnsignedQuotRem.result_range bits valid rem x _ hx (divisor_range G.pipeline _ x y hx hy) hn))) ∧
    IntValueRel (ty bits valid)
      (.int (calculate rem x (divisor G.pipeline x y))
        (UnsignedQuotRem.result_range bits valid rem x _ hx (divisor_range G.pipeline _ x y hx hy) hn) : Source.Val E.layout (.int (ty bits valid)))
      (integerValue (ty bits valid) (calculate rem x (divisor G.pipeline x y))
        (UnsignedQuotRem.result_range bits valid rem x _ hx (divisor_range G.pipeline _ x y hx hy) hn)) ∧
    IntegerLocalFamily (ty bits valid) si ti (source.1.set (si i) (.int x hx))
      (TEnv.set (ti i) (integerValue (ty bits valid) x hx) target.env) := by
  refine ⟨source_success bits valid G F fuel source rem (si i) (si a) x y hx hy hn readA readI,
    operand_success bits valid target G.pipeline rem (ti i) (ti a) x y hx hy hn
      (family.read a x hx readA) (family.read i y hy readI),integer_related _ _ _,?_⟩
  have post := family.write i a
  rw [readA,family.read a x hx readA] at post
  exact post

/-- Source retains the reached assignment state on expression failure. The
intrinsic error carries bytes but no final state; the postfamily here is the
caller immediately after its actual capture prefix, not rollback correctness. -/
theorem transport_zero (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (rem : Bool)
    (si : ι → Source.Idx srcΓ (.int (ty bits valid))) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily (ty bits valid) si ti source.1 target.env) (i a : ι)
    (x y : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi) (hz : divisor G.pipeline x y = 0)
    (readA : source.1.get (si a) = .int x hx) (readI : source.1.get (si i) = .int y hy) :
    (Source.evalE G F (fuel+4) (.binary (sourceOp rem) (.assign (.local (si i)) (.local (si a))) (.local (si i)))).run source =
      (.error (.revert (Source.panicData .divZero)),(source.1.set (si i) (.int x hx),source.2)) ∧
    (operand G.pipeline rem (ti i) (ti a)).run target = .error (THalt.ofData (Source.panicData .divZero)) ∧
    (assignReadPrefix G.pipeline (ti i) (ti a)).run target =
      .ok (⟨((target.setLocal (ti i) (integerValue (ty bits valid) x hx)).push
        (integerValue (ty bits valid) (divisor G.pipeline x y) (divisor_range G.pipeline _ x y hx hy))).push
        (integerValue (ty bits valid) x hx),List.prefix_refl _⟩) ∧
    IntegerLocalFamily (ty bits valid) si ti (source.1.set (si i) (.int x hx))
      (TEnv.set (ti i) (integerValue (ty bits valid) x hx) target.env) := by
  refine ⟨source_zero bits valid G F fuel source rem (si i) (si a) x y hx hy hz readA readI,
    operand_zero bits valid target G.pipeline rem (ti i) (ti a) x y hx hy hz
      (family.read a x hx readA) (family.read i y hy readI),
    prefix_run bits valid target G.pipeline (ti i) (ti a) x y hx hy
      (family.read a x hx readA) (family.read i y hy readI),?_⟩
  have post := family.write i a
  rw [readA,family.read a x hx readA] at post
  exact post

end Solidity.Lowering.V07.UnsignedQuotRemEffects

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffects.divisor_range' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffects.divisor_range

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffects.source_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffects.source_success

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffects.source_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffects.source_zero

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffects.prefix_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffects.prefix_run

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffects.code_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffects.code_success

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffects.code_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffects.code_zero

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffects.operand_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffects.operand_success

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffects.operand_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffects.operand_zero

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffects.transport_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffects.transport_success

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffects.transport_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffects.transport_zero
