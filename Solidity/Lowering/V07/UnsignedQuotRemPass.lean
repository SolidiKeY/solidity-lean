import Solidity.Lowering.V07.UnsignedQuotRemEffects
/-! Exact action of the published panic insertion pass on the supported typed
quotient/remainder clauses. These equalities connect existing operational
transport laws to `Prog.withPanics`; they do not assert frontend selection. -/
namespace Solidity.Lowering.V07.UnsignedQuotRemPass
open UnsignedNarrowing (ty)
open UnsignedQuotRem (calculate sourceOp)
open UnsignedQuotRemEffects (divisor divisor_range)

def raw {C : Contract} {Γ : Ctx} (rem : Bool) (a b : Idx Γ (.val .uint)) :
    Prog C Γ (.val .uint :: Γ) :=
  .cons (.declLocal .uint (.user "v07_quotrem_result")
    (some (UnsignedQuotRem.value rem (.simple (.local a)) (.simple (.local b))))) .nil

theorem pure_exact {C : Contract} {Γ : Ctx} (rem : Bool) (a b : Idx Γ (.val .uint)) :
    (raw (C := C) rem a b).withPanics = UnsignedQuotRemGuard.code rem a b := by
  cases rem <;> rfl

def rawEffects {C : Contract} {Γ : Ctx} (p : Roadmap.Pipeline) (rem : Bool)
    (i a : Idx Γ (.val .uint)) : Prog C Γ (.val .uint :: .val .uint :: .val .uint :: Γ) :=
  match p with
  | .legacy => (assignReadPrefix p i a).join (raw rem .here (.there .here))
  | .viaIR => (assignReadPrefix p i a).join (raw rem (.there .here) .here)

theorem effects_exact {C : Contract} {Γ : Ctx} (p : Roadmap.Pipeline) (rem : Bool)
    (i a : Idx Γ (.val .uint)) :
    (rawEffects (C := C) p rem i a).withPanics = UnsignedQuotRemEffects.code p rem i a := by
  cases p <;> cases rem <;> rfl

def pureOperand {C : Contract} {Γ : Ctx} (rem : Bool) (a b : Idx Γ (.val .uint)) :
    DeferredSource.Operand C Γ (.prim .uint) :=
  ⟨_,(raw rem a b).withPanics,.val (.simple (.local .here))⟩
def effectsOperand {C : Contract} {Γ : Ctx} (p : Roadmap.Pipeline) (rem : Bool)
    (i a : Idx Γ (.val .uint)) : DeferredSource.Operand C Γ (.prim .uint) :=
  ⟨_,(rawEffects p rem i a).withPanics,.val (.simple (.local .here))⟩

theorem pure_operand_exact {C : Contract} {Γ : Ctx} (rem : Bool) (a b : Idx Γ (.val .uint)) :
    pureOperand (C := C) rem a b = UnsignedQuotRemGuard.operand rem a b := by
  simp only [pureOperand,pure_exact,UnsignedQuotRemGuard.operand]

theorem effects_operand_exact {C : Contract} {Γ : Ctx} (p : Roadmap.Pipeline) (rem : Bool)
    (i a : Idx Γ (.val .uint)) :
    effectsOperand (C := C) p rem i a = UnsignedQuotRemEffects.operand p rem i a := by
  simp only [effectsOperand,effects_exact,UnsignedQuotRemEffects.operand]

theorem pure_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (rem : Bool) (a b : Idx Γ (.val .uint)) :
    ((raw rem a b).withPanics).run target = (UnsignedQuotRemGuard.code rem a b).run target := by
  simp only [pure_exact]

theorem effects_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (p : Roadmap.Pipeline) (rem : Bool) (i a : Idx Γ (.val .uint)) :
    ((rawEffects p rem i a).withPanics).run target = (UnsignedQuotRemEffects.code p rem i a).run target := by
  simp only [effects_exact]

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
    (effectsOperand G.pipeline rem (ti i) (ti a)).run target =
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
  simp only [effects_operand_exact]
  exact UnsignedQuotRemEffects.transport_success bits valid G F fuel source target rem si ti family i a x y hx hy hn readA readI

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
    (effectsOperand G.pipeline rem (ti i) (ti a)).run target = .error (THalt.ofData (Source.panicData .divZero)) ∧
    (assignReadPrefix G.pipeline (ti i) (ti a)).run target =
      .ok (⟨((target.setLocal (ti i) (integerValue (ty bits valid) x hx)).push
        (integerValue (ty bits valid) (divisor G.pipeline x y) (divisor_range G.pipeline _ x y hx hy))).push
        (integerValue (ty bits valid) x hx),List.prefix_refl _⟩) ∧
    IntegerLocalFamily (ty bits valid) si ti (source.1.set (si i) (.int x hx))
      (TEnv.set (ti i) (integerValue (ty bits valid) x hx) target.env) := by
  simp only [effects_operand_exact]
  exact UnsignedQuotRemEffects.transport_zero bits valid G F fuel source target rem si ti family i a x y hx hy hz readA readI

end Solidity.Lowering.V07.UnsignedQuotRemPass

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemPass.pure_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemPass.pure_exact

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemPass.effects_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemPass.effects_exact

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemPass.pure_operand_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemPass.pure_operand_exact

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemPass.effects_operand_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemPass.effects_operand_exact

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemPass.pure_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemPass.pure_run

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemPass.effects_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemPass.effects_run

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemPass.transport_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemPass.transport_success

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemPass.transport_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemPass.transport_zero
