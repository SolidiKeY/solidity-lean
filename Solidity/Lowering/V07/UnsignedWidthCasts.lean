import Solidity.Lowering.V07.UnsignedCasts

/-! G16 actual uintM-to-uintN explicit casts, with existing Source and target
values/states/evaluators. This introduces no admission or frontend producer. -/
namespace Solidity.Lowering.V07.UnsignedWidthCasts
open UnsignedNarrowing (ty)
open UnsignedCasts (castValue assignedOperand)

theorem word_range (fromBits : Nat)
    (fromValid : fromBits % 8 = 0 ∧ 8 ≤ fromBits ∧ fromBits ≤ 256)
    (x : Int) (hx : (ty fromBits fromValid).lo ≤ x ∧ x ≤ (ty fromBits fromValid).hi) :
    Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi := by
  apply implicit_integer_range (ty fromBits fromValid) Source.IntTy.u256 _ x hx
  change (decide (fromBits ≤ 256) || false) = true
  simp only [Bool.or_false,decide_eq_true_eq]
  exact fromValid.2.2

theorem allowed (fromBits : Nat) (fromValid : fromBits % 8 = 0 ∧ 8 ≤ fromBits ∧ fromBits ≤ 256) (E : Source.Env) (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    (Source.STy.int (ty fromBits fromValid)).explicit E.isBase (.int (ty bits valid)) = true := by
  simp only [Source.STy.explicit,ty,BEq.beq,decide_true,Bool.true_or,Bool.or_true]

theorem value_run (fromBits : Nat) (fromValid : fromBits % 8 = 0 ∧ 8 ≤ fromBits ∧ fromBits ≤ 256) {C : Contract} {Γ : Ctx} (target : State C Γ) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (v : Val C Γ .uint)
    (x : Int) (hx : (ty fromBits fromValid).lo ≤ x ∧ x ≤ (ty fromBits fromValid).hi)
    (read : v.evalT target = .ok (integerValue (ty fromBits fromValid) x hx)) :
    (castValue bits v).evalT target =
      .ok (integerValue (ty bits valid) ((ty bits valid).wrap x) ((ty bits valid).wrap_mem x)) := by
  exact UnsignedCasts.value_run target bits valid v x (word_range fromBits fromValid x hx) read

theorem source_of_run (fromBits : Nat) (fromValid : fromBits % 8 = 0 ∧ 8 ≤ fromBits ∧ fromBits ≤ 256) {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source mid : Source.EMState E Γ)
    (e : Source.RExpr E Γ (.int (ty fromBits fromValid))) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (x : Int) (hx : (ty fromBits fromValid).lo ≤ x ∧ x ≤ (ty fromBits fromValid).hi)
    (read : (Source.evalE G F fuel e).run source = (.ok (.val (.int x hx)),mid)) :
    (Source.evalE G F (fuel+1)
      (.convExplicit (τ := .int (ty bits valid)) e (allowed fromBits fromValid E bits valid))).run source =
      (.ok (.val (Source.intWrap (ty bits valid) x)),mid) := by
  rw [Source.evalE,Source.Hoare.run_bind,read]
  rfl

theorem source_local_run (fromBits : Nat) (fromValid : fromBits % 8 = 0 ∧ 8 ≤ fromBits ∧ fromBits ≤ 256) {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (i : Source.Idx Γ (.int (ty fromBits fromValid))) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (x : Int) (hx : (ty fromBits fromValid).lo ≤ x ∧ x ≤ (ty fromBits fromValid).hi)
    (read : source.1.get i = .int x hx) :
    (Source.evalE G F (fuel+2) (.convExplicit (τ := .int (ty bits valid))
      (.local i) (allowed fromBits fromValid E bits valid))).run source =
      (.ok (.val (Source.intWrap (ty bits valid) x)),source) := by
  apply source_of_run fromBits fromValid G F (fuel+1) source source (.local i) bits valid x hx
  change (Except.ok (Source.RVal.val (source.1.get i)),source) = _
  rw [read]

theorem assigned_run (fromBits : Nat) (fromValid : fromBits % 8 = 0 ∧ 8 ≤ fromBits ∧ fromBits ≤ 256) {C : Contract} {Γ : Ctx} (target : State C Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (i a : Idx Γ (.val .uint)) (x : Int)
    (hx : (ty fromBits fromValid).lo ≤ x ∧ x ≤ (ty fromBits fromValid).hi)
    (read : TEnv.get a target.env = integerValue (ty fromBits fromValid) x hx) :
    (assignedOperand bits i a).run target =
      .ok (⟨target.setLocal i (integerValue (ty fromBits fromValid) x hx),List.prefix_refl _⟩,
        .prim (integerValue (ty bits valid) ((ty bits valid).wrap x) ((ty bits valid).wrap_mem x))) := by
  exact UnsignedCasts.assigned_run target bits valid i a x (word_range fromBits fromValid x hx) read

/-- Initial-family transport for an actual effectful cast. The scalar family
continues at its original type; only the returned captured value changes width. -/
theorem assignment_transport (fromBits : Nat) (fromValid : fromBits % 8 = 0 ∧ 8 ≤ fromBits ∧ fromBits ≤ 256) {E : Source.Env} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} {ι : Type}
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (si : ι → Source.Idx srcΓ (.int (ty fromBits fromValid))) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily (ty fromBits fromValid) si ti source.1 target.env)
    (i a : ι) (x : Int) (hx : (ty fromBits fromValid).lo ≤ x ∧ x ≤ (ty fromBits fromValid).hi)
    (readA : source.1.get (si a) = .int x hx) :
    (Source.evalE G F (fuel+3)
      (.convExplicit (τ := .int (ty bits valid))
        (.assign (.local (si i)) (.local (si a))) (allowed fromBits fromValid E bits valid))).run source =
      (.ok (.val (Source.intWrap (ty bits valid) x)),(source.1.set (si i) (.int x hx),source.2)) ∧
    (assignedOperand bits (ti i) (ti a)).run target =
      .ok (⟨target.setLocal (ti i) (integerValue (ty fromBits fromValid) x hx),List.prefix_refl _⟩,
        .prim (integerValue (ty bits valid) ((ty bits valid).wrap x) ((ty bits valid).wrap_mem x))) ∧
    IntValueRel (ty bits valid) (Source.intWrap (ty bits valid) x : Source.Val E.layout (.int (ty bits valid)))
      (integerValue (ty bits valid) ((ty bits valid).wrap x) ((ty bits valid).wrap_mem x)) ∧
    IntegerLocalFamily (ty fromBits fromValid) si ti (source.1.set (si i) (.int x hx))
      (TEnv.set (ti i) (integerValue (ty fromBits fromValid) x hx) target.env) := by
  refine ⟨source_of_run fromBits fromValid G F (fuel+2) source _ _ bits valid x hx
    (source_assign_local_run G F fuel source (si i) (si a) _ readA),
    assigned_run fromBits fromValid target bits valid (ti i) (ti a) x hx (family.read a x hx readA),
    integer_related _ _ _,?_⟩
  have post := family.write i a
  rw [readA,family.read a x hx readA] at post
  exact post

theorem assignment_extension (fromBits : Nat) (fromValid : fromBits % 8 = 0 ∧ 8 ≤ fromBits ∧ fromBits ≤ 256) {C : Contract} {Γ Δ : Ctx}
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (target : State C Γ) (i a : Idx Γ (.val .uint))
    (x : Int) (hx : (ty fromBits fromValid).lo ≤ x ∧ x ≤ (ty fromBits fromValid).hi)
    (read : TEnv.get a target.env = integerValue (ty fromBits fromValid) x hx)
    (thin : Thin Γ Δ) (extra : TEnv C target.H Δ) :
    ((assignedOperand bits i a).wk thin).run (target.lift thin extra) =
      liftedT₂ thin extra (.ok ((⟨target.setLocal i (integerValue (ty fromBits fromValid) x hx),List.prefix_refl _⟩ : Out C target.H Γ),
        SVal.prim (integerValue (ty bits valid) ((ty bits valid).wrap x) ((ty bits valid).wrap_mem x)))) := by
  rw [DeferredSource.Operand.run_wk,assigned_run fromBits fromValid target bits valid i a x hx read]
  rfl

end Solidity.Lowering.V07.UnsignedWidthCasts
