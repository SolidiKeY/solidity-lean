import Solidity.Lowering.V07.UnsignedNarrowing
import Solidity.Lowering.V07.WordCasts

/-! G16 actual uint256-to-uintN explicit casts, with existing Source and target
values/states/evaluators. This introduces no admission or frontend producer. -/
namespace Solidity.Lowering.V07.UnsignedCasts
open UnsignedNarrowing (ty modulus_range)

theorem allowed (E : Source.Env) (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    (Source.STy.int .u256).explicit E.isBase (.int (ty bits valid)) = true := by
  simp only [Source.STy.explicit,ty,Source.IntTy.u256,BEq.beq,decide_true,Bool.true_or,Bool.or_true]

def castValue {C : Contract} {Γ : Ctx} (bits : Nat) (v : Val C Γ .uint) : Val C Γ .uint :=
  if h : bits < 256 then
    .binop .mod rfl rfl v (.simple (.lit ((2 ^ bits : Nat) : Int) (modulus_range bits h)))
  else v

theorem value_run {C : Contract} {Γ : Ctx} (target : State C Γ) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (v : Val C Γ .uint)
    (x : Int) (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi)
    (read : v.evalT target = .ok (integerValue .u256 x hx)) :
    (castValue bits v).evalT target =
      .ok (integerValue (ty bits valid) ((ty bits valid).wrap x) ((ty bits valid).wrap_mem x)) := by
  have hw := UnsignedNarrowing.wrap_of_range 256 (by decide) x hx
  have canonical : integerValue Source.IntTy.u256 x hx =
      integerValue Source.IntTy.u256 (Source.IntTy.u256.wrap x) (Source.IntTy.u256.wrap_mem x) := by
    apply Subtype.ext
    exact hw.symm
  unfold castValue
  split
  · rename_i hbits
    rw [Val.evalT,read]
    change TRes.ofOpt (BinOp.evalT .mod rfl (integerValue Source.IntTy.u256 x hx)
      (⟨((2 ^ bits : Nat) : Int),modulus_range bits hbits⟩ : PrimTy.uint.Denote)) = _
    rw [canonical,UnsignedNarrowing.mod_word_eval bits valid hbits x]
    rfl
  · have hb : bits = 256 := by omega
    subst bits
    simpa only [hw] using read

theorem source_of_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source mid : Source.EMState E Γ)
    (e : Source.RExpr E Γ (.int .u256)) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (x : Int) (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi)
    (read : (Source.evalE G F fuel e).run source = (.ok (.val (.int x hx)),mid)) :
    (Source.evalE G F (fuel+1)
      (.convExplicit (τ := .int (ty bits valid)) e (allowed E bits valid))).run source =
      (.ok (.val (Source.intWrap (ty bits valid) x)),mid) := by
  rw [Source.evalE,Source.Hoare.run_bind,read]
  rfl

theorem source_local_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (i : Source.Idx Γ (.int .u256)) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (x : Int) (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi)
    (read : source.1.get i = .int x hx) :
    (Source.evalE G F (fuel+2) (.convExplicit (τ := .int (ty bits valid))
      (.local i) (allowed E bits valid))).run source =
      (.ok (.val (Source.intWrap (ty bits valid) x)),source) := by
  apply source_of_run G F (fuel+1) source source (.local i) bits valid x hx
  change (Except.ok (Source.RVal.val (source.1.get i)),source) = _
  rw [read]

def assignedOperand {C : Contract} {Γ : Ctx} (bits : Nat) (i a : Idx Γ (.val .uint)) :
    DeferredSource.Operand C Γ (.prim .uint) :=
  ⟨_,(assignLocalOperand i a).code,.val (castValue bits (.simple (.local .here)))⟩

theorem assigned_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (i a : Idx Γ (.val .uint)) (x : Int)
    (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi)
    (read : TEnv.get a target.env = integerValue .u256 x hx) :
    (assignedOperand bits i a).run target =
      .ok (⟨target.setLocal i (integerValue .u256 x hx),List.prefix_refl _⟩,
        .prim (integerValue (ty bits valid) ((ty bits valid).wrap x) ((ty bits valid).wrap_mem x))) := by
  unfold assignedOperand DeferredSource.Operand.run assignLocalOperand
  change (do
    let x' ← (Except.ok (TEnv.get a target.env) : TRes PrimTy.uint.Denote)
    let y ← (Except.ok (TEnv.get i (TEnv.set i x' target.env)) : TRes PrimTy.uint.Denote)
    let z ← (Src.val (castValue bits (.simple (.local .here))) :
      Src C (.val .uint :: Γ) (.prim .uint)).valueT ((target.setLocal i x').push y)
    pure ((⟨target.setLocal i x',List.prefix_refl _⟩ : Out C target.H Γ),z)) = _
  rw [read]
  simp only [Bind.bind,Except.bind,TEnv.get_set]
  rw [Src.valueT,value_run ((target.setLocal i (integerValue Source.IntTy.u256 x hx)).push
    (integerValue Source.IntTy.u256 x hx)) bits valid (.simple (.local .here)) x hx rfl]
  rfl

/-- Initial-family transport for an actual effectful cast. The scalar family
continues at its original type; only the returned captured value changes width. -/
theorem assignment_transport {E : Source.Env} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} {ι : Type}
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (si : ι → Source.Idx srcΓ (.int Source.IntTy.u256)) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily Source.IntTy.u256 si ti source.1 target.env)
    (i a : ι) (x : Int) (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi)
    (readA : source.1.get (si a) = .int x hx) :
    (Source.evalE G F (fuel+3)
      (.convExplicit (τ := .int (ty bits valid))
        (.assign (.local (si i)) (.local (si a))) (allowed E bits valid))).run source =
      (.ok (.val (Source.intWrap (ty bits valid) x)),(source.1.set (si i) (.int x hx),source.2)) ∧
    (assignedOperand bits (ti i) (ti a)).run target =
      .ok (⟨target.setLocal (ti i) (integerValue Source.IntTy.u256 x hx),List.prefix_refl _⟩,
        .prim (integerValue (ty bits valid) ((ty bits valid).wrap x) ((ty bits valid).wrap_mem x))) ∧
    IntValueRel (ty bits valid) (Source.intWrap (ty bits valid) x : Source.Val E.layout (.int (ty bits valid)))
      (integerValue (ty bits valid) ((ty bits valid).wrap x) ((ty bits valid).wrap_mem x)) ∧
    IntegerLocalFamily Source.IntTy.u256 si ti (source.1.set (si i) (.int x hx))
      (TEnv.set (ti i) (integerValue Source.IntTy.u256 x hx) target.env) := by
  refine ⟨source_of_run G F (fuel+2) source _ _ bits valid x hx
    (source_assign_local_run G F fuel source (si i) (si a) _ readA),
    assigned_run target bits valid (ti i) (ti a) x hx (family.read a x hx readA),
    integer_related _ _ _,?_⟩
  have post := family.write i a
  rw [readA,family.read a x hx readA] at post
  exact post

theorem assignment_extension {C : Contract} {Γ Δ : Ctx}
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (target : State C Γ) (i a : Idx Γ (.val .uint))
    (x : Int) (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi)
    (read : TEnv.get a target.env = integerValue Source.IntTy.u256 x hx)
    (thin : Thin Γ Δ) (extra : TEnv C target.H Δ) :
    ((assignedOperand bits i a).wk thin).run (target.lift thin extra) =
      liftedT₂ thin extra (.ok ((⟨target.setLocal i (integerValue Source.IntTy.u256 x hx),List.prefix_refl _⟩ : Out C target.H Γ),
        SVal.prim (integerValue (ty bits valid) ((ty bits valid).wrap x) ((ty bits valid).wrap_mem x)))) := by
  rw [DeferredSource.Operand.run_wk,assigned_run target bits valid i a x hx read]
  rfl


end Solidity.Lowering.V07.UnsignedCasts
