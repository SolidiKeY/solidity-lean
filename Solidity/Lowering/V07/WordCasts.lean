import Solidity.Lowering.V07.DoubleAssignment
import Solidity.Lowering.V07.Conversions

/-! Actual full-word sign conversions. These use the published Source cast and
intrinsic conversion operators, with no new evaluator or source-admission claim. -/
namespace Solidity.Lowering.V07.WordCasts

def signed : Source.IntTy := ⟨true,256,by decide⟩

theorem signed_wrap (x : Int) (hx : 0 ≤ x ∧ x < Semantics.uintBound) :
    signed.wrap x = (if x < Semantics.intBound then x else x - Semantics.uintBound) := by
  unfold Semantics.uintBound at hx
  simp only [signed,Source.IntTy.wrap,Source.wrapBits,Source.bitsHi,true_and,if_true]
  rw [Int.emod_eq_of_lt hx.1 hx.2]
  unfold Semantics.intBound Semantics.uintBound
  split <;> split <;> omega

theorem to_int_eval (x : Int) (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi) :
    UnOp.evalT .toInt rfl (integerValue Source.IntTy.u256 x hx) =
      some (integerValue signed (signed.wrap x) (signed.wrap_mem x)) := by
  have hr := integer_range Source.IntTy.u256 x hx
  have canonical : 0 ≤ x ∧ x < Semantics.uintBound := of_decide_eq_true hr
  have outRange := integer_range signed (signed.wrap x) (signed.wrap_mem x)
  change PrimTy.int.inRange (signed.wrap x) = true at outRange
  change PrimTy.int.ofInt? (if x < Semantics.intBound then x else x-Semantics.uintBound) =
    some ⟨signed.wrap x,outRange⟩
  rw [← signed_wrap x canonical]
  simp only [PrimTy.ofInt?,dif_pos outRange]

theorem to_uint_eval (x : Int) (hx : signed.lo ≤ x ∧ x ≤ signed.hi) :
    UnOp.evalT .toUint rfl (integerValue signed x hx) =
      some (integerValue Source.IntTy.u256 (Source.IntTy.u256.wrap x) (Source.IntTy.u256.wrap_mem x)) := by
  have hr := integer_range Source.IntTy.u256 (Source.IntTy.u256.wrap x) (Source.IntTy.u256.wrap_mem x)
  change PrimTy.uint.inRange (x % Semantics.uintBound) = true at hr
  change PrimTy.uint.ofInt? (x % Semantics.uintBound) = some ⟨x % Semantics.uintBound,hr⟩
  simp only [PrimTy.ofInt?,dif_pos hr]

theorem to_int_run {C : Contract} {Γ : Ctx} (s : State C Γ) (v : Val C Γ .uint)
    (x : Int) (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi)
    (read : v.evalT s = .ok (integerValue Source.IntTy.u256 x hx)) :
    (Val.unop .toInt rfl rfl v).evalT s =
      .ok (integerValue signed (signed.wrap x) (signed.wrap_mem x)) := by
  rw [Val.evalT,read]
  change TRes.ofOpt (UnOp.evalT .toInt rfl (integerValue Source.IntTy.u256 x hx)) = _
  rw [to_int_eval]
  rfl

theorem to_uint_run {C : Contract} {Γ : Ctx} (s : State C Γ) (v : Val C Γ .int)
    (x : Int) (hx : signed.lo ≤ x ∧ x ≤ signed.hi)
    (read : v.evalT s = .ok (integerValue signed x hx)) :
    (Val.unop .toUint rfl rfl v).evalT s =
      .ok (integerValue Source.IntTy.u256 (Source.IntTy.u256.wrap x) (Source.IntTy.u256.wrap_mem x)) := by
  rw [Val.evalT,read]
  change TRes.ofOpt (UnOp.evalT .toUint rfl (integerValue signed x hx)) = _
  rw [to_uint_eval]
  rfl

theorem source_to_int {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (s mid : Source.EMState E Γ) (e : Source.RExpr E Γ (.int .u256))
    (x : Int) (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi)
    (read : (Source.evalE G F fuel e).run s = (.ok (.val (.int x hx)),mid)) :
    (Source.evalE G F (fuel+1) (.convExplicit (τ := .int signed) e (by rfl))).run s =
      (.ok (.val (Source.intWrap signed x)),mid) := by
  rw [Source.evalE,Source.Hoare.run_bind,read]
  rfl

theorem source_to_uint {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (s mid : Source.EMState E Γ) (e : Source.RExpr E Γ (.int signed))
    (x : Int) (hx : signed.lo ≤ x ∧ x ≤ signed.hi)
    (read : (Source.evalE G F fuel e).run s = (.ok (.val (.int x hx)),mid)) :
    (Source.evalE G F (fuel+1) (.convExplicit (τ := .int .u256) e (by rfl))).run s =
      (.ok (.val (Source.intWrap .u256 x)),mid) := by
  rw [Source.evalE,Source.Hoare.run_bind,read]
  rfl

/-- Reuse the actual local-assignment/capture prefix; convert the capture
while its fresh typed binder still exists. -/
def assignedToInt {C : Contract} {Γ : Ctx} (i a : Idx Γ (.val .uint)) :
    DeferredSource.Operand C Γ (.prim .int) :=
  ⟨_,(assignLocalOperand i a).code,.val (.unop .toInt rfl rfl (.simple (.local .here)))⟩

def assignedToUint {C : Contract} {Γ : Ctx} (i a : Idx Γ (.val .int)) :
    DeferredSource.Operand C Γ (.prim .uint) :=
  ⟨_,(assignLocalOperand i a).code,.val (.unop .toUint rfl rfl (.simple (.local .here)))⟩

theorem assigned_to_int_run {C : Contract} {Γ : Ctx} (s : State C Γ)
    (i a : Idx Γ (.val .uint)) (x : Int)
    (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi)
    (read : TEnv.get a s.env = integerValue Source.IntTy.u256 x hx) :
    (assignedToInt i a).run s =
      .ok (⟨s.setLocal i (integerValue Source.IntTy.u256 x hx),List.prefix_refl _⟩,
        .prim (integerValue signed (signed.wrap x) (signed.wrap_mem x))) := by
  unfold assignedToInt DeferredSource.Operand.run assignLocalOperand
  change (do
    let x' ← (Except.ok (TEnv.get a s.env) : TRes PrimTy.uint.Denote)
    let y ← (Except.ok (TEnv.get i (TEnv.set i x' s.env)) : TRes PrimTy.uint.Denote)
    let z ← (Src.val (.unop .toInt rfl rfl (.simple (.local .here))) :
      Src C (.val .uint :: Γ) (.prim .int)).valueT ((s.setLocal i x').push y)
    pure ((⟨s.setLocal i x',List.prefix_refl _⟩ : Out C s.H Γ),z)) = _
  rw [read]
  simp only [Bind.bind,Except.bind,TEnv.get_set]
  rw [Src.valueT,to_int_run ((s.setLocal i (integerValue Source.IntTy.u256 x hx)).push (integerValue Source.IntTy.u256 x hx))
    (.simple (.local .here)) x hx rfl]
  rfl

theorem assigned_to_uint_run {C : Contract} {Γ : Ctx} (s : State C Γ)
    (i a : Idx Γ (.val .int)) (x : Int) (hx : signed.lo ≤ x ∧ x ≤ signed.hi)
    (read : TEnv.get a s.env = integerValue signed x hx) :
    (assignedToUint i a).run s =
      .ok (⟨s.setLocal i (integerValue signed x hx),List.prefix_refl _⟩,
        .prim (integerValue Source.IntTy.u256 (Source.IntTy.u256.wrap x) (Source.IntTy.u256.wrap_mem x))) := by
  unfold assignedToUint DeferredSource.Operand.run assignLocalOperand
  change (do
    let x' ← (Except.ok (TEnv.get a s.env) : TRes PrimTy.int.Denote)
    let y ← (Except.ok (TEnv.get i (TEnv.set i x' s.env)) : TRes PrimTy.int.Denote)
    let z ← (Src.val (.unop .toUint rfl rfl (.simple (.local .here))) :
      Src C (.val .int :: Γ) (.prim .uint)).valueT ((s.setLocal i x').push y)
    pure ((⟨s.setLocal i x',List.prefix_refl _⟩ : Out C s.H Γ),z)) = _
  rw [read]
  simp only [Bind.bind,Except.bind,TEnv.get_set]
  rw [Src.valueT,to_uint_run ((s.setLocal i (integerValue signed x hx)).push (integerValue signed x hx))
    (.simple (.local .here)) x hx rfl]
  rfl


/-- Initial-family transport for an actual effectful cast. The scalar family
continues at its original type; only the returned captured value changes sign. -/
theorem assignment_to_int_transport {E : Source.Env} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (si : ι → Source.Idx srcΓ (.int Source.IntTy.u256)) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily Source.IntTy.u256 si ti source.1 target.env)
    (i a : ι) (x : Int) (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi)
    (readA : source.1.get (si a) = .int x hx) :
    (Source.evalE G F (fuel+3)
      (.convExplicit (τ := .int signed)
        (.assign (.local (si i)) (.local (si a))) (by rfl))).run source =
      (.ok (.val (Source.intWrap signed x)),(source.1.set (si i) (.int x hx),source.2)) ∧
    (assignedToInt (ti i) (ti a)).run target =
      .ok (⟨target.setLocal (ti i) (integerValue Source.IntTy.u256 x hx),List.prefix_refl _⟩,
        .prim (integerValue signed (signed.wrap x) (signed.wrap_mem x))) ∧
    IntValueRel signed (Source.intWrap signed x : Source.Val E.layout (.int signed))
      (integerValue signed (signed.wrap x) (signed.wrap_mem x)) ∧
    IntegerLocalFamily Source.IntTy.u256 si ti (source.1.set (si i) (.int x hx))
      (TEnv.set (ti i) (integerValue Source.IntTy.u256 x hx) target.env) := by
  refine ⟨source_to_int G F (fuel+2) source _ _ x hx
    (source_assign_local_run G F fuel source (si i) (si a) _ readA),
    assigned_to_int_run target (ti i) (ti a) x hx (family.read a x hx readA),
    integer_related _ _ _,?_⟩
  have post := family.write i a
  rw [readA,family.read a x hx readA] at post
  exact post

theorem assigned_to_int_extension {C : Contract} {Γ Δ : Ctx}
    (target : State C Γ) (i a : Idx Γ (.val .uint))
    (x : Int) (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi)
    (read : TEnv.get a target.env = integerValue Source.IntTy.u256 x hx)
    (thin : Thin Γ Δ) (extra : TEnv C target.H Δ) :
    ((assignedToInt i a).wk thin).run (target.lift thin extra) =
      liftedT₂ thin extra (.ok ((⟨target.setLocal i (integerValue Source.IntTy.u256 x hx),List.prefix_refl _⟩ : Out C target.H Γ),
        SVal.prim (integerValue signed (signed.wrap x) (signed.wrap_mem x)))) := by
  rw [DeferredSource.Operand.run_wk,assigned_to_int_run target i a x hx read]
  rfl

/-- Initial-family transport for an actual effectful cast. The scalar family
continues at its original type; only the returned captured value changes sign. -/
theorem assignment_to_uint_transport {E : Source.Env} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (si : ι → Source.Idx srcΓ (.int signed)) (ti : ι → Idx Γ (.val .int))
    (family : IntegerLocalFamily signed si ti source.1 target.env)
    (i a : ι) (x : Int) (hx : signed.lo ≤ x ∧ x ≤ signed.hi)
    (readA : source.1.get (si a) = .int x hx) :
    (Source.evalE G F (fuel+3)
      (.convExplicit (τ := .int Source.IntTy.u256)
        (.assign (.local (si i)) (.local (si a))) (by rfl))).run source =
      (.ok (.val (Source.intWrap Source.IntTy.u256 x)),(source.1.set (si i) (.int x hx),source.2)) ∧
    (assignedToUint (ti i) (ti a)).run target =
      .ok (⟨target.setLocal (ti i) (integerValue signed x hx),List.prefix_refl _⟩,
        .prim (integerValue Source.IntTy.u256 (Source.IntTy.u256.wrap x) (Source.IntTy.u256.wrap_mem x))) ∧
    IntValueRel Source.IntTy.u256 (Source.intWrap Source.IntTy.u256 x : Source.Val E.layout (.int Source.IntTy.u256))
      (integerValue Source.IntTy.u256 (Source.IntTy.u256.wrap x) (Source.IntTy.u256.wrap_mem x)) ∧
    IntegerLocalFamily signed si ti (source.1.set (si i) (.int x hx))
      (TEnv.set (ti i) (integerValue signed x hx) target.env) := by
  refine ⟨source_to_uint G F (fuel+2) source _ _ x hx
    (source_assign_local_run G F fuel source (si i) (si a) _ readA),
    assigned_to_uint_run target (ti i) (ti a) x hx (family.read a x hx readA),
    integer_related _ _ _,?_⟩
  have post := family.write i a
  rw [readA,family.read a x hx readA] at post
  exact post

theorem assigned_to_uint_extension {C : Contract} {Γ Δ : Ctx}
    (target : State C Γ) (i a : Idx Γ (.val .int))
    (x : Int) (hx : signed.lo ≤ x ∧ x ≤ signed.hi)
    (read : TEnv.get a target.env = integerValue signed x hx)
    (thin : Thin Γ Δ) (extra : TEnv C target.H Δ) :
    ((assignedToUint i a).wk thin).run (target.lift thin extra) =
      liftedT₂ thin extra (.ok ((⟨target.setLocal i (integerValue signed x hx),List.prefix_refl _⟩ : Out C target.H Γ),
        SVal.prim (integerValue Source.IntTy.u256 (Source.IntTy.u256.wrap x) (Source.IntTy.u256.wrap_mem x)))) := by
  rw [DeferredSource.Operand.run_wk,assigned_to_uint_run target i a x hx read]
  rfl

end Solidity.Lowering.V07.WordCasts
