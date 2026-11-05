import Solidity.Lowering.V07.SignedWordSubtraction
import Solidity.Lowering.V07.UnsignedMultiplication

/-! Actual unchecked int256 multiplication via existing casts and word operators.
Shared signed wrapping laws are reused, without a new representation, evaluator
or Backend.Scalar opcode compiler. Narrower signed widths remain open. -/
namespace Solidity.Lowering.V07.SignedWordMultiplication
open SignedWordSubtraction (ty wrap_of_range wrap_word)

theorem unsigned_mul_wrap (x y : Int) :
    Source.IntTy.u256.wrap (Source.IntTy.u256.wrap x*Source.IntTy.u256.wrap y) =
      Source.IntTy.u256.wrap (x*y) := by
  change ((x % Semantics.uintBound)*(y % Semantics.uintBound)) % Semantics.uintBound =
    (x*y) % Semantics.uintBound
  exact (Int.mul_emod x y Semantics.uintBound).symm

def mulValue {C : Contract} {Γ : Ctx} (a b : Val C Γ .int) : Val C Γ .int :=
  .unop .toInt rfl rfl (UnsignedMultiplication.mulValue 256
    (.unop .toUint rfl rfl a) (.unop .toUint rfl rfl b))

theorem source_mul_unchecked {D : Source.Layout} (x y : Int)
    (hx : ty.lo ≤ x ∧ x ≤ ty.hi) (hy : ty.lo ≤ y ∧ y ≤ ty.hi) :
    Source.binVal false .mul (.int x hx : Source.Val D (.int ty)) (.int y hy) =
      .ok (Source.intWrap ty (x*y)) := by
  simp only [Source.binVal,Source.intBin,Source.intRes]
  split
  · rename_i h
    have hw := wrap_of_range (x*y) h
    simp only [Source.intWrap,hw]
    rfl
  · rfl

theorem mul_value_run {C : Contract} {Γ : Ctx} (target : State C Γ) (a b : Val C Γ .int)
    (x y : Int) (hx : ty.lo ≤ x ∧ x ≤ ty.hi) (hy : ty.lo ≤ y ∧ y ≤ ty.hi)
    (left : a.evalT target = .ok (integerValue ty x hx))
    (right : b.evalT target = .ok (integerValue ty y hy)) :
    (mulValue a b).evalT target =
      .ok (integerValue ty (ty.wrap (x*y)) (ty.wrap_mem (x*y))) := by
  have first := WordCasts.to_uint_run target a x hx left
  have second := WordCasts.to_uint_run target b y hy right
  have raw := UnsignedMultiplication.mul_value_run target 256 (by decide)
    (.unop .toUint rfl rfl a) (.unop .toUint rfl rfl b)
    (Source.IntTy.u256.wrap x) (Source.IntTy.u256.wrap y)
    (Source.IntTy.u256.wrap_mem x) (Source.IntTy.u256.wrap_mem y) first second
  have result := WordCasts.to_int_run target _ _
    (Source.IntTy.u256.wrap_mem (Source.IntTy.u256.wrap x*Source.IntTy.u256.wrap y)) raw
  simpa only [mulValue,unsigned_mul_wrap,wrap_word] using result

theorem source_from_pair {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source mid : Source.EMState E Γ)
    (a b : Source.RExpr E Γ (.int ty)) (x y : Int)
    (hx : ty.lo ≤ x ∧ x ≤ ty.hi)
    (hy : ty.lo ≤ y ∧ y ≤ ty.hi)
    (pair : (Source.evalPair G {F with checked := false} fuel a b).run source =
      (.ok (.val (.int x hx),.val (.int y hy)),mid)) :
    (Source.evalE G {F with checked := false} (fuel+1) (.binary .mul a b)).run source =
      (.ok (.val (Source.intWrap ty (x*y))),mid) := by
  rw [Source.evalE]
  simp only [reduceCtorEq,decide_false,Bool.false_or,Bool.false_eq_true,if_false]
  rw [Source.Hoare.run_bind,pair]
  change (do
    let v ← Source.EM.lift (Source.binVal false .mul
      (.int x hx : Source.Val E.layout (.int ty)) (.int y hy))
    pure (Source.RVal.val v)).run mid = _
  rw [source_mul_unchecked]
  rfl

theorem source_locals_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (a b : Source.Idx Γ (.int ty)) (x y : Int)
    (hx : ty.lo ≤ x ∧ x ≤ ty.hi)
    (hy : ty.lo ≤ y ∧ y ≤ ty.hi)
    (readA : source.1.get a = .int x hx) (readB : source.1.get b = .int y hy) :
    (Source.evalE G {F with checked := false} (fuel+3)
      (.binary .mul (.local a) (.local b))).run source =
      (.ok (.val (Source.intWrap ty (x*y))),source) :=
  source_from_pair G F (fuel+2) source source _ _ x y hx hy
    (source_local_pair G {F with checked := false} fuel source ty a b x y hx hy readA readB)

theorem locals_transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (si : ι → Source.Idx srcΓ (.int ty)) (ti : ι → Idx Γ (.val .int))
    (family : IntegerLocalFamily ty si ti source.1 target.env)
    (a b : ι) (x y : Int)
    (hx : ty.lo ≤ x ∧ x ≤ ty.hi)
    (hy : ty.lo ≤ y ∧ y ≤ ty.hi)
    (readA : source.1.get (si a) = .int x hx) (readB : source.1.get (si b) = .int y hy) :
    (Source.evalE G {F with checked := false} (fuel+3)
      (.binary .mul (.local (si a)) (.local (si b)))).run source =
      (.ok (.val (Source.intWrap ty (x*y))),source) ∧
    (mulValue (.simple (.local (ti a))) (.simple (.local (ti b)))).evalT target =
      .ok (integerValue ty (ty.wrap (x*y)) (ty.wrap_mem (x*y))) ∧
    IntValueRel ty (Source.intWrap ty (x*y) : Source.Val E.layout (.int ty))
      (integerValue ty (ty.wrap (x*y)) (ty.wrap_mem (x*y))) := by
  refine ⟨source_locals_run G F fuel source (si a) (si b) x y hx hy readA readB,
    mul_value_run target _ _ x y hx hy ?_ ?_,integer_related _ _ _⟩
  · change Except.ok (TEnv.get (ti a) target.env) = _
    rw [family.read a x hx readA]
  · change Except.ok (TEnv.get (ti b) target.env) = _
    rw [family.read b y hy readB]

/-- Actual effectful assignment/read expression; result bounds come from
Source wrapping, never a desired-result range premise. -/
theorem source_assign_read_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (i a : Source.Idx Γ (.int ty)) (x y : Int)
    (hx : ty.lo ≤ x ∧ x ≤ ty.hi)
    (hy : ty.lo ≤ y ∧ y ≤ ty.hi)
    (readA : source.1.get a = .int x hx) (readI : source.1.get i = .int y hy) :
    (Source.evalE G {F with checked := false} (fuel+4)
      (.binary .mul (.assign (.local i) (.local a)) (.local i))).run source =
      (.ok (.val (Source.intWrap ty (x*(if G.pipeline = .legacy then y else x)))),
        (source.1.set i (.int x hx),source.2)) := by
  have pair := source_assign_read_pair G {F with checked := false} fuel source i a
    (.int x hx) (.int y hy) readA readI
  by_cases order : G.pipeline = .legacy
  · simp only [order,if_true] at pair ⊢
    exact source_from_pair G F (fuel+3) source _ _ _ x y hx hy pair
  · simp only [order,if_false] at pair ⊢
    exact source_from_pair G F (fuel+3) source _ _ _ x x hx hx pair

def assignReadOperand {C : Contract} {Γ : Ctx} (pipeline : Roadmap.Pipeline)
    (i a : Idx Γ (.val .int)) : DeferredSource.Operand C Γ (.prim .int) :=
  ⟨.val .int :: .val .int :: Γ,assignReadPrefix pipeline i a,
    match pipeline with
    | .legacy => .val (mulValue (.simple (.local .here)) (.simple (.local (.there .here))))
    | .viaIR => .val (mulValue (.simple (.local (.there .here))) (.simple (.local .here)))⟩

theorem assign_read_operand_run {C : Contract} {Γ : Ctx} (pipeline : Roadmap.Pipeline)
    (target : State C Γ)
    (i a : Idx Γ (.val .int)) (x y : Int)
    (hx : ty.lo ≤ x ∧ x ≤ ty.hi)
    (hy : ty.lo ≤ y ∧ y ≤ ty.hi)
    (readA : TEnv.get a target.env = integerValue ty x hx)
    (readI : TEnv.get i target.env = integerValue ty y hy) :
    (assignReadOperand pipeline i a).run target =
      .ok (⟨target.setLocal i (integerValue ty x hx),List.prefix_refl _⟩,
        .prim (integerValue ty (ty.wrap (x*(if pipeline = .legacy then y else x)))
          (ty.wrap_mem (x*(if pipeline = .legacy then y else x))))) := by
  cases pipeline
  · let reached : State C (.val .int :: .val .int :: Γ) :=
      ((target.setLocal i (integerValue ty x hx)).push (integerValue ty y hy)).push
        (integerValue ty x hx)
    have value := mul_value_run reached (.simple (.local .here))
      (.simple (.local (.there .here))) x y hx hy rfl rfl
    unfold assignReadOperand DeferredSource.Operand.run
    rw [assign_read_prefix_run .legacy target i a _ _ readA readI]
    change (do
      let v ← (Src.val (mulValue (.simple (.local .here)) (.simple (.local (.there .here)))) :
        Src C (.val .int :: .val .int :: Γ) (.prim .int)).valueT reached
      pure ((⟨target.setLocal i (integerValue ty x hx),List.prefix_refl _⟩ : Out C target.H Γ),v)) = _
    simp only [Src.valueT,value]
    rfl
  · let reached : State C (.val .int :: .val .int :: Γ) :=
      ((target.setLocal i (integerValue ty x hx)).push (integerValue ty x hx)).push
        (integerValue ty x hx)
    have value := mul_value_run reached (.simple (.local (.there .here)))
      (.simple (.local .here)) x x hx hx rfl rfl
    unfold assignReadOperand DeferredSource.Operand.run
    rw [assign_read_prefix_run .viaIR target i a _ _ readA readI]
    change (do
      let v ← (Src.val (mulValue (.simple (.local (.there .here))) (.simple (.local .here))) :
        Src C (.val .int :: .val .int :: Γ) (.prim .int)).valueT reached
      pure ((⟨target.setLocal i (integerValue ty x hx),List.prefix_refl _⟩ : Out C target.H Γ),v)) = _
    simp only [Src.valueT,value]
    rfl

/-- Initial alignment supplies target reads and every selected postbinding.
No output-range or desired-run relation is a premise. -/
theorem assignment_transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (si : ι → Source.Idx srcΓ (.int ty)) (ti : ι → Idx Γ (.val .int))
    (family : IntegerLocalFamily ty si ti source.1 target.env)
    (i a : ι) (x y : Int)
    (hx : ty.lo ≤ x ∧ x ≤ ty.hi)
    (hy : ty.lo ≤ y ∧ y ≤ ty.hi)
    (readA : source.1.get (si a) = .int x hx) (readI : source.1.get (si i) = .int y hy) :
    (Source.evalE G {F with checked := false} (fuel+4)
      (.binary .mul (.assign (.local (si i)) (.local (si a))) (.local (si i)))).run source =
      (.ok (.val (Source.intWrap ty (x*(if G.pipeline = .legacy then y else x)))),
        (source.1.set (si i) (.int x hx),source.2)) ∧
    (assignReadOperand G.pipeline (ti i) (ti a)).run target =
      .ok (⟨target.setLocal (ti i) (integerValue ty x hx),List.prefix_refl _⟩,
        .prim (integerValue ty (ty.wrap (x*(if G.pipeline = .legacy then y else x)))
          (ty.wrap_mem (x*(if G.pipeline = .legacy then y else x))))) ∧
    IntValueRel ty
      (Source.intWrap ty (x*(if G.pipeline = .legacy then y else x)) :
        Source.Val E.layout (.int ty))
      (integerValue ty (ty.wrap (x*(if G.pipeline = .legacy then y else x)))
        (ty.wrap_mem (x*(if G.pipeline = .legacy then y else x)))) ∧
    IntegerLocalFamily ty si ti (source.1.set (si i) (.int x hx))
      (TEnv.set (ti i) (integerValue ty x hx) target.env) := by
  refine ⟨source_assign_read_run G F fuel source (si i) (si a) x y hx hy readA readI,
    assign_read_operand_run G.pipeline target (ti i) (ti a) x y hx hy
      (family.read a x hx readA) (family.read i y hy readI),integer_related _ _ _,?_⟩
  have post := family.write i a
  rw [readA,family.read a x hx readA] at post
  exact post

theorem assignment_extension {C : Contract} {Γ Δ : Ctx}
    (pipeline : Roadmap.Pipeline) (target : State C Γ) (i a : Idx Γ (.val .int))
    (x y : Int) (hx : ty.lo ≤ x ∧ x ≤ ty.hi)
    (hy : ty.lo ≤ y ∧ y ≤ ty.hi)
    (readA : TEnv.get a target.env = integerValue ty x hx)
    (readI : TEnv.get i target.env = integerValue ty y hy)
    (thin : Thin Γ Δ) (extra : TEnv C target.H Δ) :
    ((assignReadOperand pipeline i a).wk thin).run (target.lift thin extra) =
      liftedT₂ thin extra (.ok ((⟨target.setLocal i (integerValue ty x hx),List.prefix_refl _⟩ : Out C target.H Γ),
        SVal.prim (integerValue ty (ty.wrap (x*(if pipeline = .legacy then y else x)))
          (ty.wrap_mem (x*(if pipeline = .legacy then y else x)))))) := by
  rw [DeferredSource.Operand.run_wk,assign_read_operand_run pipeline target i a x y hx hy readA readI]
  rfl

end Solidity.Lowering.V07.SignedWordMultiplication
