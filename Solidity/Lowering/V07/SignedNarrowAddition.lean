import Solidity.Lowering.V07.SignedNarrowing
import Solidity.Lowering.V07.SignedWordAddition

/-! Actual unchecked signed addition at every approved width, through
published int256 arithmetic and signed narrowing. No opcode compiler is added. -/
namespace Solidity.Lowering.V07.SignedNarrowAddition
open SignedWidthCasts (ty)
open SignedNarrowing (wrap_of_range wrap_word)

def addValue (bits : Nat) {C : Contract} {Γ : Ctx} (a b : Val C Γ .int) : Val C Γ .int :=
  SignedWidthCasts.castValue bits (SignedWordAddition.addValue a b)

theorem source_add_unchecked (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) {D : Source.Layout} (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi) (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi) :
    Source.binVal false .add (.int x hx : Source.Val D (.int (ty bits valid))) (.int y hy) =
      .ok (Source.intWrap (ty bits valid) (x+y)) := by
  simp only [Source.binVal,Source.intBin,Source.intRes]
  split
  · rename_i h
    have hw := wrap_of_range bits valid (x+y) h
    simp only [Source.intWrap,hw]
    rfl
  · rfl

theorem add_value_run (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) {C : Contract} {Γ : Ctx} (target : State C Γ) (a b : Val C Γ .int)
    (x y : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi) (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (left : a.evalT target = .ok (integerValue (ty bits valid) x hx))
    (right : b.evalT target = .ok (integerValue (ty bits valid) y hy)) :
    (addValue bits a b).evalT target =
      .ok (integerValue (ty bits valid) ((ty bits valid).wrap (x+y)) ((ty bits valid).wrap_mem (x+y))) := by
  have wide := SignedWordAddition.add_value_run target a b x y
    (SignedWidthCasts.word_range bits valid x hx) (SignedWidthCasts.word_range bits valid y hy) left right
  have result := SignedWidthCasts.value_run 256 (by decide) target bits valid
    (SignedWordAddition.addValue a b) (WordCasts.signed.wrap (x+y)) (WordCasts.signed.wrap_mem (x+y)) wide
  simpa only [addValue,wrap_word bits valid] using result

theorem source_from_pair (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source mid : Source.EMState E Γ)
    (a b : Source.RExpr E Γ (.int (ty bits valid))) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (pair : (Source.evalPair G {F with checked := false} fuel a b).run source =
      (.ok (.val (.int x hx),.val (.int y hy)),mid)) :
    (Source.evalE G {F with checked := false} (fuel+1) (.binary .add a b)).run source =
      (.ok (.val (Source.intWrap (ty bits valid) (x+y))),mid) := by
  rw [Source.evalE]
  simp only [reduceCtorEq,decide_false,Bool.false_or,Bool.false_eq_true,if_false]
  rw [Source.Hoare.run_bind,pair]
  change (do
    let v ← Source.EM.lift (Source.binVal false .add
      (.int x hx : Source.Val E.layout (.int (ty bits valid))) (.int y hy))
    pure (Source.RVal.val v)).run mid = _
  rw [source_add_unchecked bits valid]
  rfl

theorem source_locals_run (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (a b : Source.Idx Γ (.int (ty bits valid))) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (readA : source.1.get a = .int x hx) (readB : source.1.get b = .int y hy) :
    (Source.evalE G {F with checked := false} (fuel+3)
      (.binary .add (.local a) (.local b))).run source =
      (.ok (.val (Source.intWrap (ty bits valid) (x+y))),source) :=
  source_from_pair bits valid G F (fuel+2) source source _ _ x y hx hy
    (source_local_pair G {F with checked := false} fuel source (ty bits valid) a b x y hx hy readA readB)

theorem locals_transport (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (si : ι → Source.Idx srcΓ (.int (ty bits valid))) (ti : ι → Idx Γ (.val .int))
    (family : IntegerLocalFamily (ty bits valid) si ti source.1 target.env)
    (a b : ι) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (readA : source.1.get (si a) = .int x hx) (readB : source.1.get (si b) = .int y hy) :
    (Source.evalE G {F with checked := false} (fuel+3)
      (.binary .add (.local (si a)) (.local (si b)))).run source =
      (.ok (.val (Source.intWrap (ty bits valid) (x+y))),source) ∧
    (addValue bits (.simple (.local (ti a))) (.simple (.local (ti b)))).evalT target =
      .ok (integerValue (ty bits valid) ((ty bits valid).wrap (x+y)) ((ty bits valid).wrap_mem (x+y))) ∧
    IntValueRel (ty bits valid) (Source.intWrap (ty bits valid) (x+y) : Source.Val E.layout (.int (ty bits valid)))
      (integerValue (ty bits valid) ((ty bits valid).wrap (x+y)) ((ty bits valid).wrap_mem (x+y))) := by
  refine ⟨source_locals_run bits valid G F fuel source (si a) (si b) x y hx hy readA readB,
    add_value_run bits valid target _ _ x y hx hy ?_ ?_,integer_related _ _ _⟩
  · change Except.ok (TEnv.get (ti a) target.env) = _
    rw [family.read a x hx readA]
  · change Except.ok (TEnv.get (ti b) target.env) = _
    rw [family.read b y hy readB]

/-- Actual effectful assignment/read expression; result bounds come from
Source wrapping, never a desired-result range premise. -/
theorem source_assign_read_run (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (i a : Source.Idx Γ (.int (ty bits valid))) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (readA : source.1.get a = .int x hx) (readI : source.1.get i = .int y hy) :
    (Source.evalE G {F with checked := false} (fuel+4)
      (.binary .add (.assign (.local i) (.local a)) (.local i))).run source =
      (.ok (.val (Source.intWrap (ty bits valid) (x+(if G.pipeline = .legacy then y else x)))),
        (source.1.set i (.int x hx),source.2)) := by
  have pair := source_assign_read_pair G {F with checked := false} fuel source i a
    (.int x hx) (.int y hy) readA readI
  by_cases order : G.pipeline = .legacy
  · simp only [order,if_true] at pair ⊢
    exact source_from_pair bits valid G F (fuel+3) source _ _ _ x y hx hy pair
  · simp only [order,if_false] at pair ⊢
    exact source_from_pair bits valid G F (fuel+3) source _ _ _ x x hx hx pair

def assignReadOperand (bits : Nat) {C : Contract} {Γ : Ctx} (pipeline : Roadmap.Pipeline)
    (i a : Idx Γ (.val .int)) : DeferredSource.Operand C Γ (.prim .int) :=
  ⟨.val .int :: .val .int :: Γ,assignReadPrefix pipeline i a,
    match pipeline with
    | .legacy => .val (addValue bits (.simple (.local .here)) (.simple (.local (.there .here))))
    | .viaIR => .val (addValue bits (.simple (.local (.there .here))) (.simple (.local .here)))⟩

theorem assign_read_operand_run (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) {C : Contract} {Γ : Ctx} (pipeline : Roadmap.Pipeline)
    (target : State C Γ)
    (i a : Idx Γ (.val .int)) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (readA : TEnv.get a target.env = integerValue (ty bits valid) x hx)
    (readI : TEnv.get i target.env = integerValue (ty bits valid) y hy) :
    (assignReadOperand bits pipeline i a).run target =
      .ok (⟨target.setLocal i (integerValue (ty bits valid) x hx),List.prefix_refl _⟩,
        .prim (integerValue (ty bits valid) ((ty bits valid).wrap (x+(if pipeline = .legacy then y else x)))
          ((ty bits valid).wrap_mem (x+(if pipeline = .legacy then y else x))))) := by
  cases pipeline
  · let reached : State C (.val .int :: .val .int :: Γ) :=
      ((target.setLocal i (integerValue (ty bits valid) x hx)).push (integerValue (ty bits valid) y hy)).push
        (integerValue (ty bits valid) x hx)
    have value := add_value_run bits valid reached (.simple (.local .here))
      (.simple (.local (.there .here))) x y hx hy rfl rfl
    unfold assignReadOperand DeferredSource.Operand.run
    rw [assign_read_prefix_run .legacy target i a _ _ readA readI]
    change (do
      let v ← (Src.val (addValue bits (.simple (.local .here)) (.simple (.local (.there .here)))) :
        Src C (.val .int :: .val .int :: Γ) (.prim .int)).valueT reached
      pure ((⟨target.setLocal i (integerValue (ty bits valid) x hx),List.prefix_refl _⟩ : Out C target.H Γ),v)) = _
    simp only [Src.valueT,value]
    rfl
  · let reached : State C (.val .int :: .val .int :: Γ) :=
      ((target.setLocal i (integerValue (ty bits valid) x hx)).push (integerValue (ty bits valid) x hx)).push
        (integerValue (ty bits valid) x hx)
    have value := add_value_run bits valid reached (.simple (.local (.there .here)))
      (.simple (.local .here)) x x hx hx rfl rfl
    unfold assignReadOperand DeferredSource.Operand.run
    rw [assign_read_prefix_run .viaIR target i a _ _ readA readI]
    change (do
      let v ← (Src.val (addValue bits (.simple (.local (.there .here))) (.simple (.local .here))) :
        Src C (.val .int :: .val .int :: Γ) (.prim .int)).valueT reached
      pure ((⟨target.setLocal i (integerValue (ty bits valid) x hx),List.prefix_refl _⟩ : Out C target.H Γ),v)) = _
    simp only [Src.valueT,value]
    rfl

/-- Initial alignment supplies target reads and every selected postbinding.
No output-range or desired-run relation is a premise. -/
theorem assignment_transport (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (si : ι → Source.Idx srcΓ (.int (ty bits valid))) (ti : ι → Idx Γ (.val .int))
    (family : IntegerLocalFamily (ty bits valid) si ti source.1 target.env)
    (i a : ι) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (readA : source.1.get (si a) = .int x hx) (readI : source.1.get (si i) = .int y hy) :
    (Source.evalE G {F with checked := false} (fuel+4)
      (.binary .add (.assign (.local (si i)) (.local (si a))) (.local (si i)))).run source =
      (.ok (.val (Source.intWrap (ty bits valid) (x+(if G.pipeline = .legacy then y else x)))),
        (source.1.set (si i) (.int x hx),source.2)) ∧
    (assignReadOperand bits G.pipeline (ti i) (ti a)).run target =
      .ok (⟨target.setLocal (ti i) (integerValue (ty bits valid) x hx),List.prefix_refl _⟩,
        .prim (integerValue (ty bits valid) ((ty bits valid).wrap (x+(if G.pipeline = .legacy then y else x)))
          ((ty bits valid).wrap_mem (x+(if G.pipeline = .legacy then y else x))))) ∧
    IntValueRel (ty bits valid)
      (Source.intWrap (ty bits valid) (x+(if G.pipeline = .legacy then y else x)) :
        Source.Val E.layout (.int (ty bits valid)))
      (integerValue (ty bits valid) ((ty bits valid).wrap (x+(if G.pipeline = .legacy then y else x)))
        ((ty bits valid).wrap_mem (x+(if G.pipeline = .legacy then y else x)))) ∧
    IntegerLocalFamily (ty bits valid) si ti (source.1.set (si i) (.int x hx))
      (TEnv.set (ti i) (integerValue (ty bits valid) x hx) target.env) := by
  refine ⟨source_assign_read_run bits valid G F fuel source (si i) (si a) x y hx hy readA readI,
    assign_read_operand_run bits valid G.pipeline target (ti i) (ti a) x y hx hy
      (family.read a x hx readA) (family.read i y hy readI),integer_related _ _ _,?_⟩
  have post := family.write i a
  rw [readA,family.read a x hx readA] at post
  exact post

theorem assignment_extension (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) {C : Contract} {Γ Δ : Ctx}
    (pipeline : Roadmap.Pipeline) (target : State C Γ) (i a : Idx Γ (.val .int))
    (x y : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (readA : TEnv.get a target.env = integerValue (ty bits valid) x hx)
    (readI : TEnv.get i target.env = integerValue (ty bits valid) y hy)
    (thin : Thin Γ Δ) (extra : TEnv C target.H Δ) :
    ((assignReadOperand bits pipeline i a).wk thin).run (target.lift thin extra) =
      liftedT₂ thin extra (.ok ((⟨target.setLocal i (integerValue (ty bits valid) x hx),List.prefix_refl _⟩ : Out C target.H Γ),
        SVal.prim (integerValue (ty bits valid) ((ty bits valid).wrap (x+(if pipeline = .legacy then y else x)))
          ((ty bits valid).wrap_mem (x+(if pipeline = .legacy then y else x)))))) := by
  rw [DeferredSource.Operand.run_wk,assign_read_operand_run bits valid pipeline target i a x y hx hy readA readI]
  rfl


end Solidity.Lowering.V07.SignedNarrowAddition
