import Solidity.Lowering.V07.IntegerSubtraction

namespace Solidity.Lowering.V07

/-- Read the captured LEFT minus captured RIGHT, even when evaluation was
right-first. These are existing typed Val/Prog/Operand constructors only. -/
def assignReadSubOperand {C : Contract} {Γ : Ctx} (pipeline : Roadmap.Pipeline)
    (t : Source.IntTy) (i a : Idx Γ (.val (integerPrim t))) :
    DeferredSource.Operand C Γ (.prim (integerPrim t)) :=
  ⟨.val (integerPrim t) :: .val (integerPrim t) :: Γ,assignReadPrefix pipeline i a,
    match pipeline with
    | .legacy => .val (.binop .sub (integer_sub_accepts t) rfl
      (.simple (.local .here)) (.simple (.local (.there .here))))
    | .viaIR => .val (.binop .sub (integer_sub_accepts t) rfl
      (.simple (.local (.there .here))) (.simple (.local .here)))⟩

theorem assign_read_sub_operand_run {C : Contract} {Γ : Ctx}
    (pipeline : Roadmap.Pipeline) (target : State C Γ) (t : Source.IntTy)
    (i a : Idx Γ (.val (integerPrim t))) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (readA : TEnv.get a target.env = integerValue t x hx)
    (readI : TEnv.get i target.env = integerValue t y hy)
    (hz : t.lo ≤ x-(if pipeline = .legacy then y else x) ∧
      x-(if pipeline = .legacy then y else x) ≤ t.hi) :
    (assignReadSubOperand pipeline t i a).run target =
      .ok (⟨target.setLocal i (integerValue t x hx),List.prefix_refl _⟩,
        .prim (integerValue t (x-(if pipeline = .legacy then y else x)) hz)) := by
  cases pipeline
  · simp only [if_true] at hz ⊢
    let reached : State C (.val (integerPrim t) :: .val (integerPrim t) :: Γ) := ((target.setLocal i (integerValue t x hx)).push (integerValue t y hy)).push (integerValue t x hx)
    have hv := intrinsic_sub_run reached t (.simple (.local .here))
      (.simple (.local (.there .here))) x y hx hy hz rfl rfl
    unfold assignReadSubOperand DeferredSource.Operand.run
    rw [assign_read_prefix_run .legacy target i a _ _ readA readI]
    change (do
      let value ← (Src.val (.binop .sub (integer_sub_accepts t) rfl
        (.simple (.local .here)) (.simple (.local (.there .here)))) :
        Src C (.val (integerPrim t) :: .val (integerPrim t) :: Γ) (.prim (integerPrim t))).valueT reached
      pure ((⟨target.setLocal i (integerValue t x hx),List.prefix_refl _⟩ : Out C target.H Γ),value)) = _
    simp only [Src.valueT,hv]
    rfl
  · simp only [reduceCtorEq,if_false] at hz ⊢
    let reached : State C (.val (integerPrim t) :: .val (integerPrim t) :: Γ) := ((target.setLocal i (integerValue t x hx)).push (integerValue t x hx)).push (integerValue t x hx)
    have hv := intrinsic_sub_run reached t (.simple (.local (.there .here)))
      (.simple (.local .here)) x x hx hx hz rfl rfl
    unfold assignReadSubOperand DeferredSource.Operand.run
    rw [assign_read_prefix_run .viaIR target i a _ _ readA readI]
    change (do
      let value ← (Src.val (.binop .sub (integer_sub_accepts t) rfl
        (.simple (.local (.there .here))) (.simple (.local .here))) :
        Src C (.val (integerPrim t) :: .val (integerPrim t) :: Γ) (.prim (integerPrim t))).valueT reached
      pure ((⟨target.setLocal i (integerValue t x hx),List.prefix_refl _⟩ : Out C target.H Γ),value)) = _
    simp only [Src.valueT,hv]
    rfl

theorem assign_read_sub_extension {C : Contract} {Γ Δ : Ctx}
    (pipeline : Roadmap.Pipeline) (target : State C Γ) (t : Source.IntTy)
    (i a : Idx Γ (.val (integerPrim t))) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (readA : TEnv.get a target.env = integerValue t x hx)
    (readI : TEnv.get i target.env = integerValue t y hy)
    (hz : t.lo ≤ x-(if pipeline = .legacy then y else x) ∧
      x-(if pipeline = .legacy then y else x) ≤ t.hi)
    (thin : Thin Γ Δ) (extra : TEnv C target.H Δ) :
    ((assignReadSubOperand pipeline t i a).wk thin).run (target.lift thin extra) =
      liftedT₂ thin extra (.ok ((⟨target.setLocal i (integerValue t x hx),List.prefix_refl _⟩ : Out C target.H Γ),
        SVal.prim (integerValue t (x-(if pipeline = .legacy then y else x)) hz))) := by
  rw [DeferredSource.Operand.run_wk,
    assign_read_sub_operand_run pipeline target t i a x y hx hy readA readI hz]

theorem assignment_subtraction_transport {E : Source.Env} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (t : Source.IntTy)
    (i a : Source.Idx srcΓ (.int t)) (j b : Idx Γ (.val (integerPrim t)))
    (x y : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (sourceA : source.1.get a = .int x hx) (sourceI : source.1.get i = .int y hy)
    (targetA : TEnv.get b target.env = integerValue t x hx)
    (targetI : TEnv.get j target.env = integerValue t y hy)
    (hz : t.lo ≤ x-(if G.pipeline = .legacy then y else x) ∧
      x-(if G.pipeline = .legacy then y else x) ≤ t.hi) :
    (Source.evalE G F (fuel+4)
      (.binary .sub (.assign (.local i) (.local a)) (.local i))).run source =
      (.ok (.val (.int (x-(if G.pipeline = .legacy then y else x)) hz)),
        (source.1.set i (.int x hx),source.2)) ∧
    (assignReadSubOperand G.pipeline t j b).run target =
      .ok (⟨target.setLocal j (integerValue t x hx),List.prefix_refl _⟩,
        .prim (integerValue t (x-(if G.pipeline = .legacy then y else x)) hz)) ∧
    IntValueRel t (.int (x-(if G.pipeline = .legacy then y else x)) hz :
      Source.Val E.layout (.int t)) (integerValue t (x-(if G.pipeline = .legacy then y else x)) hz) :=
  ⟨source_assign_sub_run G F fuel source t i a x y hx hy sourceA sourceI hz,
    assign_read_sub_operand_run G.pipeline target t j b x y hx hy targetA targetI hz,
    integer_related t _ hz⟩

end Solidity.Lowering.V07
