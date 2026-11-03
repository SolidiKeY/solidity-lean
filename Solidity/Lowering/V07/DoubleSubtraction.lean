import Solidity.Lowering.V07.DoubleAssignmentFamily

/-! In-range subtraction with TWO actual effectful operands. The family
supplies initial target reads and identity reflection; neither final runs nor
a reached preservation relation are premises. -/
namespace Solidity.Lowering.V07

def doubleDelta (pipeline : Roadmap.Pipeline) (x z : Int) : Int :=
  (if pipeline = .legacy then z else x)-z

theorem source_assign_assign_sub_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (t : Source.IntTy) (i a b : Source.Idx Γ (.int t)) (x z : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hz : t.lo ≤ z ∧ z ≤ t.hi)
    (readA : source.1.get a = .int x hx) (readB : source.1.get b = .int z hz)
    (separate : i.toNat ≠ b.toNat)
    (resultRange : t.lo ≤ doubleDelta G.pipeline x z ∧ doubleDelta G.pipeline x z ≤ t.hi) :
    (Source.evalE G F (fuel+4)
      (.binary .sub (.assign (.local i) (.local a)) (.assign (.local a) (.local b)))).run source =
      (.ok (.val (.int (doubleDelta G.pipeline x z) resultRange)),
        (if G.pipeline = .legacy then ((source.1.set a (.int z hz)).set i (.int z hz),source.2)
          else ((source.1.set i (.int x hx)).set a (.int z hz),source.2))) := by
  have pair := source_assign_assign_pair G F fuel source i a b (.int x hx) (.int z hz) readA readB separate
  by_cases order : G.pipeline = .legacy
  · simp only [doubleDelta,order,if_true] at pair resultRange ⊢
    exact source_sub_of_pair G F (fuel+3) source _ t _ _ z z hz hz resultRange pair
  · simp only [doubleDelta,order,if_false] at pair resultRange ⊢
    exact source_sub_of_pair G F (fuel+3) source _ t _ _ x z hx hz resultRange pair

def assignAssignSubOperand {C : Contract} {Γ : Ctx} (pipeline : Roadmap.Pipeline)
    (t : Source.IntTy) (i a b : Idx Γ (.val (integerPrim t))) :
    DeferredSource.Operand C Γ (.prim (integerPrim t)) :=
  ⟨.val (integerPrim t) :: .val (integerPrim t) :: Γ,assignAssignPrefix pipeline i a b,
    match pipeline with
    | .legacy => .val (.binop .sub (integer_sub_accepts t) rfl
      (.simple (.local .here)) (.simple (.local (.there .here))))
    | .viaIR => .val (.binop .sub (integer_sub_accepts t) rfl
      (.simple (.local (.there .here))) (.simple (.local .here)))⟩

theorem assign_assign_sub_operand_run {C : Contract} {Γ : Ctx}
    (pipeline : Roadmap.Pipeline) (target : State C Γ) (t : Source.IntTy)
    (i a b : Idx Γ (.val (integerPrim t))) (x z : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hz : t.lo ≤ z ∧ z ≤ t.hi)
    (readA : TEnv.get a target.env = integerValue t x hx)
    (readB : TEnv.get b target.env = integerValue t z hz)
    (separate : i.toNat ≠ b.toNat)
    (resultRange : t.lo ≤ doubleDelta pipeline x z ∧ doubleDelta pipeline x z ≤ t.hi) :
    (assignAssignSubOperand pipeline t i a b).run target =
      .ok (⟨(if pipeline = .legacy then (target.setLocal a (integerValue t z hz)).setLocal i (integerValue t z hz)
        else (target.setLocal i (integerValue t x hx)).setLocal a (integerValue t z hz)),
        by split <;> exact List.prefix_refl _⟩,
        .prim (integerValue t (doubleDelta pipeline x z) resultRange)) := by
  cases pipeline
  · simp only [doubleDelta,if_true] at resultRange ⊢
    let caller : State C Γ := (target.setLocal a (integerValue t z hz)).setLocal i (integerValue t z hz)
    let reached : State C (.val (integerPrim t) :: .val (integerPrim t) :: Γ) := (caller.push (integerValue t z hz)).push (integerValue t z hz)
    have value := intrinsic_sub_run reached t (.simple (.local .here))
      (.simple (.local (.there .here))) z z hz hz resultRange rfl rfl
    unfold assignAssignSubOperand DeferredSource.Operand.run
    rw [assign_assign_prefix_run .legacy target i a b _ _ readA readB separate]
    change (do
      let v ← (Src.val (.binop .sub (integer_sub_accepts t) rfl
        (.simple (.local .here)) (.simple (.local (.there .here)))) :
        Src C (.val (integerPrim t) :: .val (integerPrim t) :: Γ) (.prim (integerPrim t))).valueT reached
      pure ((⟨caller,List.prefix_refl _⟩ : Out C target.H Γ),v)) = _
    simp only [Src.valueT,value]
    rfl
  · simp only [doubleDelta,reduceCtorEq,if_false] at resultRange ⊢
    let caller : State C Γ := (target.setLocal i (integerValue t x hx)).setLocal a (integerValue t z hz)
    let reached : State C (.val (integerPrim t) :: .val (integerPrim t) :: Γ) := (caller.push (integerValue t x hx)).push (integerValue t z hz)
    have value := intrinsic_sub_run reached t (.simple (.local (.there .here)))
      (.simple (.local .here)) x z hx hz resultRange rfl rfl
    unfold assignAssignSubOperand DeferredSource.Operand.run
    rw [assign_assign_prefix_run .viaIR target i a b _ _ readA readB separate]
    change (do
      let v ← (Src.val (.binop .sub (integer_sub_accepts t) rfl
        (.simple (.local (.there .here))) (.simple (.local .here))) :
        Src C (.val (integerPrim t) :: .val (integerPrim t) :: Γ) (.prim (integerPrim t))).valueT reached
      pure ((⟨caller,List.prefix_refl _⟩ : Out C target.H Γ),v)) = _
    simp only [Src.valueT,value]
    rfl

theorem double_assignment_transport {E : Source.Env} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} {ι : Type} (t : Source.IntTy)
    (si : ι → Source.Idx srcΓ (.int t)) (ti : ι → Idx Γ (.val (integerPrim t)))
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (family : IntegerLocalFamily t si ti source.1 target.env) (i a b : ι) (x z : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hz : t.lo ≤ z ∧ z ≤ t.hi)
    (readA : source.1.get (si a) = .int x hx) (readB : source.1.get (si b) = .int z hz)
    (different : (si i).toNat ≠ (si b).toNat)
    (resultRange : t.lo ≤ doubleDelta G.pipeline x z ∧ doubleDelta G.pipeline x z ≤ t.hi) :
    (Source.evalE G F (fuel+4) (.binary .sub
      (.assign (.local (si i)) (.local (si a))) (.assign (.local (si a)) (.local (si b))))).run source =
      (.ok (.val (.int (doubleDelta G.pipeline x z) resultRange)),
        (if G.pipeline = .legacy then ((source.1.set (si a) (.int z hz)).set (si i) (.int z hz),source.2)
          else ((source.1.set (si i) (.int x hx)).set (si a) (.int z hz),source.2))) ∧
    (assignAssignSubOperand G.pipeline t (ti i) (ti a) (ti b)).run target =
      .ok (⟨(if G.pipeline = .legacy then
          (target.setLocal (ti a) (integerValue t z hz)).setLocal (ti i) (integerValue t z hz)
        else (target.setLocal (ti i) (integerValue t x hx)).setLocal (ti a) (integerValue t z hz)),
        by split <;> exact List.prefix_refl _⟩,
        .prim (integerValue t (doubleDelta G.pipeline x z) resultRange)) ∧
    IntValueRel t (.int (doubleDelta G.pipeline x z) resultRange : Source.Val E.layout (.int t))
      (integerValue t (doubleDelta G.pipeline x z) resultRange) ∧
    IntegerLocalFamily t si ti
      (if G.pipeline = .legacy then (source.1.set (si a) (.int z hz)).set (si i) (.int z hz)
        else (source.1.set (si i) (.int x hx)).set (si a) (.int z hz))
      (if G.pipeline = .legacy then
        TEnv.set (ti i) (integerValue t z hz) (TEnv.set (ti a) (integerValue t z hz) target.env)
        else TEnv.set (ti a) (integerValue t z hz) (TEnv.set (ti i) (integerValue t x hx) target.env)) :=
  ⟨source_assign_assign_sub_run G F fuel source t (si i) (si a) (si b) x z hx hz readA readB different resultRange,
    assign_assign_sub_operand_run G.pipeline target t (ti i) (ti a) (ti b) x z hx hz
      (family.read a x hx readA) (family.read b z hz readB) (family.separate i b different) resultRange,
    integer_related t _ resultRange,
    family.assign_pair G.pipeline i a b x z hx hz readA readB different⟩

theorem assign_assign_sub_extension {C : Contract} {Γ Δ : Ctx}
    (pipeline : Roadmap.Pipeline) (target : State C Γ) (t : Source.IntTy)
    (i a b : Idx Γ (.val (integerPrim t))) (x z : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hz : t.lo ≤ z ∧ z ≤ t.hi)
    (readA : TEnv.get a target.env = integerValue t x hx)
    (readB : TEnv.get b target.env = integerValue t z hz)
    (different : i.toNat ≠ b.toNat)
    (resultRange : t.lo ≤ doubleDelta pipeline x z ∧ doubleDelta pipeline x z ≤ t.hi)
    (thin : Thin Γ Δ) (extra : TEnv C target.H Δ) :
    ((assignAssignSubOperand pipeline t i a b).wk thin).run (target.lift thin extra) =
      liftedT₂ thin extra (.ok ((⟨(if pipeline = .legacy then
          (target.setLocal a (integerValue t z hz)).setLocal i (integerValue t z hz)
        else (target.setLocal i (integerValue t x hx)).setLocal a (integerValue t z hz)),
        by split <;> exact List.prefix_refl _⟩ : Out C target.H Γ),
        SVal.prim (integerValue t (doubleDelta pipeline x z) resultRange))) := by
  rw [DeferredSource.Operand.run_wk,
    assign_assign_sub_operand_run pipeline target t i a b x z hx hz readA readB different resultRange]

end Solidity.Lowering.V07
