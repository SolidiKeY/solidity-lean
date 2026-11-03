import Solidity.Lowering.V07.AllAliasPair
import Solidity.Lowering.V07.DoubleSubtraction

/-! The previously missing i=b clause uses REACHED reads. Its numeric result
is zero in both pipelines, while captures and final callers still differ. -/
namespace Solidity.Lowering.V07

theorem integer_zero_range (t : Source.IntTy) : t.lo ≤ 0 ∧ 0 ≤ t.hi := by
  have hp : 0 ≤ ((2 ^ (t.bits - 1) : Nat) : Int) := Int.natCast_nonneg _
  cases hs : t.signed <;>
    simp only [Source.IntTy.lo, Source.IntTy.hi, hs, Bool.false_eq_true, if_false, if_true] <;>
    constructor <;> omega

theorem source_alias_rhs_sub_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (t : Source.IntTy) (i a : Source.Idx Γ (.int t)) (x z : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hz : t.lo ≤ z ∧ z ≤ t.hi)
    (readA : source.1.get a = .int x hx) (readI : source.1.get i = .int z hz) :
    (Source.evalE G F (fuel+4) (.binary .sub
      (.assign (.local i) (.local a)) (.assign (.local a) (.local i)))).run source =
      (.ok (.val (.int 0 (integer_zero_range t))),
        (if G.pipeline = .legacy then ((source.1.set a (.int z hz)).set i (.int z hz),source.2)
          else ((source.1.set i (.int x hx)).set a (.int x hx),source.2))) := by
  have pair := source_assign_assign_pair_all_aliases G F fuel source i a i
    (.int x hx) (.int z hz) readA readI
  cases order : G.pipeline
  · simp only [order,if_true] at pair ⊢
    have hzero : t.lo ≤ z-z ∧ z-z ≤ t.hi := by
      simpa only [Int.sub_self] using integer_zero_range t
    simpa only [Int.sub_self] using
      source_sub_of_pair G F (fuel+3) source _ t _ _ z z hz hz hzero pair
  · simp only [order,reduceCtorEq,if_false,ite_true] at pair ⊢
    have hzero : t.lo ≤ x-x ∧ x-x ≤ t.hi := by
      simpa only [Int.sub_self] using integer_zero_range t
    simpa only [Int.sub_self] using
      source_sub_of_pair G F (fuel+3) source _ t _ _ x x hx hx hzero pair

theorem alias_rhs_sub_operand_run {C : Contract} {Γ : Ctx}
    (pipeline : Roadmap.Pipeline) (target : State C Γ) (t : Source.IntTy)
    (i a : Idx Γ (.val (integerPrim t))) (x z : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hz : t.lo ≤ z ∧ z ≤ t.hi)
    (readA : TEnv.get a target.env = integerValue t x hx)
    (readI : TEnv.get i target.env = integerValue t z hz) :
    (assignAssignSubOperand pipeline t i a i).run target =
      .ok (⟨(if pipeline = .legacy then
          (target.setLocal a (integerValue t z hz)).setLocal i (integerValue t z hz)
        else (target.setLocal i (integerValue t x hx)).setLocal a (integerValue t x hx)),
        by split <;> exact List.prefix_refl _⟩,
        .prim (integerValue t 0 (integer_zero_range t))) := by
  cases pipeline
  · let caller : State C Γ := (target.setLocal a (integerValue t z hz)).setLocal i (integerValue t z hz)
    let reached : State C (.val (integerPrim t) :: .val (integerPrim t) :: Γ) :=
      (caller.push (integerValue t z hz)).push (integerValue t z hz)
    have hzero : t.lo ≤ z-z ∧ z-z ≤ t.hi := by
      simpa only [Int.sub_self] using integer_zero_range t
    have value := intrinsic_sub_run reached t (.simple (.local .here))
      (.simple (.local (.there .here))) z z hz hz hzero rfl rfl
    simp only [Int.sub_self] at value
    unfold assignAssignSubOperand DeferredSource.Operand.run
    rw [assign_assign_prefix_all_aliases .legacy target i a i _ _ readA readI]
    change (do
      let v ← (Src.val (.binop .sub (integer_sub_accepts t) rfl
        (.simple (.local .here)) (.simple (.local (.there .here)))) :
        Src C (.val (integerPrim t) :: .val (integerPrim t) :: Γ) (.prim (integerPrim t))).valueT reached
      pure ((⟨caller,List.prefix_refl _⟩ : Out C target.H Γ),v)) = _
    simp only [Src.valueT,value]
    rfl
  · let caller : State C Γ := (target.setLocal i (integerValue t x hx)).setLocal a (integerValue t x hx)
    let reached : State C (.val (integerPrim t) :: .val (integerPrim t) :: Γ) :=
      (caller.push (integerValue t x hx)).push (integerValue t x hx)
    have hzero : t.lo ≤ x-x ∧ x-x ≤ t.hi := by
      simpa only [Int.sub_self] using integer_zero_range t
    have value := intrinsic_sub_run reached t (.simple (.local (.there .here)))
      (.simple (.local .here)) x x hx hx hzero rfl rfl
    simp only [Int.sub_self] at value
    unfold assignAssignSubOperand DeferredSource.Operand.run
    have pref : (assignAssignPrefix .viaIR i a i).run target =
        .ok (⟨reached,List.prefix_refl _⟩) := by
      have h := assign_assign_prefix_all_aliases .viaIR target i a i _ _ readA readI
      rw [if_pos (rfl : i.toNat = i.toNat)] at h
      simpa only [reduceCtorEq, if_false, ite_true] using h
    rw [pref]
    change (do
      let v ← (Src.val (.binop .sub (integer_sub_accepts t) rfl
        (.simple (.local (.there .here))) (.simple (.local .here))) :
        Src C (.val (integerPrim t) :: .val (integerPrim t) :: Γ) (.prim (integerPrim t))).valueT reached
      pure ((⟨caller,List.prefix_refl _⟩ : Out C target.H Γ),v)) = _
    simp only [Src.valueT,value]
    rfl

/-- Initial selected value/identity alignment derives both actual runs and
EVERY selected caller value after the two writes. The numeric zero range is
proved for all approved widths/signs; it is not supplied as a result premise. -/
theorem alias_rhs_sub_transport {E : Source.Env} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} {ι : Type} (t : Source.IntTy)
    (si : ι → Source.Idx srcΓ (.int t)) (ti : ι → Idx Γ (.val (integerPrim t)))
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (family : IntegerLocalFamily t si ti source.1 target.env) (i a : ι) (x z : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hz : t.lo ≤ z ∧ z ≤ t.hi)
    (readA : source.1.get (si a) = .int x hx) (readI : source.1.get (si i) = .int z hz) :
    (Source.evalE G F (fuel+4) (.binary .sub
      (.assign (.local (si i)) (.local (si a))) (.assign (.local (si a)) (.local (si i))))).run source =
      (.ok (.val (.int 0 (integer_zero_range t))),
        (if G.pipeline = .legacy then
          ((source.1.set (si a) (.int z hz)).set (si i) (.int z hz),source.2)
        else ((source.1.set (si i) (.int x hx)).set (si a) (.int x hx),source.2))) ∧
    (assignAssignSubOperand G.pipeline t (ti i) (ti a) (ti i)).run target =
      .ok (⟨(if G.pipeline = .legacy then
          (target.setLocal (ti a) (integerValue t z hz)).setLocal (ti i) (integerValue t z hz)
        else (target.setLocal (ti i) (integerValue t x hx)).setLocal (ti a) (integerValue t x hx)),
        by split <;> exact List.prefix_refl _⟩,.prim (integerValue t 0 (integer_zero_range t))) ∧
    IntValueRel t (.int 0 (integer_zero_range t) : Source.Val E.layout (.int t))
      (integerValue t 0 (integer_zero_range t)) ∧
    IntegerLocalFamily t si ti
      (if G.pipeline = .legacy then (source.1.set (si a) (.int z hz)).set (si i) (.int z hz)
        else (source.1.set (si i) (.int x hx)).set (si a) (.int x hx))
      (if G.pipeline = .legacy then
        TEnv.set (ti i) (integerValue t z hz) (TEnv.set (ti a) (integerValue t z hz) target.env)
        else TEnv.set (ti a) (integerValue t x hx) (TEnv.set (ti i) (integerValue t x hx) target.env)) := by
  refine ⟨source_alias_rhs_sub_run G F fuel source t (si i) (si a) x z hx hz readA readI,
    alias_rhs_sub_operand_run G.pipeline target t (ti i) (ti a) x z hx hz
      (family.read a x hx readA) (family.read i z hz readI),
    integer_related t 0 (integer_zero_range t), ?_⟩
  have h := family.assign_pair_all_aliases G.pipeline i a i x z hx hz readA readI
  rw [if_pos (rfl : (si i).toNat = (si i).toNat)] at h
  simpa only [ite_true] using h

theorem alias_rhs_sub_extension {C : Contract} {Γ Δ : Ctx}
    (pipeline : Roadmap.Pipeline) (target : State C Γ) (t : Source.IntTy)
    (i a : Idx Γ (.val (integerPrim t))) (x z : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hz : t.lo ≤ z ∧ z ≤ t.hi)
    (readA : TEnv.get a target.env = integerValue t x hx)
    (readI : TEnv.get i target.env = integerValue t z hz)
    (thin : Thin Γ Δ) (extra : TEnv C target.H Δ) :
    ((assignAssignSubOperand pipeline t i a i).wk thin).run (target.lift thin extra) =
      liftedT₂ thin extra (.ok ((⟨(if pipeline = .legacy then
          (target.setLocal a (integerValue t z hz)).setLocal i (integerValue t z hz)
        else (target.setLocal i (integerValue t x hx)).setLocal a (integerValue t x hx)),
        by split <;> exact List.prefix_refl _⟩ : Out C target.H Γ),
        SVal.prim (integerValue t 0 (integer_zero_range t)))) := by
  rw [DeferredSource.Operand.run_wk,
    alias_rhs_sub_operand_run pipeline target t i a x z hx hz readA readI]

end Solidity.Lowering.V07
