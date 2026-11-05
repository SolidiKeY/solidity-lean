import Solidity.Lowering.V07.UnsignedMultiplication
import Solidity.Lowering.V07.WrappedAssignmentPair
import Solidity.Lowering.V07.AllAliasPair

/-! Two actual effectful integer operands, unchecked unsigned multiplication.
All aliases are permitted; this composes published operations, not replacement Source
execution semantics or an alternative evaluator. -/
namespace Solidity.Lowering.V07.WrappedMultiplicationPair
open UnsignedNarrowing (ty)
open UnsignedMultiplication
open WrappedAssignmentPair (sourcePost targetPost)

/-- Arithmetic observation only; the alias test is supplied by existing indices. -/
def product (p : Roadmap.Pipeline) (same : Bool) (x z : Int) : Int :=
  (if p = .legacy then z else x) *
    (if p = .legacy then z else if same then x else z)

theorem source_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (s : Source.EMState E Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (i a b : Source.Idx Γ (.int (ty bits valid))) (x z : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hz : (ty bits valid).lo ≤ z ∧ z ≤ (ty bits valid).hi)
    (readA : s.1.get a = .int x hx) (readB : s.1.get b = .int z hz) :
    (Source.evalE G {F with checked := false} (fuel+4) (.binary .mul
      (.assign (.local i) (.local a)) (.assign (.local a) (.local b)))).run s =
      (.ok (.val (Source.intWrap (ty bits valid)
        (product G.pipeline (decide (i.toNat = b.toNat)) x z))),
        sourcePost G.pipeline s bits valid i a b x z hx hz) := by
  have pair := source_assign_assign_pair_all_aliases G {F with checked := false} fuel s
    i a b (.int x hx) (.int z hz) readA readB
  cases order : G.pipeline
  · simp only [order,product,sourcePost,if_true] at pair ⊢
    exact source_from_pair G F (fuel+3) s _ bits valid _ _ z z hz hz pair
  · by_cases same : i.toNat = b.toNat
    · simp only [order,product,sourcePost,reduceCtorEq,if_false,same,decide_true,if_true] at pair ⊢
      exact source_from_pair G F (fuel+3) s _ bits valid _ _ x x hx hx pair
    · simp only [order,product,sourcePost,reduceCtorEq,if_false,same,decide_false,Bool.false_eq_true] at pair ⊢
      exact source_from_pair G F (fuel+3) s _ bits valid _ _ x z hx hz pair

def operand {C : Contract} {Γ : Ctx} (p : Roadmap.Pipeline)
    (bits : Nat) (i a b : Idx Γ (.val .uint)) : DeferredSource.Operand C Γ (.prim .uint) :=
  ⟨.val .uint :: .val .uint :: Γ,assignAssignPrefix p i a b,
    match p with
    | .legacy => .val (mulValue bits (.simple (.local .here)) (.simple (.local (.there .here))))
    | .viaIR => .val (mulValue bits (.simple (.local (.there .here))) (.simple (.local .here)))⟩

theorem operand_run {C : Contract} {Γ : Ctx} (p : Roadmap.Pipeline)
    (s : State C Γ) (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (i a b : Idx Γ (.val .uint)) (x z : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hz : (ty bits valid).lo ≤ z ∧ z ≤ (ty bits valid).hi)
    (readA : TEnv.get a s.env = integerValue (ty bits valid) x hx)
    (readB : TEnv.get b s.env = integerValue (ty bits valid) z hz) :
    (operand p bits i a b).run s =
      .ok (⟨targetPost p s bits valid i a b x z hx hz,by cases p <;> exact List.prefix_refl _⟩,
        .prim (integerValue (ty bits valid)
          ((ty bits valid).wrap (product p (decide (i.toNat = b.toNat)) x z))
          ((ty bits valid).wrap_mem (product p (decide (i.toNat = b.toNat)) x z)))) := by
  have seqRun := assign_assign_prefix_all_aliases p s i a b _ _ readA readB
  cases p
  · let caller := targetPost .legacy s bits valid i a b x z hx hz
    let reached : State C (.val .uint :: .val .uint :: Γ) := (caller.push (integerValue (ty bits valid) z hz)).push (integerValue (ty bits valid) z hz)
    have value := mul_value_run reached bits valid (.simple (.local .here))
      (.simple (.local (.there .here))) z z hz hz rfl rfl
    unfold operand DeferredSource.Operand.run
    rw [seqRun]
    change (do
      let v ← (Src.val (mulValue bits (.simple (.local .here)) (.simple (.local (.there .here)))) :
        Src C (.val .uint :: .val .uint :: Γ) (.prim .uint)).valueT reached
      pure ((⟨caller,List.prefix_refl _⟩ : Out C s.H Γ),v)) = _
    simp only [Src.valueT,value,product,if_true]
    rfl
  · by_cases same : i.toNat = b.toNat
    · simp only [same,if_true] at seqRun
      let caller := targetPost .viaIR s bits valid i a b x z hx hz
      let reached : State C (.val .uint :: .val .uint :: Γ) := (caller.push (integerValue (ty bits valid) x hx)).push (integerValue (ty bits valid) x hx)
      have value := mul_value_run reached bits valid (.simple (.local (.there .here)))
        (.simple (.local .here)) x x hx hx rfl rfl
      unfold operand DeferredSource.Operand.run
      rw [seqRun]
      change (do
        let v ← (Src.val (mulValue bits (.simple (.local (.there .here))) (.simple (.local .here))) :
          Src C (.val .uint :: .val .uint :: Γ) (.prim .uint)).valueT reached
        pure ((⟨caller,List.prefix_refl _⟩ : Out C s.H Γ),v)) = _
      simp only [Src.valueT,value,product,reduceCtorEq,if_false,same,decide_true,if_true]
      rfl
    · simp only [same,if_false] at seqRun
      let caller := targetPost .viaIR s bits valid i a b x z hx hz
      let reached : State C (.val .uint :: .val .uint :: Γ) := (caller.push (integerValue (ty bits valid) x hx)).push (integerValue (ty bits valid) z hz)
      have value := mul_value_run reached bits valid (.simple (.local (.there .here)))
        (.simple (.local .here)) x z hx hz rfl rfl
      unfold operand DeferredSource.Operand.run
      rw [seqRun]
      change (do
        let v ← (Src.val (mulValue bits (.simple (.local (.there .here))) (.simple (.local .here))) :
          Src C (.val .uint :: .val .uint :: Γ) (.prim .uint)).valueT reached
        pure ((⟨caller,List.prefix_refl _⟩ : Out C s.H Γ),v)) = _
      simp only [Src.valueT,value,product,reduceCtorEq,if_false,same,decide_false,Bool.false_eq_true]
      rfl

/-- INITIAL value/identity alignment derives both effect runs and the whole
selected postfamily. No desired result, postfamily, output-range or inequality premise. -/
theorem transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (si : ι → Source.Idx srcΓ (.int (ty bits valid))) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily (ty bits valid) si ti source.1 target.env)
    (i a b : ι) (x z : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hz : (ty bits valid).lo ≤ z ∧ z ≤ (ty bits valid).hi)
    (readA : source.1.get (si a) = .int x hx) (readB : source.1.get (si b) = .int z hz) :
    (Source.evalE G {F with checked := false} (fuel+4) (.binary .mul
      (.assign (.local (si i)) (.local (si a))) (.assign (.local (si a)) (.local (si b))))).run source =
      (.ok (.val (Source.intWrap (ty bits valid)
        (product G.pipeline (decide ((si i).toNat = (si b).toNat)) x z))),
        sourcePost G.pipeline source bits valid (si i) (si a) (si b) x z hx hz) ∧
    (operand G.pipeline bits (ti i) (ti a) (ti b)).run target =
      .ok (⟨targetPost G.pipeline target bits valid (ti i) (ti a) (ti b) x z hx hz,
        by cases G.pipeline <;> exact List.prefix_refl _⟩,
        .prim (integerValue (ty bits valid)
          ((ty bits valid).wrap (product G.pipeline (decide ((si i).toNat = (si b).toNat)) x z))
          ((ty bits valid).wrap_mem (product G.pipeline (decide ((si i).toNat = (si b).toNat)) x z)))) ∧
    IntValueRel (ty bits valid)
      (Source.intWrap (ty bits valid) (product G.pipeline (decide ((si i).toNat = (si b).toNat)) x z) :
        Source.Val E.layout (.int (ty bits valid)))
      (integerValue (ty bits valid)
        ((ty bits valid).wrap (product G.pipeline (decide ((si i).toNat = (si b).toNat)) x z))
        ((ty bits valid).wrap_mem (product G.pipeline (decide ((si i).toNat = (si b).toNat)) x z))) ∧
    IntegerLocalFamily (ty bits valid) si ti
      (sourcePost G.pipeline source bits valid (si i) (si a) (si b) x z hx hz).1
      (targetPost G.pipeline target bits valid (ti i) (ti a) (ti b) x z hx hz).env := by
  have actual := operand_run G.pipeline target bits valid (ti i) (ti a) (ti b) x z hx hz
    (family.read a x hx readA) (family.read b z hz readB)
  simp only [← family.aliases i b] at actual
  refine ⟨source_run G F fuel source bits valid (si i) (si a) (si b) x z hx hz readA readB,
    actual,integer_related _ _ _,?_⟩
  have post := family.assign_pair_all_aliases G.pipeline i a b x z hx hz readA readB
  cases order : G.pipeline
  · change IntegerLocalFamily (ty bits valid) si ti
      ((source.1.set (si a) (.int z hz)).set (si i) (.int z hz))
      (TEnv.set (ti i) (integerValue (ty bits valid) z hz)
        (TEnv.set (ti a) (integerValue (ty bits valid) z hz) target.env))
    simpa only [order,if_true] using post
  · change IntegerLocalFamily (ty bits valid) si ti
      ((source.1.set (si i) (.int x hx)).set (si a)
        (if (si i).toNat = (si b).toNat then .int x hx else .int z hz))
      (TEnv.set (ti a)
        (if (ti i).toNat = (ti b).toNat then integerValue (ty bits valid) x hx else integerValue (ty bits valid) z hz)
        (TEnv.set (ti i) (integerValue (ty bits valid) x hx) target.env))
    simpa only [order,reduceCtorEq,if_false,← family.aliases i b] using post

theorem extension {C : Contract} {Γ Δ : Ctx} (p : Roadmap.Pipeline)
    (s : State C Γ) (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (i a b : Idx Γ (.val .uint)) (x z : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hz : (ty bits valid).lo ≤ z ∧ z ≤ (ty bits valid).hi)
    (readA : TEnv.get a s.env = integerValue (ty bits valid) x hx)
    (readB : TEnv.get b s.env = integerValue (ty bits valid) z hz)
    (thin : Thin Γ Δ) (extra : TEnv C s.H Δ) :
    ((operand p bits i a b).wk thin).run (s.lift thin extra) =
      liftedT₂ thin extra (.ok ((⟨targetPost p s bits valid i a b x z hx hz,
        by cases p <;> exact List.prefix_refl _⟩ : Out C s.H Γ),
        SVal.prim (integerValue (ty bits valid)
          ((ty bits valid).wrap (product p (decide (i.toNat = b.toNat)) x z))
          ((ty bits valid).wrap_mem (product p (decide (i.toNat = b.toNat)) x z))))) := by
  rw [DeferredSource.Operand.run_wk,operand_run p s bits valid i a b x z hx hz readA readB]
  rfl

end Solidity.Lowering.V07.WrappedMultiplicationPair
