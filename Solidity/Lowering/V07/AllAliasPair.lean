import Solidity.Lowering.V07.DoubleAssignmentFamily

/-! Actual two assignments without a disjointness restriction. All observations
are reads of existing locals at their actual reached states. No new evaluator. -/
namespace Solidity.Lowering.V07

theorem source_written_read {D : Source.Layout} {Γ : Source.RCtx} {τ : Source.STy}
    (source : Source.Locals D Γ) (i b : Source.Idx Γ τ) (v : Source.Val D τ) :
    (source.set i v).get b = if i.toNat = b.toNat then v else source.get b := by
  by_cases h : i.toNat = b.toNat
  · have he := source_idx_injective i b h
    subst b
    simp only [source_locals_get_set, ite_true]
  · rw [source_locals_get_set_ne source i b v h,if_neg h]

theorem target_written_read {C : Contract} {H : HTy} {Γ : Ctx} {p : PrimTy}
    (target : TEnv C H Γ) (i b : Idx Γ (.val p)) (v : p.Denote) :
    TEnv.get b (TEnv.set i v target) = if i.toNat = b.toNat then v else TEnv.get b target := by
  by_cases h : i.toNat = b.toNat
  · have he := Idx.toNat_inj i b h
    subst b
    simp only [TEnv.get_set, ite_true]
  · rw [TEnv.get_set_ne i b v target h,if_neg h]

theorem source_assign_assign_pair_all_aliases {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (i a b : Source.Idx Γ τ) (x z : Source.Val E.layout τ)
    (readA : source.1.get a = x) (readB : source.1.get b = z) :
    (Source.evalPair G F (fuel+3) (.assign (.local i) (.local a))
      (.assign (.local a) (.local b))).run source =
      (.ok (.val (if G.pipeline = .legacy then z else x),
        .val (if G.pipeline = .legacy then z else if i.toNat = b.toNat then x else z)),
        (if G.pipeline = .legacy then ((source.1.set a z).set i z,source.2)
          else ((source.1.set i x).set a (if i.toNat = b.toNat then x else z),source.2))) := by
  rw [Source.evalPair]
  cases order : G.pipeline
  · rw [Source.Hoare.run_bind,source_assign_local_run G F fuel source a b z readB]
    dsimp only
    rw [Source.Hoare.run_bind,source_assign_local_run G F fuel
      (source.1.set a z,source.2) i a z (source_locals_get_set source.1 a z)]
    rfl
  · have reached : (source.1.set i x).get b = if i.toNat = b.toNat then x else z := by
      rw [source_written_read,readB]
    rw [Source.Hoare.run_bind,source_assign_local_run G F fuel source i a x readA]
    dsimp only
    rw [Source.Hoare.run_bind,source_assign_local_run G F fuel
      (source.1.set i x,source.2) a b _ reached]
    rfl

theorem assign_assign_prefix_all_aliases {C : Contract} {Γ : Ctx} {p : PrimTy}
    (pipeline : Roadmap.Pipeline) (target : State C Γ) (i a b : Idx Γ (.val p))
    (x z : p.Denote) (readA : TEnv.get a target.env = x)
    (readB : TEnv.get b target.env = z) :
    (assignAssignPrefix pipeline i a b).run target =
      .ok (⟨(if pipeline = .legacy then
          (((target.setLocal a z).setLocal i z).push z).push z
        else (((target.setLocal i x).setLocal a
          (if i.toNat = b.toNat then x else z)).push x).push
          (if i.toNat = b.toNat then x else z)),by split <;> exact List.prefix_refl _⟩) := by
  cases pipeline
  · change (do
      let r ← (Except.ok (TEnv.get b target.env) : TRes p.Denote)
      let capturedRight ← (Except.ok (TEnv.get a (TEnv.set a r target.env)) : TRes p.Denote)
      let l ← (Except.ok (TEnv.get a (TEnv.set a r target.env)) : TRes p.Denote)
      let capturedLeft ← (Except.ok (TEnv.get i (TEnv.set i l (TEnv.set a r target.env))) : TRes p.Denote)
      pure (⟨(((target.setLocal a r).setLocal i l).push capturedRight).push capturedLeft,List.prefix_refl _⟩ :
        Out C target.H (.val p :: .val p :: Γ))) = _
    rw [readB]
    simp only [TEnv.get_set]
    rfl
  · change (do
      let l ← (Except.ok (TEnv.get a target.env) : TRes p.Denote)
      let capturedLeft ← (Except.ok (TEnv.get i (TEnv.set i l target.env)) : TRes p.Denote)
      let r ← (Except.ok (TEnv.get b (TEnv.set i l target.env)) : TRes p.Denote)
      let capturedRight ← (Except.ok (TEnv.get a (TEnv.set a r (TEnv.set i l target.env))) : TRes p.Denote)
      pure (⟨(((target.setLocal i l).setLocal a r).push capturedLeft).push capturedRight,List.prefix_refl _⟩ :
        Out C target.H (.val p :: .val p :: Γ))) = _
    rw [readA]
    simp only [TEnv.get_set]
    change (do
      let r ← (Except.ok (TEnv.get b (TEnv.set i x target.env)) : TRes p.Denote)
      pure (⟨(((target.setLocal i x).setLocal a r).push x).push r,List.prefix_refl _⟩ :
        Out C target.H (.val p :: .val p :: Γ))) = _
    rw [target_written_read,readB]
    rfl

namespace IntegerLocalFamily
variable {D : Source.Layout} {srcΓ : Source.RCtx} {C : Contract} {H : HTy} {Γ : Ctx}
  {ι : Type} {t : Source.IntTy} {si : ι → Source.Idx srcΓ (.int t)}
  {ti : ι → Idx Γ (.val (integerPrim t))} {source : Source.Locals D srcΓ} {target : TEnv C H Γ}

/-- No inequality or reached-family hypothesis. Initial alias correspondence
selects the SAME reached RHS branch on Source and target sides. -/
theorem assign_pair_all_aliases (h : IntegerLocalFamily t si ti source target)
    (pipeline : Roadmap.Pipeline) (i a b : ι) (x z : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hz : t.lo ≤ z ∧ z ≤ t.hi)
    (readA : source.get (si a) = .int x hx) (readB : source.get (si b) = .int z hz) :
    IntegerLocalFamily t si ti
      (if pipeline = .legacy then (source.set (si a) (.int z hz)).set (si i) (.int z hz)
        else (source.set (si i) (.int x hx)).set (si a)
          (if (si i).toNat = (si b).toNat then .int x hx else .int z hz))
      (if pipeline = .legacy then
        TEnv.set (ti i) (integerValue t z hz) (TEnv.set (ti a) (integerValue t z hz) target)
        else TEnv.set (ti a)
          (if (si i).toNat = (si b).toNat then integerValue t x hx else integerValue t z hz)
          (TEnv.set (ti i) (integerValue t x hx) target)) := by
  have targetA := h.read a x hx readA
  have targetB := h.read b z hz readB
  by_cases order : pipeline = .legacy
  · simp only [order,if_true]
    simpa only [readB,targetB,source_locals_get_set,TEnv.get_set] using
      (h.write a b).write i a
  · simp only [order,if_false]
    simpa only [readA,targetA,source_written_read,target_written_read,readB,targetB,
      ← h.aliases i b] using (h.write i a).write a b

end IntegerLocalFamily
end Solidity.Lowering.V07
