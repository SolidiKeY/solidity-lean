import Solidity.Lowering.V07.IntegerLocalFamily

/-! Actual two-effect operand order. Only the first destination must differ
from the second RHS cell; the two destinations may alias. No effect
commutation, whole-state purity or desired postrelation is assumed. -/
namespace Solidity.Lowering.V07

theorem source_assign_assign_pair {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (i a b : Source.Idx Γ τ) (x z : Source.Val E.layout τ)
    (readA : source.1.get a = x) (readB : source.1.get b = z)
    (separate : i.toNat ≠ b.toNat) :
    (Source.evalPair G F (fuel+3) (.assign (.local i) (.local a))
      (.assign (.local a) (.local b))).run source =
      (.ok (.val (if G.pipeline = .legacy then z else x),.val z),
        (if G.pipeline = .legacy then ((source.1.set a z).set i z,source.2)
          else ((source.1.set i x).set a z,source.2))) := by
  rw [Source.evalPair]
  cases order : G.pipeline
  · rw [Source.Hoare.run_bind,source_assign_local_run G F fuel source a b z readB]
    dsimp only
    rw [Source.Hoare.run_bind,source_assign_local_run G F fuel
      (source.1.set a z,source.2) i a z (source_locals_get_set source.1 a z)]
    rfl
  · have reached : (source.1.set i x).get b = z := by
      rw [source_locals_get_set_ne source.1 i b x separate,readB]
    rw [Source.Hoare.run_bind,source_assign_local_run G F fuel source i a x readA]
    dsimp only
    rw [Source.Hoare.run_bind,source_assign_local_run G F fuel
      (source.1.set i x,source.2) a b z reached]
    rfl

/-- Each assignment result is captured at its own reached state. In legacy
order head=left/second=right; viaIR head=right/second=left. -/
def assignAssignPrefix {C : Contract} {Γ : Ctx} {p : PrimTy}
    (pipeline : Roadmap.Pipeline) (i a b : Idx Γ (.val p)) :
    Prog C Γ (.val p :: .val p :: Γ) :=
  match pipeline with
  | .legacy =>
    .cons (.assignLocal a (.simple (.local b)))
      (.cons (.declLocal p (.user "v07_right") (some (.simple (.local a))))
        (.cons (.assignLocal (.there i) (.simple (.local (.there a))))
          (.cons (.declLocal p (.user "v07_left") (some (.simple (.local (.there i))))) .nil)))
  | .viaIR =>
    .cons (.assignLocal i (.simple (.local a)))
      (.cons (.declLocal p (.user "v07_left") (some (.simple (.local i))))
        (.cons (.assignLocal (.there a) (.simple (.local (.there b))))
          (.cons (.declLocal p (.user "v07_right") (some (.simple (.local (.there a))))) .nil)))

theorem assign_assign_prefix_run {C : Contract} {Γ : Ctx} {p : PrimTy}
    (pipeline : Roadmap.Pipeline) (target : State C Γ) (i a b : Idx Γ (.val p))
    (x z : p.Denote) (readA : TEnv.get a target.env = x)
    (readB : TEnv.get b target.env = z) (separate : i.toNat ≠ b.toNat) :
    (assignAssignPrefix pipeline i a b).run target =
      .ok (⟨(if pipeline = .legacy then
          (((target.setLocal a z).setLocal i z).push z).push z
        else (((target.setLocal i x).setLocal a z).push x).push z),by split <;> exact List.prefix_refl _⟩) := by
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
    rw [TEnv.get_set_ne i b x target.env separate,readB]
    rfl

/-- Numeric agreement determines the intrinsic primitive value at fixed
width/sign. This is content inversion, not identity inference. -/
theorem integer_relation_target {D : Source.Layout} (t : Source.IntTy) (x : Int)
    (range : t.lo ≤ x ∧ x ≤ t.hi) (v : (integerPrim t).Denote)
    (related : IntValueRel t (.int x range : Source.Val D (.int t)) v) :
    v = integerValue t x range := by
  obtain ⟨signed,bits,valid⟩ := t
  cases signed
  · change some x = some v.val at related
    apply Subtype.ext
    exact (Option.some.inj related).symm
  · change some x = some v.val at related
    apply Subtype.ext
    exact (Option.some.inj related).symm

namespace IntegerLocalFamily
variable {D : Source.Layout} {srcΓ : Source.RCtx} {C : Contract} {H : HTy} {Γ : Ctx}
  {ι : Type} {t : Source.IntTy} {si : ι → Source.Idx srcΓ (.int t)}
  {ti : ι → Idx Γ (.val (integerPrim t))} {source : Source.Locals D srcΓ} {target : TEnv C H Γ}

theorem read (h : IntegerLocalFamily t si ti source target) (k : ι) (x : Int)
    (range : t.lo ≤ x ∧ x ≤ t.hi) (initial : source.get (si k) = .int x range) :
    TEnv.get (ti k) target = integerValue t x range := by
  have related := h.values k
  rw [initial] at related
  exact integer_relation_target t x range _ related

theorem separate (h : IntegerLocalFamily t si ti source target) (i b : ι)
    (different : (si i).toNat ≠ (si b).toNat) : (ti i).toNat ≠ (ti b).toNat :=
  fun eq => different ((h.aliases i b).mpr eq)

end IntegerLocalFamily
end Solidity.Lowering.V07
