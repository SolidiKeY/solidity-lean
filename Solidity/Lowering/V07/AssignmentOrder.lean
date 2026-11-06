import Solidity.Lowering.V07.AssignmentOperands

namespace Solidity.Lowering.V07

/-- Capture each operand at its actual evaluation point. The two top locals
have pipeline-dependent identities; their semantic positions are retained. -/
def assignReadPrefix {C : Contract} {Γ : Ctx} {p : PrimTy}
    (pipeline : Roadmap.Pipeline) (i a : Idx Γ (.val p)) :
    Prog C Γ (.val p :: .val p :: Γ) :=
  match pipeline with
  | .legacy =>
    .cons (.declLocal p (.user "v07_right") (some (.simple (.local i))))
      (.cons (.assignLocal (.there i) (.simple (.local (.there a))))
        (.cons (.declLocal p (.user "v07_left") (some (.simple (.local (.there i))))) .nil))
  | .viaIR =>
    .cons (.assignLocal i (.simple (.local a)))
      (.cons (.declLocal p (.user "v07_left") (some (.simple (.local i))))
        (.cons (.declLocal p (.user "v07_right") (some (.simple (.local (.there i))))) .nil))

theorem assign_read_prefix_run {C : Contract} {Γ : Ctx} {p : PrimTy}
    (pipeline : Roadmap.Pipeline) (target : State C Γ) (i a : Idx Γ (.val p))
    (assigned old : p.Denote) (readA : TEnv.get a target.env = assigned)
    (readI : TEnv.get i target.env = old) :
    (assignReadPrefix pipeline i a).run target =
      .ok (⟨((target.setLocal i assigned).push
        (if pipeline = .legacy then old else assigned)).push assigned,List.prefix_refl _⟩) := by
  cases pipeline
  · change (do
      let right ← (Except.ok (TEnv.get i target.env) : TRes p.Denote)
      let left ← (Except.ok (TEnv.get a target.env) : TRes p.Denote)
      let captured ← (Except.ok (TEnv.get i (TEnv.set i left target.env)) : TRes p.Denote)
      pure (⟨((target.setLocal i left).push right).push captured,List.prefix_refl _⟩ :
        Out C target.H (.val p :: .val p :: Γ))) = _
    rw [readI,readA]
    change Except.ok (⟨((target.setLocal i assigned).push old).push
      (TEnv.get i (TEnv.set i assigned target.env)),List.prefix_refl _⟩ :
      Out C target.H (.val p :: .val p :: Γ)) = _
    rw [TEnv.get_set]
    rfl
  · change (do
      let left ← (Except.ok (TEnv.get a target.env) : TRes p.Denote)
      let capturedLeft ← (Except.ok (TEnv.get i (TEnv.set i left target.env)) : TRes p.Denote)
      let capturedRight ← (Except.ok (TEnv.get i (TEnv.set i left target.env)) : TRes p.Denote)
      pure (⟨((target.setLocal i left).push capturedLeft).push capturedRight,List.prefix_refl _⟩ :
        Out C target.H (.val p :: .val p :: Γ))) = _
    rw [readA]
    change Except.ok (⟨((target.setLocal i assigned).push
      (TEnv.get i (TEnv.set i assigned target.env))).push
      (TEnv.get i (TEnv.set i assigned target.env)),List.prefix_refl _⟩ :
      Out C target.H (.val p :: .val p :: Γ)) = _
    rw [TEnv.get_set]
    rfl

theorem assignment_operand_transport {E : Source.Env} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (t : Source.IntTy)
    (i a : Source.Idx srcΓ (.int t)) (j b : Idx Γ (.val (integerPrim t)))
    (x : Int) (range : t.lo ≤ x ∧ x ≤ t.hi)
    (sourceRead : source.1.get a = .int x range)
    (targetRead : TEnv.get b target.env = integerValue t x range) :
    (Source.evalE G F (fuel+2) (.assign (.local i) (.local a))).run source =
      (.ok (.val (.int x range)),(source.1.set i (.int x range),source.2)) ∧
    (assignLocalOperand j b).run target =
      .ok (⟨target.setLocal j (integerValue t x range),List.prefix_refl _⟩,
        .prim (integerValue t x range)) ∧
    IntValueRel t (.int x range : Source.Val E.layout (.int t)) (integerValue t x range) :=
  ⟨source_assign_local_run G F fuel source i a _ sourceRead,
    assign_local_operand_run target j b _ targetRead,integer_related t x range⟩

end Solidity.Lowering.V07
