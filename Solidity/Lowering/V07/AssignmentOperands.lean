import Solidity.Lowering.V07.Operands

/-! Actual integer local assignment and scoped result capture. No source
admission or general effect commutation is assumed. -/
namespace Solidity.Lowering.V07

theorem source_locals_get_set {D : Source.Layout} {Γ : Source.RCtx} {τ : Source.STy}
    (locals : Source.Locals D Γ) (i : Source.Idx Γ τ) (v : Source.Val D τ) :
    (locals.set i v).get i = v := by
  induction i with
  | here => cases locals; rfl
  | there i ih => cases locals with | cons _ rest => exact ih rest v

theorem source_assign_local_run {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (i a : Source.Idx Γ τ) (v : Source.Val E.layout τ)
    (read : source.1.get a = v) :
    (Source.evalE G F (fuel+2) (.assign (.local i) (.local a))).run source =
      (.ok (.val v),(source.1.set i v,source.2)) := by
  change (Except.ok (Source.RVal.val (source.1.get a)),
    (source.1.set i (source.1.get a),source.2)) = _
  rw [read]

/-- A read alias sees the old cell under legacy and the reached cell via IR.
The returned pair ALWAYS retains semantic left/right operand positions. -/
theorem source_assign_read_pair {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (i a : Source.Idx Γ τ) (assigned old : Source.Val E.layout τ)
    (readA : source.1.get a = assigned) (readI : source.1.get i = old) :
    (Source.evalPair G F (fuel+3) (.assign (.local i) (.local a)) (.local i)).run source =
      (.ok (.val assigned,.val (if G.pipeline = .legacy then old else assigned)),
        (source.1.set i assigned,source.2)) := by
  have firstRead : (Source.evalE G F (fuel+2) (.local i)).run source =
      (.ok (.val old),source) := by
    change (Except.ok (Source.RVal.val (source.1.get i)),source) = _
    rw [readI]
  have reachedRead : (Source.evalE G F (fuel+2) (.local i)).run
      (source.1.set i assigned,source.2) =
      (.ok (.val assigned),(source.1.set i assigned,source.2)) := by
    change (Except.ok (Source.RVal.val ((source.1.set i assigned).get i)),_) = _
    rw [source_locals_get_set]
  rw [Source.evalPair]
  cases order : G.pipeline
  · rw [Source.Hoare.run_bind,firstRead]
    dsimp only
    rw [Source.Hoare.run_bind,source_assign_local_run G F fuel source i a assigned readA]
    rfl
  · rw [Source.Hoare.run_bind,source_assign_local_run G F fuel source i a assigned readA]
    dsimp only
    rw [Source.Hoare.run_bind,reachedRead]
    rfl

/-- The typed context extension, not the printed temporary name, makes the
capture fresh. Its value is read by Operand.run before this binder is dropped. -/
def assignLocalOperand {C : Contract} {Γ : Ctx} {p : PrimTy}
    (i a : Idx Γ (.val p)) : DeferredSource.Operand C Γ (.prim p) :=
  ⟨.val p :: Γ,
    .cons (.assignLocal i (.simple (.local a)))
      (.cons (.declLocal p (.user "v07_result") (some (.simple (.local i)))) .nil),
    .val (.simple (.local .here))⟩

theorem assign_local_operand_run {C : Contract} {Γ : Ctx} {p : PrimTy}
    (target : State C Γ) (i a : Idx Γ (.val p)) (v : p.Denote)
    (read : TEnv.get a target.env = v) :
    (assignLocalOperand i a).run target =
      .ok (⟨target.setLocal i v,List.prefix_refl _⟩,.prim v) := by
  unfold assignLocalOperand DeferredSource.Operand.run
  change (do
    let x ← (Except.ok (TEnv.get a target.env) : TRes p.Denote)
    let y ← (Except.ok (TEnv.get i (TEnv.set i x target.env)) : TRes p.Denote)
    pure ((⟨target.setLocal i x,List.prefix_refl _⟩ : Out C target.H Γ),SVal.prim y)) = _
  rw [read]
  change Except.ok ((⟨target.setLocal i v,List.prefix_refl _⟩ : Out C target.H Γ),
    SVal.prim (TEnv.get i (TEnv.set i v target.env))) = _
  rw [TEnv.get_set]

end Solidity.Lowering.V07
