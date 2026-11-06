import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducerRefTupleTyped

/-! Checked tuple-call emission from the existing intrinsic frame expansion.
Only existing instructions and intrinsic source relations are used. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducerRef.Tuple
open Evm Evm.Memory

def expand {C : Contract} {Γ ps rs Γf : Ctx} (args : Args C Γ ps)
    (bs : RetBinders rs) (body : Prog C (rs ++ ps) Γf) : Prog C Γ (rs ++ (ps ++ Γ)) :=
  args.declsThen (bs.declsThen
    (.cons (.block (body.wk (Thin.keepAll rs (Thin.atop ps Γ))).2.2) .nil))

theorem expand_run {C : Contract} {Γ ps rs Γf : Ctx} (f : Name)
    (args : Args C Γ ps) (bs : RetBinders rs) (body : Prog C (rs ++ ps) Γf)
    (σ : State C Γ) :
    ((expand args bs body).runSt σ).map
      (State.thin (Thin.keepAll rs (Thin.ofExt (Ext.append Γ ps)))) =
      (.call f args (.rets bs) body : Stmt C Γ (rs ++ Γ)).runSt σ :=
  Stmt.runSt_callRets f args bs body σ

abbrev Emitter : Type :=
  ∀ {C : Contract} {Γ ps rs Γf : Ctx} {b : Nat} {F : Frag Γ}
    (f : Name) (args : Args C Γ ps) (bs : RetBinders rs)
    (body : Prog C (rs ++ ps) Γf),
    Composition.Program b F (expand args bs body) →
    Composition.Statement b F (.call f args (.rets bs) body)

private theorem ok_of_state {C : Contract} {Γ Δ : Ctx} {σ : State C Γ}
    {res : TRes (Solidity.Out C σ.H Δ)} {τ : State C Δ}
    (actual : res.map (·.st) = .ok τ) : ∃ o, res = .ok o ∧ o.st = τ := by
  cases res with
  | error halt => cases actual
  | ok out => exact ⟨out, rfl, Except.ok.inj actual⟩

private theorem error_of_state {C : Contract} {Γ Δ : Ctx} {σ : State C Γ}
    {res : TRes (Solidity.Out C σ.H Δ)}
    (actual : res.map (·.st) = .error .revert) : res = .error .revert := by
  cases res with
  | error halt => cases actual; rfl
  | ok out => cases actual

/-- Checked tuple calls use the actual existing source expansion, exact
reached allocation cost, and typed downward result copies. -/
def emit : Emitter := by
  intro C Γ ps rs Γf b F f args bs body expanded
  refine { checked := {
    frag := resultFrag bs ((expanded.checked.frag.restrict (ps ++ Γ)).restrict Γ)
    code := expanded.checked.code ++ code b Γ ps bs
    need := max expanded.checked.need (rs ++ (ps ++ Γ)).length
    cost := expanded.checked.cost
    allocates := expanded.checked.allocates
    zeroCost := expanded.checked.zeroCost
    sound := ?_ }, safe := ?_ }
  · intro L frame σ base m represented room capacity
    have prefixRoom : b + expanded.checked.need ≤ frame := by omega
    have allRoom : b + (rs ++ (ps ++ Γ)).length ≤ frame := by omega
    have copyRoom : b + Γ.length + rs.length ≤ frame := by
      simp only [List.length_append] at allRoom
      omega
    have ordered : b + Γ.length ≤ b + Γ.length + ps.length := by omega
    rcases expanded.checked.sound represented prefixRoom capacity with
      ⟨out, mid, addresses, source, executed, reached, stack, extension, growth⟩ | ⟨source, executed⟩
    · obtain ⟨last, copied, copiedStack, values, outside, fields⟩ :=
        copy_run rs.length (b + Γ.length + ps.length) (b + Γ.length) mid ordered
      have copyRun : Evm.run (code b Γ ps bs) mid = .ok last 0 := copied
      let τ := out.st.thin (Thin.keepAll rs (Thin.ofExt (Ext.append Γ ps)))
      have sourceState : (.call f args (.rets bs) body : Stmt C Γ (rs ++ Γ)).runSt σ = .ok τ := by
        rw [← expand_run f args bs body σ]
        change ((Prog.run σ (expand args bs body)).map (·.st)).map _ = _
        rw [source]
        rfl
      obtain ⟨result, resultRun, resultState⟩ := ok_of_state sourceState
      refine .inl ⟨result, last, addresses, resultRun, ?_, ?_, copiedStack.trans stack, extension, ?_⟩
      · rw [Evm.run_append_ok executed]
        exact copyRun
      · rw [resultState]
        exact compacted bs out.st addresses mid last reached copyRun
      · intro cursor positive allocator space
        rw [resultState]
        exact copy_allocator rs.length (b + Γ.length + ps.length) (b + Γ.length) mid last
          (growth cursor positive allocator space) (by omega) copyRoom copied
    · have sourceState : (.call f args (.rets bs) body : Stmt C Γ (rs ++ Γ)).runSt σ =
          .error .revert := by
        rw [← expand_run f args bs body σ]
        change ((Prog.run σ (expand args bs body)).map (·.st)).map _ = _
        rw [source]
        rfl
      exact .inr ⟨error_of_state sourceState, Evm.run_append_revert executed⟩
  · intro L frame lo σ base m target represented room boundary capacity actual
    change b + max expanded.checked.need (rs ++ (ps ++ Γ)).length ≤ lo at room
    have prefixRoom : b + expanded.checked.need ≤ lo := by omega
    have allRoom : b + (rs ++ (ps ++ Γ)).length ≤ lo := by omega
    have copyEnd : b + Γ.length + rs.length ≤ lo := by
      simp only [List.length_append] at allRoom
      omega
    rcases expanded.checked.sound represented (by omega) capacity with
      ⟨out, mid, addresses, source, executed, reached, stack, extension, growth⟩ | ⟨source, executed⟩
    · have remaining : Evm.run (code b Γ ps bs) mid = .ok target 0 := by
        change Evm.run (expanded.checked.code ++ code b Γ ps bs) m = _ at actual
        rw [Evm.run_append_ok executed] at actual
        exact actual
      obtain ⟨last, copied, copiedStack, values, outside, fields⟩ :=
        copy_run rs.length (b + Γ.length + ps.length) (b + Γ.length) mid (by omega)
      have same : last = target := (Evm.Out.ok.inj (copied.symm.trans remaining)).1
      subst last
      exact Footprint.words_trans (expanded.safe represented prefixRoom boundary capacity executed)
        (fun address lower upper => outside address (.inr (by omega)))
    · have failed : Evm.run (expanded.checked.code ++ code b Γ ps bs) m = .revert :=
        Evm.run_append_revert executed
      change Evm.run (expanded.checked.code ++ code b Γ ps bs) m = _ at actual
      rw [failed] at actual
      contradiction

#print axioms emit

end Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducerRef.Tuple
