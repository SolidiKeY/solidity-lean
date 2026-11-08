import Solidity.Lowering.V07.P12ContextExtension

/-! Execute an arbitrary effectful Boolean operand and store its captured value. The prefix remains scoped; caller writes, heap growth and halts are retained. This helper does not assert admitted-syntax coverage or a whole compiler pass. -/
namespace Solidity.Lowering.G17

variable {C : Contract} {Γ : Ctx}

/-- The value is read before the operand's private locals are dropped. -/
def storeOperand (i : Idx Γ (.val .bool))
    (e : DeferredSource.Operand C Γ (.prim .bool)) : Stmt C Γ Γ :=
  match e.value with
  | .val v => .block (e.code.join (.cons (.assignLocal (i.ext e.code.ext) v) .nil))

private theorem drop_set {H : HTy} {Δ : Ctx} (h : Ext Γ Δ)
    (i : Idx Γ (.val .bool)) (b : Bool) (env : TEnv C H Δ) :
    TEnv.drop h (TEnv.set (i.ext h) b env) = TEnv.set i b (TEnv.drop h env) := by
  induction h with
  | refl => rfl
  | push h ih => exact ih env.2

/-- A universal ordinary-run equation, including failed prefixes and reads. -/
theorem storeOperand_run (i : Idx Γ (.val .bool))
    (e : DeferredSource.Operand C Γ (.prim .bool)) (target : State C Γ) :
    (storeOperand i e).run target = (e.run target).map (fun (out,value) =>
      match value with
      | .prim b => (⟨out.st.setLocal i b,out.ext⟩ : Out C target.H Γ)) := by
  obtain ⟨Δ,code,value⟩ := e
  cases value with
  | val v =>
    unfold storeOperand DeferredSource.Operand.run
    change TRun.block (code.join (.cons (.assignLocal (i.ext code.ext) v) .nil)).ext
      (code.join (.cons (.assignLocal (i.ext code.ext) v) .nil)).runR target = _
    unfold TRun.block
    have joined := DeferredSource.join_run code (.cons (.assignLocal (i.ext code.ext) v) .nil) target
    change (code.join (.cons (.assignLocal (i.ext code.ext) v) .nil)).runR target = _ at joined
    rw [joined]
    simp only [Prog.run]
    unfold TRun.seq
    cases prelude : code.runR target with
    | error err => rfl
    | ok out =>
      have tail : (Prog.cons (.assignLocal (i.ext code.ext) v) .nil).runR out.st =
          (v.evalT out.st).map (fun b =>
            (⟨out.st.setLocal (i.ext code.ext) b,List.prefix_refl _⟩ : Out C out.st.H Δ)) := by
        change TRun.seq (TRun.assignLocal _ v) TRun.nil out.st = _
        unfold TRun.seq TRun.assignLocal TRun.nil
        cases v.evalT out.st <;> rfl
      dsimp only []
      rw [tail]
      cases read : v.evalT out.st with
      | error err => simp only [Src.valueT,read,bind,Except.bind,Except.map]
      | ok b =>
        simp only [Src.valueT,read,bind,Except.bind,Except.map]
        simp only [DeferredSource.join_ext]
        change Except.ok (⟨(out.st.setLocal (i.ext code.ext) b).drop code.ext,out.ext⟩ : Out C target.H Γ) =
          .ok ⟨(out.st.drop code.ext).setLocal i b,out.ext⟩
        simp only [State.drop,State.setLocal,drop_set]

#print axioms drop_set
#print axioms storeOperand_run

end Solidity.Lowering.G17
