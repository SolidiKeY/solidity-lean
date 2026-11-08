import Solidity.Lowering.V07.P12ContextExtension

/-! Execute an arbitrary effectful primitive operand and store its captured value before private locals are dropped; caller writes, heap growth and halts are retained. The existing Boolean API remains unchanged. This native helper asserts no Source admission or whole compiler pass. -/
namespace Solidity.Lowering.G17

variable {C : Contract} {Γ : Ctx}

def storeOperand (i : Idx Γ (.val .bool))
    (e : DeferredSource.Operand C Γ (.prim .bool)) : Stmt C Γ Γ :=
  match e.value with
  | .val v => .block (e.code.join (.cons (.assignLocal (i.ext e.code.ext) v) .nil))

private theorem drop_set {p : PrimTy} {H : HTy} {Δ : Ctx} (h : Ext Γ Δ)
    (i : Idx Γ (.val p)) (b : p.Denote) (env : TEnv C H Δ) :
    TEnv.drop h (TEnv.set (i.ext h) b env) = TEnv.set i b (TEnv.drop h env) := by
  induction h with
  | refl => rfl
  | push h ih => exact ih env.2

def storePrimitiveOperand {p : PrimTy} (i : Idx Γ (.val p))
    (e : DeferredSource.Operand C Γ (.prim p)) : Stmt C Γ Γ :=
  match e.value with
  | .val v => .block (e.code.join (.cons (.assignLocal (i.ext e.code.ext) v) .nil))

/-- Universal primitive capture, including failed prefixes/reads; controls reject lost temporaries, caller effects and ignored halts. -/
theorem storePrimitiveOperand_run {p : PrimTy} (i : Idx Γ (.val p))
    (e : DeferredSource.Operand C Γ (.prim p)) (target : State C Γ) :
    (storePrimitiveOperand i e).run target = (e.run target).map (fun (out,value) =>
      match value with
      | .prim b => (⟨out.st.setLocal i b,out.ext⟩ : Out C target.H Γ)) := by
  obtain ⟨Δ,code,value⟩ := e
  cases value with
  | val v =>
    unfold storePrimitiveOperand DeferredSource.Operand.run
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

theorem storePrimitive_fresh_run {p : PrimTy} (e : DeferredSource.Operand C Γ (.prim p))
    (target : State C Γ) (previous : p.Denote) :
    (storePrimitiveOperand .here (e.wk (.drop .refl))).run
      (target.push (t := .val p) previous) =
    (e.run target).map (fun (out,value) => match value with
      | .prim b => (⟨out.st.push (t := .val p) b,out.ext⟩ : Out C target.H (.val p :: Γ))) := by
  rw [storePrimitiveOperand_run]
  have weak := DeferredSource.Operand.run_wk e (.drop (t := .val p) .refl)
    target (previous,target.env)
  change (e.wk (.drop .refl)).run (target.push (t := .val p) previous) = _ at weak
  rw [weak]
  cases run : e.run target with
  | error err => rfl
  | ok result =>
    obtain ⟨out,value⟩ := result
    cases value with
    | prim b => rfl

theorem storeOperand_run (i : Idx Γ (.val .bool))
    (e : DeferredSource.Operand C Γ (.prim .bool)) (target : State C Γ) :
    (storeOperand i e).run target = (e.run target).map (fun (out,value) =>
      match value with
      | .prim b => (⟨out.st.setLocal i b,out.ext⟩ : Out C target.H Γ)) := by
  have same : storeOperand i e = storePrimitiveOperand i e := by
    cases e with
    | mk Δ code value => cases value <;> rfl
  rw [same,storePrimitiveOperand_run]
  cases run : e.run target with
  | error err => rfl
  | ok result =>
    obtain ⟨out,value⟩ := result
    cases value with
    | prim b => rfl

namespace PrimitiveCaptureControls
private abbrev captureContract := (default : Solidity.Contract)
private abbrev Context : Ctx := [.val .uint,.val .uint]
private def zero : PrimTy.uint.Denote := ⟨0,by decide⟩
private def seven : PrimTy.uint.Denote := ⟨7,by decide⟩
private def nine : PrimTy.uint.Denote := ⟨9,by decide⟩
private def target : State captureContract Context :=
  {(State.init captureContract) with env := (zero,⟨42,by decide⟩,())}
private def operand : DeferredSource.Operand captureContract Context (.prim .uint) :=
  ⟨.val .uint :: Context,
    .cons (.declLocal .uint (.user "private_result") (some (.simple (.lit 7 (by decide)))))
      (.cons (.assignLocal (.there (.there .here)) (.simple (.lit 9 (by decide)))) .nil),
    .val (.simple (.local .here))⟩
private def failing : DeferredSource.Operand captureContract Context (.prim .uint) :=
  ⟨_,.cons .revert .nil,.val (.simple (.lit 0 (by decide)))⟩

/-- The result lives only in a private temporary while another caller slot changes; rejects scope-exit reads, lost caller writes and ignored halts for ordinary/fresh capture. -/
theorem capture_control :
    (storePrimitiveOperand .here operand).run target =
      .ok (⟨(target.setLocal (.there .here) nine).setLocal .here seven,List.prefix_refl _⟩) ∧
    (storePrimitiveOperand .here (operand.wk (.drop .refl))).run (target.push (t := .val .uint) nine) =
      .ok (⟨(target.setLocal (.there .here) nine).push (t := .val .uint) seven,List.prefix_refl _⟩) ∧
    (storePrimitiveOperand .here failing).run target = .error .revert := by
  constructor
  · rw [storePrimitiveOperand_run]
    rfl
  · constructor
    · rw [storePrimitive_fresh_run]
      rfl
    · rw [storePrimitiveOperand_run]
      rfl

#print axioms capture_control
end PrimitiveCaptureControls

#print axioms drop_set
#print axioms storeOperand_run
#print axioms storePrimitiveOperand_run
#print axioms storePrimitive_fresh_run

end Solidity.Lowering.G17
