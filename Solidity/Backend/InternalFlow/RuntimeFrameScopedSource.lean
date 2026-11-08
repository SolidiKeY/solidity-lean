import Solidity.Semantics.Run

/-! Exact elimination of a scoped, unused default local around an actual
body. These are equations of the existing source evaluator, for its full
result including every halt class, not a replacement evaluator or frame
preservation assumption. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScopedSource

/-- The body executes before the unused local is introduced. The enclosing
block removes that local; all body state and halt observations survive. -/
def decorate {C : Contract} {Γ : Ctx} (body : Prog C Γ Γ) (p : PrimTy) (name : Var) : Prog C Γ Γ :=
 .cons (.block (.cons (.block body) (.cons (.declLocal p name none) .nil))) .nil

theorem decorate_run {C : Contract} {Γ : Ctx} (body : Prog C Γ Γ) (p : PrimTy) (name : Var) :
 (decorate body p name).runR=body.runR := by
 funext σ
 have outer : (Prog.cons (.block body) (.cons (.declLocal p name none) .nil)).ext=Ext.push Ext.refl := Subsingleton.elim _ _
 have scope : body.ext=Ext.refl := Subsingleton.elim _ _
 change TRun.seq (TRun.block _ (TRun.seq (TRun.block body.ext body.runR)
   (TRun.seq (TRun.declLocal p none) TRun.nil))) TRun.nil σ=body.runR σ
 rw [outer,scope]
 unfold TRun.seq TRun.block
 cases actual : body.runR σ with
 | error halt => simp only [actual,Except.map]
 | ok out =>
   cases out
   simp only [actual,Except.map,TRun.declLocal,TRun.nil]
   rfl

/-- Call execution observes exactly the same arguments, return binder,
heap-extension and full result after this checked local unwind. -/
theorem call_run {C : Contract} {Γ Δ ps rs : Ctx} (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
 (body : Prog C (rs++ps) (rs++ps)) (p : PrimTy) (name : Var) :
 TRun.call args ret (decorate body p name).ext (decorate body p name).runR=
 TRun.call args ret body.ext body.runR := by
 have scope : (decorate body p name).ext=body.ext := Subsingleton.elim _ _
 rw [scope,decorate_run]

end Solidity.Backend.InternalFlow.RuntimeFrame.ScopedSource
