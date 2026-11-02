import Solidity.Backend.InternalFlow.RuntimeFrameTransport

/-! Caller-frame equations derived from actual intrinsic call execution.
Argument failure, result entry and body execution use the existing semantics;
no source-to-target simulation or new evaluator is assumed. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.CallAgreement
open Evm Evm.Memory
variable {C : Contract} {Γ Δ ps rs Γf : Ctx}

/-- Invert actual success into the same evaluated arguments, entered frame,
body output and exported caller frame used by the existing call semantics. -/
theorem output_of_call (f : Name) (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
 (body : Prog C (rs ++ ps) Γf) (caller : State C Γ) (out : Solidity.Out C caller.H Δ)
 (source : (.call f args ret body : Stmt C Γ Δ).run caller=.ok out) :
 ∃ (arguments : TEnv C caller.H ps)
   (bodyOut : Solidity.Out C (ret.enterT (caller.withEnv arguments)).st.H Γf),
 args.evalT caller=.ok arguments ∧
 body.runR (ret.enterT (caller.withEnv arguments)).st=.ok bodyOut ∧
 out=exported ret body.ext caller arguments bodyOut := by
 change TRun.call args ret body.ext body.runR caller=.ok out at source
 unfold TRun.call at source
 cases evaluated : args.evalT caller with
 | error halt =>
   simp only [evaluated,error_bind] at source
   cases source
 | ok arguments =>
   simp only [evaluated,ok_bind] at source
   cases executed : body.runR (ret.enterT (caller.withEnv arguments)).st with
   | error halt =>
     simp only [executed,error_bind] at source
     cases source
   | ok bodyOut =>
     simp only [executed,ok_bind] at source
     exact ⟨arguments,bodyOut,rfl,executed,(Except.ok.inj source).symm⟩

theorem none_tail (f : Name) (args : Args C Γ ps) (body : Prog C ps Γf)
 (caller : State C Γ) (out : Solidity.Out C caller.H Γ)
 (source : (.call f args .none body : Stmt C Γ Γ).run caller=.ok out) :
 TEnv.drop (.refl : Ext Γ Γ) out.st.env=TEnv.wk out.ext Γ caller.env := by
 obtain ⟨arguments,bodyOut,evaluated,executed,rfl⟩ := output_of_call f args .none body caller out source
 rfl

theorem memory_tail (f : Name) (args : Args C Γ ps) (R : RefTy) (name : Var)
 (hd : (Ty.ref R).defaultOkS=true) (hm : (Ty.ref R).mapFree=true)
 (body : Prog C (.mem R :: ps) Γf) (caller : State C Γ)
 (out : Solidity.Out C caller.H (.mem R :: Γ))
 (source : (.call f args (.mem R name hd hm) body : Stmt C Γ (.mem R :: Γ)).run caller=.ok out) :
 TEnv.drop (.push .refl : Ext Γ (.mem R :: Γ)) out.st.env=TEnv.wk out.ext Γ caller.env := by
 obtain ⟨arguments,bodyOut,evaluated,executed,rfl⟩ := output_of_call f args (.mem R name hd hm) body caller out source
 rfl

theorem singleton_success {s : Stmt C Γ Δ} {caller : State C Γ}
 {out : Solidity.Out C caller.H Δ} (source : s.run caller=.ok out) :
 (Prog.cons s .nil).run caller=.ok out := by
 rw [Prog.run_cons_ok source,Prog.run_nil]
 rfl

theorem singleton_failure {s : Stmt C Γ Δ} {caller : State C Γ} {halt : THalt}
 (source : s.run caller=.error halt) : (Prog.cons s .nil).run caller=.error halt := by
 change TRun.seq s.runR TRun.nil caller=_
 simp only [TRun.seq,source]

end Solidity.Backend.InternalFlow.RuntimeFrame.CallAgreement
