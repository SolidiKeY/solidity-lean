import Solidity.Backend.InternalFlow.RuntimeFrameV3EffectfulScalarCall
import Solidity.Backend.InternalFlow.RuntimeFrameV3SameCallControls

/-! The actual callee write fails after successful arguments, before scalar
recursion even at source index zero. Checked target writer failure absorbs
the continuation. Reverting results supply no failed state or world rollback. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulScalarFailure
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
abbrev A : RefTy := EffectfulScalarSource.A

def statement {C : Contract} {Γ : Ctx} (reference : Idx Γ (.mem A)) : Stmt C Γ Γ :=
 .assignMem (.index .dyn (.var reference rfl) (.simple (.lit 0 rfl)))
   (.val (.simple (.lit 37 rfl)))

theorem write_failure {C : Contract} {Γ : Ctx} (caller : State C Γ)
 (reference : Idx Γ (.mem A)) (ref : HRef caller.H A)
 (alias : TEnv.get reference caller.env=some ref)
 (actual : caller.heap.writeAddr (.index ref .dyn (countValue 0 W_pos)) EffectfulScalarSource.replacement=none) :
 (statement reference).run caller=.error .revert := by
 change TRun.assignMem (.index .dyn (.var reference rfl) (.simple (.lit 0 rfl)))
   (.val (.simple (.lit 37 rfl))) caller=_
 simp only [TRun.assignMem,MSrc.mvalT,Val.evalT,Simple.evalT,MLoc.addrT,MPath.mvalT,alias,ok_bind]
 simp only [pure,Except.pure,bind,Except.bind]
 change (do
   let heap ← TRes.ofOpt (caller.heap.writeAddr (.index ref .dyn (countValue 0 W_pos)) EffectfulScalarSource.replacement)
   pure (⟨caller.withHeap heap,List.prefix_refl _⟩ : Solidity.Out C caller.H Γ))=_
 rw [actual]
 rfl

/-- Successful arguments do not hide the body-write failure at index zero. -/
theorem call_failure {C : Contract} {Γ : Ctx} (function : Name)
 (args : Args C Γ (Parameters A)) (destination : Idx Γ (.val .uint))
 (depth : Nat) (caller : State C Γ) (count : Nat) (bound : count<W)
 (ref : HRef caller.H A)
 (evaluated : args.evalT caller=.ok (countValue count bound,(some ref,())))
 (actual : caller.heap.writeAddr (.index ref .dyn (countValue 0 W_pos)) EffectfulScalarSource.replacement=none) :
 (EffectfulScalarSource.invoke function args destination depth).run caller=.error .revert := by
 let child : State C (Frame A) :=
   (caller.withEnv (Δ:=Parameters A) (countValue count bound,(some ref,()))).push (t:=.val .uint) (PrimTy.dflt .uint)
 have failed := write_failure child (.there (.there .here)) ref rfl actual
 have body : (EffectfulScalarSource.body depth).run child=.error .revert := by
   change TRun.seq EffectfulScalarSource.write.runR (ScalarRecursiveSource.body A rfl depth).runR child=_
   simp only [TRun.seq,show EffectfulScalarSource.write.runR child=.error .revert from failed]
 change TRun.call args (.val .uint (.user "result") (some destination))
   (EffectfulScalarSource.body (C:=C) depth).ext (EffectfulScalarSource.body depth).runR caller=_
 unfold TRun.call
 simp only [evaluated,ok_bind,CallRet.enterT]
 change (do
   let out ← (EffectfulScalarSource.body depth).run child
   pure (exported (ps:=Parameters A) (.val .uint (.user "result") (some destination))
     (EffectfulScalarSource.body (C:=C) depth).ext caller (countValue count bound,(some ref,())) out))=_
 rw [body]
 rfl

def selected {C : Contract} {Γ : Ctx} (b : Nat) (F : Frag Γ) (reference : Idx Γ (.mem A)) :
 CompiledStmt b F (statement (C:=C) reference) :=
 (Memory.compileStmt b F (statement reference)).get (by rfl)

theorem public_root {C : Contract} {Γ : Ctx} (b : Nat) (F : Frag Γ) (reference : Idx Γ (.mem A)) :
 Memory.compileStmt b F (statement (C:=C) reference)=some (selected b F reference) := rfl

/-- Actual public write soundness absorbs any continuation; no unreachable
continuation Room or failed output State is assumed. -/
theorem target_suffix {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Frag Γ}
 (caller : State C Γ) (reference : Idx Γ (.mem A)) (ref : HRef caller.H A)
 (alias : TEnv.get reference caller.env=some ref)
 (actual : caller.heap.writeAddr (.index ref .dyn (countValue 0 W_pos)) EffectfulScalarSource.replacement=none)
 (base : Nat → Fin W) (machine : Machine) (repr : StateRepr L b frame F caller base machine)
 (room : b+frameNeedStmt (statement (C:=C) reference)≤frame) (suffix : List Instr) :
 run ((selected (C:=C) b F reference).code++suffix) machine=.revert := by
 have result := (selected (C:=C) b F reference).cert.correct repr room (.inl rfl)
 rcases result with ⟨out,last,addresses,source,target,represented,stack,extended,growth⟩ | ⟨source,target⟩
 · rw [write_failure caller reference ref alias actual] at source
   cases source
 · exact run_append_revert target

namespace Client
open DisjointScalarReturn.Client (Γ F reference)

theorem arguments : (DisjointScalarEntry.args rfl reference DisjointScalarReturn.Client.count).evalT SameCallInputs.caller=
 .ok (countValue 3 (by decide),(some SameCallInputs.fresh,())) := rfl

theorem actual_write_failure : SameCallInputs.caller.heap.writeAddr
 (.index SameCallInputs.fresh .dyn (countValue 0 W_pos)) EffectfulScalarSource.replacement=none := by
 with_unfolding_all rfl

theorem source (depth : Nat) : (EffectfulScalarCall.invoke depth).run SameCallInputs.caller=.error .revert :=
 call_failure "effectfulScalar" (DisjointScalarEntry.args rfl reference DisjointScalarReturn.Client.count)
 .here depth SameCallInputs.caller 3 (by decide) SameCallInputs.fresh arguments actual_write_failure

theorem write_code : (selected (C:=SameCallInputs.C) 1 F reference).code=EffectfulScalarCall.writeCode := rfl

theorem target : run EffectfulScalarCall.image SameCallInputs.machine=.revert := by
 have failed := target_suffix SameCallInputs.caller reference SameCallInputs.fresh rfl actual_write_failure
   SameCallInputs.addresses SameCallInputs.machine SameCallInputs.reached.2.2.1 (by decide)
   (DisjointScalarReturn.code 1 5 reference DisjointScalarReturn.Client.value (.here : Idx Γ (.val .uint)) 9 8)
 rw [write_code] at failed
 exact failed

def program (depth : Nat) : Prog SameCallInputs.C Γ Γ :=
 .cons SameCallInputs.preparation (.cons (EffectfulScalarCall.invoke depth) .nil)

theorem whole_source (depth : Nat) : (program depth).run SameCallInputs.origin=.error .revert := by
 rw [program,Prog.run_cons_ok SameCallInputs.reached.1]
 change (TRun.seq (EffectfulScalarCall.invoke depth).runR TRun.nil SameCallInputs.caller).map _=_
 simp only [TRun.seq,show (EffectfulScalarCall.invoke depth).runR SameCallInputs.caller=.error .revert from source depth,Except.map]

theorem whole_target :
 run (SameCallInputs.checked.code++EffectfulScalarCall.image) SameCallInputs.before=.revert :=
 (run_append_ok SameCallInputs.reached.2.1).trans target

theorem arguments_not_failure (halt : THalt) :
 (DisjointScalarEntry.args rfl reference DisjointScalarReturn.Client.count).evalT SameCallInputs.caller≠.error halt := by
 rw [arguments]
 intro impossible
 cases impossible

theorem source_not_exhausted (depth : Nat) :
 (EffectfulScalarCall.invoke depth).run SameCallInputs.caller≠.error .exhausted := by
 rw [source]
 intro impossible
 cases impossible

theorem target_not_ok (last : Machine) (remaining : Nat) :
 run EffectfulScalarCall.image SameCallInputs.machine≠.ok last remaining := by
 rw [target]
 intro impossible
 cases impossible

theorem target_not_fault : run EffectfulScalarCall.image SameCallInputs.machine≠.fault := by
 rw [target]
 intro impossible
 cases impossible

/-- The same call distinguishes real callee-write failure from a valid but shallow
recursive quotation. Target success on the good shallow input remains explicit. -/
theorem zero_control :
 (EffectfulScalarCall.invoke 0).run DisjointScalarReturn.Client.caller=.error .exhausted ∧
 (EffectfulScalarCall.invoke 0).run SameCallInputs.caller=.error .revert ∧
 run EffectfulScalarCall.image DisjointScalarReturn.Client.before=.ok EffectfulScalarCall.machine 0 ∧
 run EffectfulScalarCall.image SameCallInputs.machine=.revert :=
 ⟨EffectfulScalarCall.exhaustion_boundary.1,source 0,EffectfulScalarCall.target,target⟩

end Client

end Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulScalarFailure
