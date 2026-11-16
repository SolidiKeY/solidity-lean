import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarSourceCompilerClient

/-! Actual selected success/bare-revert clients and syntax-authentication
counterexamples. The deeper-child witness passes one-layer inspection but
fails complete verification. Exhaustion remains outside the two conditional
frozen claims; no full simulation or failed-state relation is inferred. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler.Controls
open Evm Evm.Memory ScalarRecursiveSource
open DisjointScalarReturn.Client (Γ F caller before reference)
abbrev A := CountdownWitness.A
abbrev C := CountdownWitness.P.C

def alteredChild : Prog C (Frame A) (Frame A) :=
 step A rfl 1 (fun _ => .cons .revert .nil)

theorem outer_layer_matches : (ScalarSourceCheck.readHead A rfl alteredChild).isSome=true := rfl

theorem deeper_child_rejected : ScalarSourceCheck.check A rfl 2 alteredChild=none := rfl

def alteredInput : Stmt C Γ Γ := call rfl reference ScalarReentry.count .here
 (.user "alias") (.user "count") (.user "result") "scalarCountdown" 2 (fun _ => alteredChild)

theorem altered_root_rejected : compile 1 5 16 9 8 F alteredInput=none := rfl

theorem source_difference : alteredInput.run ScalarContinuation.final=.error .revert ∧
 (Client.input 2).run ScalarContinuation.final=.error .exhausted := by
 constructor
 · with_unfolding_all rfl
 · simpa only [if_neg (show ¬(3:Nat)<2 from by decide)] using ScalarReentry.source 2

def wrongIndex : Prog C (Frame A) (Frame A) := step A rfl 2 (fun _ => body A rfl 1)

theorem index_rejected : ScalarSourceCheck.check A rfl 2 wrongIndex=none := rfl

theorem wrong_base_rejected : ScalarSourceCheck.check (C:=C) A rfl 0 (.cons .revert .nil)=none := rfl

theorem wrong_guard_rejected : ScalarSourceCheck.checkGuard (C:=C) (R:=A) (.simple (.bool false))=none := rfl

theorem wrong_increment_rejected : ScalarSourceCheck.checkIncrement (C:=C) (R:=A)
 (.assignLocal .here (.simple (.lit 9 rfl)))=none := rfl

theorem wrong_result_rejected : ScalarSourceCheck.checkResult (R:=A)
 (.val .uint (.user "result") (some (.there .here)))=none := rfl

theorem ordinary_call_refused : compile 1 5 16 9 8 F
 (.call "scalarCountdown" (DisjointScalarEntry.args rfl reference ScalarReentry.count)
 (.val .uint (.user "result") (some (.here : Idx Γ (.val .uint)))) (body A rfl 4))=none := rfl

/-- Recognition does not claim that an exhausted source quotation is a full
source-to-target failure correspondence. The actual image is index-independent. -/
theorem exhausted_boundary : (Client.input 0).run ScalarContinuation.final=.error .exhausted ∧
 run (Client.selected 0).plan.code ScalarContinuation.target=.ok ScalarReentry.Endpoint.machine 0 := by
 constructor
 · simpa only [if_neg (show ¬(3:Nat)<0 from by decide)] using ScalarReentry.source 0
 · rw [Client.same_image 0 4]
   exact Client.target

def badCount : Val C Γ .uint :=
 .readMem (.index .dyn (.var reference rfl) (.simple (.lit 3 rfl)))
def badEmitted : ScalarEmitter.Emission 1 5 16 9 8 F badCount :=
 (ScalarEmitter.compile 1 5 16 9 8 F badCount).get (by rfl)
def badInput : Stmt C Γ Γ := call rfl reference badCount .here
 (.user "outerAlias") (.user "outerCount") (.user "outerResult") "scalarCountdown" 4 (fun _ => body A rfl 4)
def badSelected : Selected 1 5 16 9 8 F badInput :=
 make rfl reference badCount (.here : Idx Γ (.val .uint))
 (.user "outerAlias") (.user "outerCount") (.user "outerResult") "scalarCountdown" 4
 (fun _ => body A rfl 4) rfl (ScalarSourceCheck.complete A rfl 4) badEmitted rfl

theorem bad_root : compile 1 5 16 9 8 F badInput=some badSelected :=
 compile_call rfl reference badCount (.here : Idx Γ (.val .uint))
 (.user "outerAlias") (.user "outerCount") (.user "outerResult") "scalarCountdown" 4
 (fun _ => body A rfl 4) rfl (ScalarSourceCheck.complete A rfl 4) badEmitted rfl

theorem bad_eval : badCount.evalT ScalarContinuation.final=.error .revert := by
 with_unfolding_all rfl

theorem bad_source : badInput.run ScalarContinuation.final=.error .revert :=
 (badSelected.source_run ScalarContinuation.final).trans
   (ScalarClaims.source_revert rfl reference badCount .here "scalarCountdown" 4 ScalarContinuation.final bad_eval)

theorem bad_entry : InterfaceV1.Entry badSelected.plan 1 1 16 F ScalarContinuation.final
 ScalarContinuation.finalBase ScalarContinuation.target 10 := by
 have initial := ScalarReentry.entry 4
 refine ⟨initial.represented,initial.callerBound,initial.resultBound,initial.workspace,
   initial.pointerAbove,initial.pointerBelow,initial.payloadAbove,?_,?_,.inl (by decide),?_,initial.cursor,.inl rfl⟩
 · change 10+ScalarDemand.reserve badCount ScalarContinuation.final≤16
   rw [ScalarDemand.reserve_error _ bad_eval]
   decide
 · change 5≤ScalarDemand.reserve badCount ScalarContinuation.final
   rw [ScalarDemand.reserve_error _ bad_eval]
   decide
 · change 10+ScalarDemand.reserve badCount ScalarContinuation.final<W
   rw [ScalarDemand.reserve_error _ bad_eval]
   decide

theorem bad_target : run badSelected.plan.code ScalarContinuation.target=.revert :=
 badSelected.bare_revert (by decide) 1 16 ScalarContinuation.final ScalarContinuation.finalBase
   ScalarContinuation.target 10 bad_entry bad_source

theorem bad_not_fault : run badSelected.plan.code ScalarContinuation.target≠.fault := by
 rw [bad_target]
 intro wrong
 cases wrong

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler.Controls
