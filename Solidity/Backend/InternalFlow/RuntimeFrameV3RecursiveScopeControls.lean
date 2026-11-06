import Solidity.Backend.InternalFlow.RuntimeFrameV3RecursiveScopeClient
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScopedScalarControls

/-! Positive mixed-scope recognition and actual deep-child refusals. The
older exact/outer-only selectors keep their original refusals. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveScopeCompiler.Controls
open Evm Evm.Memory ScalarRecursiveSource
open Client (C A)
open DisjointScalarReturn.Client (Γ F reference)
open ScalarSourceCompiler (call)

def mixed : Prog C (Frame A) (Frame A) :=
 step A rfl 1 (fun _ => RecursiveScopes.scopedBody A rfl .bool (.user "nested") 1)
def mixedAgreement : mixed.runR=(body (C:=C) A rfl 2).runR :=
 RecursiveScopes.step_congr rfl 1 _ _ (RecursiveScopes.scoped_run A rfl .bool (.user "nested") 1)

theorem mixed_checked : RecursiveScopes.check A rfl 2 mixed=some ⟨mixedAgreement⟩ := rfl

theorem old_exact_refuses : ScalarSourceCompiler.compile 1 5 16 9 8 F
 (Client.input .uint (.user "nested") 4)=none := rfl

theorem old_outer_only_refuses : ScopedScalarCompiler.compile 1 5 16 9 8 F
 (Client.input .uint (.user "nested") 4)=none := rfl

def brokenChild : Prog C (Frame A) (Frame A) :=
 ScopedSource.decorate (step A rfl 0 (fun _ => .cons .revert .nil)) .uint (.user "nested")
def broken : Prog C (Frame A) (Frame A) :=
 ScopedSource.decorate (step A rfl 1 (fun _ => brokenChild)) .uint (.user "nested")

theorem deep_child_refused : RecursiveScopes.check A rfl 2 broken=none := rfl

def brokenInput : Stmt C Γ Γ :=
 call rfl reference ScalarReentry.count .here (.user "alias") (.user "count") (.user "result")
   "scalarCountdown" 2 (fun _ => broken)

theorem deep_root_refused : compile 1 5 16 9 8 F brokenInput=none := rfl

/-- The rejected base is observably different, not merely a different proof
or printer: the actual source reverts instead of exhausting. -/
theorem source_difference : brokenInput.run ScalarContinuation.final=.error .revert ∧
 (Client.input .uint (.user "nested") 2).run ScalarContinuation.final=.error .exhausted := by
 constructor
 · with_unfolding_all rfl
 · exact (Client.source .uint (.user "nested") 2).trans
     (by simpa only [if_neg (show ¬(3:Nat)<2 from by decide)] using ScalarReentry.source 2)

theorem wrong_index_refused : RecursiveScopes.check A rfl 2
 (ScopedSource.decorate ScalarSourceCompiler.Controls.wrongIndex .uint (.user "nested"))=none := rfl

theorem double_wrapper_refused : RecursiveScopes.check A rfl 1
 (ScopedSource.decorate (RecursiveScopes.scopedBody (C:=C) A rfl .uint (.user "nested") 1)
   .bool (.user "extra"))=none := rfl

theorem initialized_refused : RecursiveScopes.check A rfl 4 ScopedScalarCompiler.Controls.initialized=none := rfl

theorem protected_write_refused : RecursiveScopes.check A rfl 4 ScopedScalarCompiler.Controls.protectedWrite=none := rfl

theorem extra_context_refused : RecursiveScopes.check A rfl 4 ScopedScalarCompiler.Controls.extraInnerLocal=none := rfl

/-- Recognition is not a full source/target exhaustion correspondence. -/
theorem exhausted_boundary :
 (Client.input .uint (.user "nested") 0).run ScalarContinuation.final=.error .exhausted ∧
 run (Client.selected .uint (.user "nested") 0).plan.code ScalarContinuation.target=.ok ScalarReentry.Endpoint.machine 0 := by
 exact ⟨Client.exhausted_source _ _,ScalarSourceCompiler.Controls.exhausted_boundary.2⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveScopeCompiler.Controls
