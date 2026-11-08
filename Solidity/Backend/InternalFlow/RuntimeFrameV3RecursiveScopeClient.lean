import Solidity.Backend.InternalFlow.RuntimeFrameV3RecursiveScopeCompiler
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarSourceCompilerControls

/-! Actual native recursive activations with a default local scoped at every
quotation level, selected at the populated post-allocation caller. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveScopeCompiler.Client
open Evm Evm.Memory ScalarRecursiveSource
open ScalarSourceCompiler (call)
open DisjointScalarReturn.Client (Γ F reference)
abbrev C := CountdownWitness.P.C
abbrev A := CountdownWitness.A

def input (p : PrimTy) (name : Var) (depth : Nat) : Stmt C Γ Γ :=
 call rfl reference ScalarReentry.count .here (.user "alias") (.user "count") (.user "result")
   "scalarCountdown" depth (fun _ => RecursiveScopes.scopedBody A rfl p name depth)

def selected (p : PrimTy) (name : Var) (depth : Nat) : Selected 1 5 16 9 8 F (input p name depth) :=
 make rfl reference ScalarReentry.count (.here : Idx Γ (.val .uint))
   (.user "alias") (.user "count") (.user "result") "scalarCountdown" depth
   (fun _ => RecursiveScopes.scopedBody A rfl p name depth)
   (RecursiveScopes.scoped_run A rfl p name depth) (RecursiveScopes.complete A rfl p name depth)
   ScalarReentry.emitted ScalarReentry.selected

theorem root (p : PrimTy) (name : Var) (depth : Nat) :
 compile 1 5 16 9 8 F (input p name depth)=some (selected p name depth) :=
 compile_call rfl reference ScalarReentry.count (.here : Idx Γ (.val .uint))
   (.user "alias") (.user "count") (.user "result") "scalarCountdown" depth
   (fun _ => RecursiveScopes.scopedBody A rfl p name depth)
   (RecursiveScopes.scoped_run A rfl p name depth) (RecursiveScopes.complete A rfl p name depth)
   ScalarReentry.emitted ScalarReentry.selected

theorem same_image (p : PrimTy) (name : Var) (depth : Nat) :
 (selected p name depth).plan=(ScalarSourceCompiler.Client.selected depth).plan := rfl

theorem source (p : PrimTy) (name : Var) (depth : Nat) :
 (input p name depth).run ScalarContinuation.final=
   (ScalarSourceCompiler.Client.input depth).run ScalarContinuation.final :=
 (selected p name depth).source_run ScalarContinuation.final

theorem returned (p : PrimTy) (name : Var) (depth : Nat) (enough : 3<depth) :
 InterfaceV1.Returned (selected p name depth).plan 1 1 16 ScalarContinuation.final
 ScalarContinuation.finalBase ScalarContinuation.target 10
 ⟨ScalarReentry.Endpoint.resultState,List.prefix_refl _⟩ :=
 (selected p name depth).returns (by decide) 1 16 ScalarContinuation.final ScalarContinuation.finalBase
   ScalarContinuation.target 10 (ScalarSourceCompiler.Client.entered depth) _
   ((source p name depth).trans (ScalarSourceCompiler.Client.actual_source depth enough))

theorem target (p : PrimTy) (name : Var) :
 run (selected p name 4).plan.code ScalarContinuation.target=.ok ScalarReentry.Endpoint.machine 0 :=
 ScalarSourceCompiler.Client.target

theorem complete_observations (p : PrimTy) (name : Var) :
 run (selected p name 4).plan.code ScalarContinuation.target=.ok ScalarReentry.Endpoint.machine 0 ∧
 (List.range 26).map (fun index => ScalarReentry.Endpoint.machine.mem index)=
 [w[26],w[16],w[16],w[2],w[3],w[16],w[3],w[3],w[10],w[10],w[16],w[3],w[16],w[2],w[16],w[1],
  w[2],w[3],w[9],w[0],w[1],w[4],w[3],w[0],w[0],w[0]] ∧
 ScalarReentry.Endpoint.machine.stack=[w[77]] := by
 refine ⟨target p name,?_,?_⟩
 · exact congrArg Prod.snd ScalarSourceCompiler.Client.complete_observations
 · exact congrArg Prod.fst ScalarSourceCompiler.Client.complete_observations

theorem native_default_root (p : PrimTy) (name : Var) :
 compile 1 5 16 9 8 F (input p name recDepth)=some (selected p name recDepth) := root p name recDepth

theorem native_default_returned (p : PrimTy) (name : Var) :
 InterfaceV1.Returned (selected p name recDepth).plan 1 1 16 ScalarContinuation.final
 ScalarContinuation.finalBase ScalarContinuation.target 10
 ⟨ScalarReentry.Endpoint.resultState,List.prefix_refl _⟩ := returned p name recDepth (by decide)

theorem exhausted_source (p : PrimTy) (name : Var) :
 (input p name 0).run ScalarContinuation.final=.error .exhausted :=
 (source p name 0).trans ScalarSourceCompiler.Controls.exhausted_boundary.1

def badInput : Stmt C Γ Γ :=
 call rfl reference ScalarSourceCompiler.Controls.badCount .here
   (.user "outerAlias") (.user "outerCount") (.user "outerResult") "scalarCountdown" 4
   (fun _ => RecursiveScopes.scopedBody A rfl .uint (.user "privateDefault") 4)
def badSelected : Selected 1 5 16 9 8 F badInput :=
 make rfl reference ScalarSourceCompiler.Controls.badCount (.here : Idx Γ (.val .uint))
   (.user "outerAlias") (.user "outerCount") (.user "outerResult") "scalarCountdown" 4
   (fun _ => RecursiveScopes.scopedBody A rfl .uint (.user "privateDefault") 4)
   (RecursiveScopes.scoped_run A rfl .uint (.user "privateDefault") 4)
   (RecursiveScopes.complete A rfl .uint (.user "privateDefault") 4) ScalarSourceCompiler.Controls.badEmitted rfl

theorem bad_root : compile 1 5 16 9 8 F badInput=some badSelected :=
 compile_call rfl reference ScalarSourceCompiler.Controls.badCount (.here : Idx Γ (.val .uint))
   (.user "outerAlias") (.user "outerCount") (.user "outerResult") "scalarCountdown" 4
   (fun _ => RecursiveScopes.scopedBody A rfl .uint (.user "privateDefault") 4)
   (RecursiveScopes.scoped_run A rfl .uint (.user "privateDefault") 4)
   (RecursiveScopes.complete A rfl .uint (.user "privateDefault") 4) ScalarSourceCompiler.Controls.badEmitted rfl

theorem bad_source : badInput.run ScalarContinuation.final=.error .revert :=
 (badSelected.source_run ScalarContinuation.final).trans ScalarSourceCompiler.Controls.bad_source

theorem bad_target : run badSelected.plan.code ScalarContinuation.target=.revert :=
 badSelected.bare_revert (by decide) 1 16 ScalarContinuation.final ScalarContinuation.finalBase
   ScalarContinuation.target 10 ScalarSourceCompiler.Controls.bad_entry bad_source

theorem bad_not_fault : run badSelected.plan.code ScalarContinuation.target≠.fault := by
 rw [bad_target]
 intro wrong
 cases wrong

end Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveScopeCompiler.Client
