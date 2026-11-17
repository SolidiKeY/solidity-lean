import Solidity.Backend.CompilerEndpoint
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarSourceCompiler
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarReentryControls

/-! The actual heap-reading source statement is publicly selected after the
real mutation/allocation prefix. Its source and target observations are the
unchanged re-entry endpoint, now linked to checked source syntax. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler.Client
open Evm Evm.Memory ScalarRecursiveSource
open DisjointScalarReturn.Client (Γ F caller before reference)

def input (depth : Nat) := ScalarReentry.statement depth

def selected (depth : Nat) : Selected 1 5 16 9 8 F (input depth) :=
 make rfl reference ScalarReentry.count (.here : Idx Γ (.val .uint))
   (.user "alias") (.user "count") (.user "result") "scalarCountdown" depth
   (fun _ => body CountdownWitness.A rfl depth) rfl
   (ScalarSourceCheck.complete CountdownWitness.A rfl depth) ScalarReentry.emitted ScalarReentry.selected

theorem root (depth : Nat) : compile 1 5 16 9 8 F (input depth)=some (selected depth) :=
 compile_call rfl reference ScalarReentry.count (.here : Idx Γ (.val .uint))
   (.user "alias") (.user "count") (.user "result") "scalarCountdown" depth
   (fun _ => body CountdownWitness.A rfl depth) rfl
   (ScalarSourceCheck.complete CountdownWitness.A rfl depth) ScalarReentry.emitted ScalarReentry.selected

theorem plan_eq (depth : Nat) : (selected depth).plan=ScalarReentry.plan.at depth := rfl

/-- Every recognized quotation selects the SAME runtime image. The theorem
is about actual public selector results, not an assumed image equality. -/
theorem same_image (left right : Nat) :
 (selected left).plan.code=(selected right).plan.code := rfl

theorem entered (depth : Nat) : InterfaceV1.Entry (selected depth).plan 1 1 16 F ScalarContinuation.final
 ScalarContinuation.finalBase ScalarContinuation.target 10 := by
 rw [plan_eq]
 exact ScalarReentry.entry depth

theorem actual_source (depth : Nat) (enough : 3<depth) :
 (input depth).run ScalarContinuation.final=.ok ⟨ScalarReentry.Endpoint.resultState,List.prefix_refl _⟩ := by
 simpa only [if_pos enough] using ScalarReentry.source depth

theorem returned (depth : Nat) (enough : 3<depth) :
 InterfaceV1.Returned (selected depth).plan 1 1 16 ScalarContinuation.final ScalarContinuation.finalBase
 ScalarContinuation.target 10 ⟨ScalarReentry.Endpoint.resultState,List.prefix_refl _⟩ :=
 (selected depth).returns (by decide) 1 16 ScalarContinuation.final ScalarContinuation.finalBase
   ScalarContinuation.target 10 (entered depth) _ (actual_source depth enough)

theorem target : run (selected 4).plan.code ScalarContinuation.target=.ok ScalarReentry.Endpoint.machine 0 := by
 rw [plan_eq]
 exact ScalarReentry.Endpoint.specification.1

theorem whole_target : run (ScalarContinuation.image++(selected 4).plan.code) before=.ok ScalarReentry.Endpoint.machine 0 := by
 rw [plan_eq]
 exact ScalarReentry.Endpoint.whole_target

theorem whole_source : ScalarReentry.Endpoint.sourceProgram.run caller=.ok ScalarReentry.Endpoint.sourceOutput :=
 ScalarReentry.Endpoint.whole_source

theorem complete_observations :
 (ScalarReentry.Endpoint.machine.stack,
 [ScalarReentry.Endpoint.machine.mem 0,ScalarReentry.Endpoint.machine.mem 1,ScalarReentry.Endpoint.machine.mem 2,
 ScalarReentry.Endpoint.machine.mem 3,ScalarReentry.Endpoint.machine.mem 4,ScalarReentry.Endpoint.machine.mem 5,
 ScalarReentry.Endpoint.machine.mem 6,ScalarReentry.Endpoint.machine.mem 7,ScalarReentry.Endpoint.machine.mem 8,
 ScalarReentry.Endpoint.machine.mem 9,ScalarReentry.Endpoint.machine.mem 10,ScalarReentry.Endpoint.machine.mem 11,
 ScalarReentry.Endpoint.machine.mem 12,ScalarReentry.Endpoint.machine.mem 13,ScalarReentry.Endpoint.machine.mem 14,
 ScalarReentry.Endpoint.machine.mem 15,ScalarReentry.Endpoint.machine.mem 16,ScalarReentry.Endpoint.machine.mem 17,
 ScalarReentry.Endpoint.machine.mem 18,ScalarReentry.Endpoint.machine.mem 19,ScalarReentry.Endpoint.machine.mem 20,
 ScalarReentry.Endpoint.machine.mem 21,ScalarReentry.Endpoint.machine.mem 22,ScalarReentry.Endpoint.machine.mem 23,
 ScalarReentry.Endpoint.machine.mem 24,ScalarReentry.Endpoint.machine.mem 25])=
 ([w[77]],[w[26],w[16],w[16],w[2],w[3],w[16],w[3],w[3],w[10],w[10],w[16],w[3],w[16],w[2],w[16],w[1],
 w[2],w[3],w[9],w[0],w[1],w[4],w[3],w[0],w[0],w[0]]) := ScalarReentry.Controls.complete_observations


/-- The existing source quotation index is supported without normalizing an
independent full certificate or changing recDepth. -/
theorem native_default_root : compile 1 5 16 9 8 F (input recDepth)=some (selected recDepth) := root recDepth

theorem native_default_returned : InterfaceV1.Returned (selected recDepth).plan 1 1 16
 ScalarContinuation.final ScalarContinuation.finalBase ScalarContinuation.target 10
 ⟨ScalarReentry.Endpoint.resultState,List.prefix_refl _⟩ := returned recDepth (by decide)

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler.Client

/-! Legacy owners: `Client.returned`, Controls `bad_target`/`exhausted_boundary`.
The b1 R1 tests below keep these executions outside accepted coverage (H949). -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler.Controls
open Evm Evm.Memory ScalarRecursiveSource
open DisjointScalarReturn.Client (Γ F caller before reference)

/-- R1 of b1 refuses this scalar fixture at every depth; local selector
acceptance remains a separate claim. -/
theorem endpoint_refused (depth : Nat) :
 Evm.Compiler.compile 1 F (.cons (Client.input depth) .nil)=none := rfl

/-- A successful local selector and R1 of the public endpoint coexist. -/
theorem selected_but_endpoint_refused (depth : Nat) :
 compile 1 5 16 9 8 F (Client.input depth)=some (Client.selected depth) ∧
 Evm.Compiler.compile 1 F (.cons (Client.input depth) .nil)=none :=
 ⟨Client.root depth, endpoint_refused depth⟩

example : ∃ out, (Client.input 4).run ScalarContinuation.final=.ok out ∧
 Evm.Compiler.compile 1 F (.cons (Client.input 4) .nil)=none :=
 ⟨_,Client.actual_source 4 (by decide),(selected_but_endpoint_refused 4).2⟩

/-- Recognition does not claim that an exhausted source quotation is a full
source-to-target failure correspondence. The actual image is index-independent. -/
theorem exhausted_boundary : (Client.input 0).run ScalarContinuation.final=.error .exhausted ∧
 run (Client.selected 0).plan.code ScalarContinuation.target=.ok ScalarReentry.Endpoint.machine 0 := by
 constructor
 · simpa only [if_neg (show ¬(3:Nat)<0 from by decide)] using ScalarReentry.source 0
 · rw [Client.same_image 0 4]
   exact Client.target


-- H949: the exhausted legacy quotation remains outside b1 accepted coverage.
example :
 ((Client.input 0).run ScalarContinuation.final=.error .exhausted ∧
  run (Client.selected 0).plan.code ScalarContinuation.target=.ok ScalarReentry.Endpoint.machine 0) ∧
 Evm.Compiler.compile 1 F (.cons (Client.input 0) .nil)=none :=
 ⟨exhausted_boundary,endpoint_refused 0⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler.Controls
