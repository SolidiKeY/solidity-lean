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
