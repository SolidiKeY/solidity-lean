import Solidity.Yul.World.DelegateOutputPort

/-! Lean-only local Box for the actual selected call-and-copy operation.
No intrinsic Yul/G51 source calculus or compiler adequacy is inferred. -/
namespace Solidity.Yul.World.DelegateOutputRules
open Solidity.Source
open Solidity.Roadmap (Outcome)
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.DelegatePhysical

abbrev Configuration := AdapterRules.Configuration (HeapOutputTransport.CopyResult env [.bytes .memory]) env.layout env.lay env.lay

def initial (G : Glob env) : Configuration :=
  ⟨StateCallChecks.observed,(⟨⟨⟨StateCallChecks.caller G,StateCallChecks.residual⟩,before⟩,StateCallChecks.observed⟩,none)⟩

def Step (G : Glob env) (before after : Configuration) : Prop :=
  before=initial G ∧ DelegateOutput.runAndCopy G=some (.ok (.success ReturningCall.output),after.memory) ∧
    after.observed=after.memory.1.2

theorem normal_sound (G : Glob env) :
    AdapterRules.Box (Step G) (fun after=>after.memory=DelegateOutput.expected G ∧
      after.observed=(DelegateOutput.completed G).2) (initial G) := by
  intro after step
  have ran:=step.2.1
  rw [DelegateOutput.runAndCopy_exact] at ran
  have same : after.memory=DelegateOutput.expected G := ((Prod.mk.inj (Option.some.inj ran)).2).symm
  refine ⟨same,?_⟩
  rw [step.2.2,same]
  rfl

theorem inhabited (G : Glob env) :
    Step G (initial G) ⟨(DelegateOutput.completed G).2,DelegateOutput.expected G⟩ :=
  ⟨rfl,DelegateOutput.runAndCopy_exact G,rfl⟩
end Solidity.Yul.World.DelegateOutputRules
