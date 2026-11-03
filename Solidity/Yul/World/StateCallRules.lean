import Solidity.Yul.World.StateCallExtra

/-! Lean-only existing Box rules for actual selected state-changing calls.
No intrinsic Yul/G51/frontend/compiler/general world adequacy is inferred. -/
namespace Solidity.Yul.World.StateCallRules
open Solidity.Source
open Solidity.Roadmap (Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.StateCallPhysical
open Solidity.Yul.World.StateCallPort

abbrev Configuration (Γ : RCtx) := AdapterRules.Configuration (Carrier env Γ) env.layout env.lay env.lay

def Step {Γ} (G : Glob env) (failed : Bool) (m : ByteView) (gas offset size : Word)
    (status : Except Source.Halt Outcome) (before after : Configuration Γ) : Prop :=
  ∃ shared : before.observed.effects.execution=before.memory.1.1.2.ex,
    call (CallerFrame.liftInvoke (invoke failed G)) before.memory.1.1 before.memory.1.2 before.memory.2
      before.observed shared m (parent before.memory.1.1) .call CallerFrameChecks.receiver gas 7 offset size=
      some (status,(after.memory,after.observed))

theorem success_sound (G : Glob env) {Γ} (before : Configuration Γ) (next : ExecState env.layout env.lay env.lay)
    (code : (before.memory.1.1.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : before.memory.1.1.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (encoding : before.memory.2=encodingPrefix)
    (padding : before.memory.1.2.cells (complementKey false CallerFrameChecks.receiver 7)=0xaabbcc00)
    (m : ByteView) (gas offset size : Word) (loaded : PhysicalHeapPort.port.load m offset size=some (input G)) :
    AdapterRules.Box (Step G false m gas offset size (.ok (.success ReturningCall.output)))
      (fun after=>after.memory=(successResult before.memory.1.1 next before.memory.1.2 before.observed).1 ∧
        after.observed=(successResult before.memory.1.1 next before.memory.1.2 before.observed).2) before := by
  intro result step
  obtain ⟨shared,ran⟩ := step
  rw [encoding,call_success G _ next code transfer _ padding _ shared m gas offset size loaded] at ran
  have out:=(Prod.mk.inj (Option.some.inj ran)).2
  exact ⟨(Prod.mk.inj out).1.symm,(Prod.mk.inj out).2.symm⟩

theorem revert_sound (G : Glob env) {Γ} (before : Configuration Γ) (next : ExecState env.layout env.lay env.lay)
    (code : (before.memory.1.1.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : before.memory.1.1.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (encoding : before.memory.2=encodingPrefix)
    (padding : before.memory.1.2.cells (complementKey false CallerFrameChecks.receiver 7)=0xaabbcc00)
    (m : ByteView) (gas offset size : Word) (loaded : PhysicalHeapPort.port.load m offset size=some (input G)) :
    AdapterRules.Box (Step G true m gas offset size (.ok (.revert (StateCall.errorData G))))
      (fun after=>after.memory=⟨⟨before.memory.1.1,before.memory.1.2⟩,encodingPrefix⟩ ∧
        after.observed=(revertResult G before.memory.1.1 before.memory.1.2 before.observed).2) before := by
  intro result step
  obtain ⟨shared,ran⟩ := step
  rw [encoding,call_revert G _ next code transfer _ padding _ shared m gas offset size loaded] at ran
  have out:=(Prod.mk.inj (Option.some.inj ran)).2
  exact ⟨(Prod.mk.inj out).1.symm,(Prod.mk.inj out).2.symm⟩

theorem inhabited_success (G : Glob env) :
    Step G false (StateCallChecks.memory G) 10000 160 4 (.ok (.success ReturningCall.output))
      ⟨StateCallChecks.observed,⟨⟨StateCallChecks.caller G,StateCallChecks.residual⟩,encodingPrefix⟩⟩
      ⟨(successResult (StateCallChecks.caller G) StateCallChecks.moved StateCallChecks.residual StateCallChecks.observed).2,
        (successResult (StateCallChecks.caller G) StateCallChecks.moved StateCallChecks.residual StateCallChecks.observed).1⟩ :=
  ⟨rfl,StateCallChecks.success G⟩

theorem inhabited_revert (G : Glob env) :
    Step G true (StateCallChecks.memory G) 10000 160 4 (.ok (.revert (StateCall.errorData G)))
      ⟨StateCallChecks.observed,⟨⟨StateCallChecks.caller G,StateCallChecks.residual⟩,encodingPrefix⟩⟩
      ⟨(revertResult G (StateCallChecks.caller G) StateCallChecks.residual StateCallChecks.observed).2,
        (revertResult G (StateCallChecks.caller G) StateCallChecks.residual StateCallChecks.observed).1⟩ :=
  ⟨rfl,StateCallChecks.reverted G⟩

end Solidity.Yul.World.StateCallRules
