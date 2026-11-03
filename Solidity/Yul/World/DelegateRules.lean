import Solidity.Yul.World.DelegatePending

/-! Lean-only local full-carrier rules, derived from actual registered bodies.
No universal Yul/G51/frontend/compiler/world adequacy is claimed. -/
namespace Solidity.Yul.World.DelegateRules
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.DelegatePhysical
open Solidity.Yul.World.DelegatePort
abbrev Configuration (Γ : RCtx) := AdapterRules.Configuration (Carrier env Γ) env.layout env.lay env.lay

def Step {Γ} (G : Glob env) (failed : Bool) (depth : Nat) (sender target : Address) (value : Word)
    (m : ByteView) (gas offset size : Word) (status : Except Halt Outcome) (before after : Configuration Γ) : Prop :=
  ∃ shared : before.observed.effects.execution=before.memory.1.1.2.ex,
    call (CallerFrame.liftInvoke (invoke failed G depth)) before.memory.1.1 before.memory.1.2 before.memory.2
      before.observed shared m (parent before.memory.1.1 sender value false) .delegatecall target gas 0 offset size=
      some (status,(after.memory,after.observed))

theorem success_sound (G : Glob env) (depth : Nat) (bounded : depth<1024) {Γ} (before : Configuration Γ)
    (sender target : Address) (value : Word)
    (classification : target.val≠0 ∧ (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=false)
    (code : (before.memory.1.1.2.ex.world.accounts target).code=some 0)
    (encoding : before.memory.2=DelegatePhysical.before)
    (padding : before.memory.1.2.cells (complementKey false account 7)=0xaabbcc00)
    (m : ByteView) (gas offset size : Word) (loaded : PhysicalHeapPort.port.load m offset size=some (input G)) :
    AdapterRules.Box (Step G false depth sender target value m gas offset size (.ok (.success ReturningCall.output)))
      (fun after=>(after.memory,after.observed)=successful before.memory.1.1 before.memory.1.2 before.observed) before := by
  intro result step
  obtain ⟨shared,ran⟩:=step
  rw [encoding,call_success G depth bounded _ sender target value gas classification code _ padding _ shared m offset size loaded] at ran
  exact ((Prod.mk.inj (Option.some.inj ran)).2).symm

theorem revert_sound (G : Glob env) (depth : Nat) (bounded : depth<1024) {Γ} (before : Configuration Γ)
    (sender target : Address) (value : Word)
    (classification : target.val≠0 ∧ (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=false)
    (code : (before.memory.1.1.2.ex.world.accounts target).code=some 0)
    (encoding : before.memory.2=DelegatePhysical.before)
    (padding : before.memory.1.2.cells (complementKey false account 7)=0xaabbcc00)
    (m : ByteView) (gas offset size : Word) (loaded : PhysicalHeapPort.port.load m offset size=some (input G)) :
    AdapterRules.Box (Step G true depth sender target value m gas offset size (.ok (.revert (errorData G))))
      (fun after=>(after.memory,after.observed)=reverted before.memory.1.1 before.memory.1.2 DelegatePhysical.before before.observed (errorData G)) before := by
  intro result step
  obtain ⟨shared,ran⟩:=step
  rw [encoding,call_revert G depth bounded _ sender target value gas classification code _ padding _ shared m offset size loaded] at ran
  exact ((Prod.mk.inj (Option.some.inj ran)).2).symm

theorem inhabited_success (G : Glob env) :
    Step G false 0 DelegateChecks.sender DelegateChecks.target DelegateChecks.value (StateCallChecks.memory G) 10000 160 4
      (.ok (.success ReturningCall.output))
      ⟨StateCallChecks.observed,⟨⟨StateCallChecks.caller G,StateCallChecks.residual⟩,DelegatePhysical.before⟩⟩
      ⟨(successful (StateCallChecks.caller G) StateCallChecks.residual StateCallChecks.observed).2,
        (successful (StateCallChecks.caller G) StateCallChecks.residual StateCallChecks.observed).1⟩ := ⟨rfl,DelegateChecks.success G⟩
end Solidity.Yul.World.DelegateRules
