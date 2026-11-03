import Solidity.Yul.World.DelegateCompletion
namespace Solidity.Yul.World.DelegateChecks
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.DelegatePhysical
open Solidity.Yul.World.DelegatePort
open Solidity.Yul.World.StateCallChecks (caller residual observed memory loaded)

def sender : Address := CallerFrameChecks.sender
def target : Address := CallerFrameChecks.receiver
/-- Larger than caller balance11: DELEGATECALL never attempts value transfer. -/
def value : Word := 17

theorem distinct : target≠account ∧ sender≠account ∧ sender≠target := ⟨by decide,by decide,by decide⟩

theorem success (G : Glob env) :
    call (CallerFrame.liftInvoke (invoke false G 0)) (caller G) residual before observed rfl (memory G)
      (parent (caller G) sender value false) .delegatecall target 10000 0 160 4=
      some (.ok (.success ReturningCall.output),successful (caller G) residual observed) :=
  call_success G 0 (by decide) _ sender target value 10000 (by decide) rfl residual rfl observed rfl _ 160 4 (loaded G)

theorem reverted_call (G : Glob env) :
    call (CallerFrame.liftInvoke (invoke true G 0)) (caller G) residual before observed rfl (memory G)
      (parent (caller G) sender value false) .delegatecall target 10000 0 160 4=
      some (.ok (.revert (errorData G)),reverted (caller G) residual before observed (errorData G)) :=
  call_revert G 0 (by decide) _ sender target value 10000 (by decide) rfl residual rfl observed rfl _ 160 4 (loaded G)

theorem static_refusal (G : Glob env) (failed : Bool) :
    call (CallerFrame.liftInvoke (invoke failed G 0)) (caller G) residual before observed rfl (memory G)
      (parent (caller G) sender value true) .delegatecall target 10000 0 160 4=
      some (.ok (.revert []),reverted (caller G) residual before observed []) :=
  call_static failed G 0 (by decide) _ sender target value 10000 (by decide) rfl residual before observed rfl _ 160 4 (loaded G)

theorem enclosing (G : Glob env) :
    finish (caller G) before observed (enter (caller G) residual (parent (caller G) sender value false) .delegatecall target 0 [])
      (successful (caller G) residual observed).1 [] (.revert [0xdd,0xee])=
      reverted (caller G) residual before observed [0xdd,0xee] :=
  enclosing_revert _ sender target value residual observed _

theorem full_state (G : Glob env) :
    let result:=successful (caller G) residual observed
    result.1.1.1.1=(caller G).1 ∧ result.1.1.1.2.heap=(caller G).2.heap ∧
    result.1.1.1.2.fnLocals=(caller G).2.fnLocals ∧ result.1.1.1.2.events=(caller G).2.events ∧
    result.1.1.1.2.logs=(caller G).2.logs ∧ result.2.trace=observed.trace ∧
    result.2.effects.returndata=ReturningCall.output ∧ result.1.1.1.2.ex.journal.length=5 ∧
    result.1.1.2.journal.length=2 ∧ result.1.2.journal.length=2 ∧
    (result.1.1.1.2.ex.world.accounts account).balance=11 ∧
    (result.1.1.1.2.ex.world.accounts target)=(caller G).2.ex.world.accounts target ∧
    (result.1.1.1.2.ex.world.accounts account).storage.read flagPath=some (.bool true) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem inherited_context (G : Glob env) :
    let frame:=enter (caller G) residual (parent (caller G) sender value false) .delegatecall target 0 (input G)
    frame.source.this=account ∧ frame.source.caller=sender ∧ frame.source.value=value ∧ frame.source.static=false := ⟨rfl,rfl,rfl,rfl⟩

theorem input_view (G : Glob env) :
    reencodePersistentSlot (representedBanks (E:=env) StateCallPhysical.registry false before)
      ⟨(caller G).2.ex,residual⟩ account 7=some 0xaabbcc00 := by
  have store : ((caller G).2.ex.world.accounts account).storage=Source.Storage.empty := rfl
  unfold reencodePersistentSlot
  rw [store]
  have pad : residual.cells (complementKey false account 7)=(0xaabbcc00 : Word) := rfl
  change (finiteEncode (selectedSlotPaths (representedBanks (E:=env) StateCallPhysical.registry false before account) 7)
    Source.Storage.empty (fun _=>residual.cells (complementKey false account 7))).map (fun out=>out 7)=_
  rw [pad]
  decide

theorem output_view (G : Glob env) :
    reencodePersistentSlot (representedBanks (E:=env) StateCallPhysical.registry false
      (requestEncoding (E:=env) StateCallPhysical.registry StateCallPhysical.registry request before))
      ⟨(changed (caller G) account).2.ex,residualWrite residual plan.packed.residualUpdate⟩ account 7=some request.raw := by
  have actual:=full_word (caller G) sender value 1 residual observed rfl
  unfold PhysicalSlotPort.step at actual
  rw [representedSourceStep_nonstatic _ _ _ _ rfl,source_op] at actual
  exact actual

theorem precompile_control (G : Glob env) :
    invoke false G 0 observed (enter (caller G) residual (parent (caller G) sender value false) .delegatecall 1 0 (input G))
      .delegatecall 1 10000 (input G) ⟨⟨⟨Source.L0 env,(caller G).2⟩,residual⟩,before⟩=none := by
  -- Explicit carrier keeps the original source and physical prefixes.
  exact precompile_refused false G 0 _ _ _ _ _ _ rfl
end Solidity.Yul.World.DelegateChecks
