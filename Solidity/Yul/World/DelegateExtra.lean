import Solidity.Yul.World.DelegateRules
namespace Solidity.Yul.World.DelegateExtra
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.DelegatePhysical
open Solidity.Yul.World.DelegatePort
open Solidity.Yul.World.DelegateChecks (sender target value)
open Solidity.Yul.World.StateCallChecks (caller residual observed memory loaded)

def trueCaller (G : Glob env) := changed (caller G) account
def trueObserved (G : Glob env) : ObservedEffects env.layout env.lay env.lay :=
  {observed with effects:={observed.effects with execution:=(trueCaller G).2.ex}}

theorem dirty_true_input (G : Glob env) :
    reencodePersistentSlot (representedBanks (E:=env) StateCallPhysical.registry false before)
      ⟨(trueCaller G).2.ex,residual⟩ account 7=some 0xaabbcc02 := by
  have store : ((trueCaller G).2.ex.world.accounts account).storage=
      (Source.Storage.empty : Source.Storage env.layout (env.lay account)).write flagPath (.bool true) := rfl
  unfold reencodePersistentSlot
  rw [store]
  have pad : residual.cells (complementKey false account 7)=(0xaabbcc00 : Word) := rfl
  change (finiteEncode (selectedSlotPaths (representedBanks (E:=env) StateCallPhysical.registry false before account) 7)
    ((Source.Storage.empty : Source.Storage env.layout (env.lay account)).write flagPath (.bool true))
    (fun _=>residual.cells (complementKey false account 7))).map (fun out=>out 7)=_
  rw [pad]
  decide

theorem dirty_true_call (G : Glob env) :
    call (CallerFrame.liftInvoke (invoke false G 0)) (trueCaller G) residual before (trueObserved G) rfl (memory G)
      (parent (trueCaller G) sender value false) .delegatecall target 10000 0 160 4=
      some (.ok (.success ReturningCall.output),successful (trueCaller G) residual (trueObserved G)) :=
  call_success G 0 (by decide) _ sender target value 10000 (by decide) rfl residual rfl _ rfl _ 160 4 (loaded G)

theorem dirty_true_output (G : Glob env) :
    reencodePersistentSlot (representedBanks (E:=env) StateCallPhysical.registry false
      (requestEncoding (E:=env) StateCallPhysical.registry StateCallPhysical.registry request before))
      ⟨(changed (trueCaller G) account).2.ex,residualWrite residual plan.packed.residualUpdate⟩ account 7=some request.raw := by
  have actual:=full_word (trueCaller G) sender value 1 residual (trueObserved G) rfl
  unfold PhysicalSlotPort.step at actual
  rw [representedSourceStep_nonstatic _ _ _ _ rfl,source_op] at actual
  exact actual

theorem wrong_code (failed : Bool) (G : Glob env) (a sender target : Address) (v : Word) (depth horizon : Nat)
    (bytes : Bytes) (s : EMState env []) (code : (s.2.ex.world.accounts target).code=some 1) :
    DelegateEntry.execute failed G a sender target v depth horizon bytes s=none := by
  simp only [DelegateEntry.execute,Source.instanceAt,Source.Hoare.run_bind,ReturningCall.run_st,code,ReturningCall.run_pure]
  rfl

theorem wrong_owner (G : Glob env) :
    invoke false G 0 observed (enter (caller G) residual (StateCallPort.parent (caller G)) .call target 7 (input G))
      .delegatecall target 10000 (input G) ⟨⟨⟨Source.L0 env,(caller G).2⟩,residual⟩,before⟩=none :=
  owner_refused false G 0 _ _ _ _ _ _ (show target≠account from by decide)

theorem wrong_payload (G : Glob env) :
    invoke false G 0 observed (enter (caller G) residual (parent (caller G) sender value false) .delegatecall target 0 [])
      .delegatecall target 10000 [] ⟨⟨⟨Source.L0 env,(caller G).2⟩,residual⟩,before⟩=none := by
  apply payload_refused
  intro equal
  have size:=congrArg List.length equal
  rw [List.length_nil,input_length] at size
  omega

def wrongResidual := residualWrite residual (complementKey false account 7,0x11223300)

theorem wrong_padding (G : Glob env) :
    invoke false G 0 observed (enter (caller G) wrongResidual (parent (caller G) sender value false) .delegatecall target 0 (input G))
      .delegatecall target 10000 (input G) ⟨⟨⟨Source.L0 env,(caller G).2⟩,wrongResidual⟩,before⟩=none := by
  apply padding_refused _ _ _ _ _ _ _ _ _ rfl
  change residualSave residual.cells (complementKey false account 7) (0x11223300 : Word) (complementKey false account 7)≠_
  rw [residualSave_get]
  decide

theorem full_return_window (G : Glob env) :
    returnWindow (successful (caller G) residual observed).2.effects.returndata 0 32=some ReturningCall.output := rfl

theorem full_error_size (G : Glob env) :
    (reverted (caller G) residual before observed (errorData G)).2.effects.returndata.length=36 := StateCallExtra.error_length G

theorem error_window (G : Glob env) :
    returnWindow (reverted (caller G) residual before observed (errorData G)).2.effects.returndata 4 2=some [0x11,0x22] := StateCallExtra.error_window G

theorem output_prefix (G : Glob env) :
    callOutput (successful (caller G) residual observed).2.effects.returndata 2=[0x11,0x22] := rfl
end Solidity.Yul.World.DelegateExtra
