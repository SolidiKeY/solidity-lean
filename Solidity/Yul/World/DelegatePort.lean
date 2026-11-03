import Solidity.Yul.World.DelegateStatic

/-! Selected registered DELEGATECALL consumer: target code is selected by the
owner runtime; the caller account is the physical request owner. Unsupported
code/layout/depth/classification is adapter None, never an EVM failure. -/
namespace Solidity.Yul.World.DelegatePort
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.StateCallPhysical (registry)
open Solidity.Yul.World.DelegatePhysical

def parent {Γ} (s : EMState env Γ) (sender : Address) (value : Word) (static : Bool) :=
  s.2.ex.enter account sender value [] static

def carrier {Γ} (s : EMState env Γ) (r : ResidualJournal complementCarrierOwnership) : Carrier env Γ :=
  ⟨⟨changed s account,residualWrite r plan.packed.residualUpdate⟩,
    requestEncoding (E:=env) registry registry request before⟩

def invoke (failed : Bool) (G : Glob env) (depth : Nat) : Invoke env [] :=
  fun o frame kind target _ bytes c=>match kind with
  | .delegatecall =>
    if decide (frame.source.this=account) && decide (target.val≠0) && !(Roadmap.Evm.Precompile.ofAddress? target.val).isSome &&
      decide (depth<1024) && decide (bytes=input G) then
      if frame.source.static then do
        let actual ← DelegateStatic.execute failed G account frame.source.caller target frame.source.value (depth+1) bytes c.1.1
        pure (StateCallPort.staticPack c actual)
      else if c.1.2.cells (complementKey false account 7)=(0xaabbcc00 : Word) then do
        let p ← prepareRepresentedSlot (E:=env) registry registry request c.2
        let actual ← DelegateEntry.execute failed G account frame.source.caller target frame.source.value (depth+1) 9 bytes c.1.1
        let sourceFrame:=DelegateBody.frame account frame.source.caller frame.source.value (depth+1)
        let shared : ObservedEffects env.layout env.lay env.lay := {o with effects:={o.effects with execution:=c.1.1.2.ex}}
        let physical:=PhysicalSlotPort.step registry registry request c.2 sourceFrame p c.1.1 c.1.2 shared rfl rfl
        let banks:=match actual.1 with
          | .ok (.success _) => (physical.1.1.2,physical.1.2)
          | .ok (.revert _) => (residualRollback c.1.2.journal.length physical.1.1.2,boolEncodingRollback c.2.journal.length physical.1.2)
          | .error _ => (c.1.2,c.2)
        pure ((actual.1,(⟨⟨actual.2,banks.1⟩,banks.2⟩ : Carrier env [])),
          (actual.2.2.events.drop c.1.1.2.events.length).map Observation.event)
      else none
    else none
  | .call | .staticcall => none

theorem success_empty (G : Glob env) (depth : Nat) (bounded : depth<1024)
    (s : EMState env []) (sender target : Address) (v gas : Word)
    (classification : target.val≠0 ∧ (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=false)
    (code : (s.2.ex.world.accounts target).code=some 0)
    (r : ResidualJournal complementCarrierOwnership)
    (padding : r.cells (complementKey false account 7)=0xaabbcc00)
    (o : ObservedEffects env.layout env.lay env.lay) :
    invoke false G depth o (enter s r (parent s sender v false) .delegatecall target 0 (input G))
      .delegatecall target gas (input G) ⟨⟨s,r⟩,before⟩=
      some ((.ok (.success ReturningCall.output),carrier s r),[]) := by
  unfold invoke
  have prep : prepareRepresentedSlot (E:=env) registry registry request before=some plan := (Option.some_get ready).symm
  simp only [enter,parent,childContext,ExecState.enter,classification.2,bounded,decide_true,Bool.not_false,Bool.and_true,Bool.false_eq_true,if_false,prep,if_pos padding,bind,Option.bind_some]
  rw [DelegateEntry.success G account sender target v (depth+1) s code]
  have physical:=step_exact s sender v (depth+1) r
    ({o with effects:={o.effects with execution:=s.2.ex}} : ObservedEffects env.layout env.lay env.lay) rfl
  rw [physical]
  simp only [Option.bind_some,changed,List.drop_length,List.map_nil]
  simp only [Bool.true_and,decide_eq_true_eq,if_pos classification.1]
  rfl

theorem revert_empty (G : Glob env) (depth : Nat) (bounded : depth<1024)
    (s : EMState env []) (sender target : Address) (v gas : Word)
    (classification : target.val≠0 ∧ (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=false)
    (code : (s.2.ex.world.accounts target).code=some 0)
    (r : ResidualJournal complementCarrierOwnership)
    (padding : r.cells (complementKey false account 7)=0xaabbcc00)
    (o : ObservedEffects env.layout env.lay env.lay) :
    invoke true G depth o (enter s r (parent s sender v false) .delegatecall target 0 (input G))
      .delegatecall target gas (input G) ⟨⟨s,r⟩,before⟩=
      some ((.ok (.revert (errorData G)),⟨⟨s,r⟩,before⟩),[]) := by
  unfold invoke
  have prep : prepareRepresentedSlot (E:=env) registry registry request before=some plan := (Option.some_get ready).symm
  simp only [enter,parent,childContext,ExecState.enter,classification.2,bounded,decide_true,Bool.not_false,Bool.and_true,Bool.false_eq_true,if_false,prep,if_pos padding,bind,Option.bind_some]
  rw [DelegateEntry.revert_exact G account sender target v (depth+1) s code]
  have physical:=step_exact s sender v (depth+1) r
    ({o with effects:={o.effects with execution:=s.2.ex}} : ObservedEffects env.layout env.lay env.lay) rfl
  rw [physical]
  have res:=residualRollback_run r [plan.packed.residualUpdate]
  have enc:=boolEncodingRollback_run before
    (encodingWrites (selectedSlotPaths (registry request.address) request.slot) false request.address (fun _=>request.raw) before)
  simp only [residualRun] at res
  change boolEncodingRollback before.journal.length (requestEncoding (E:=env) registry registry request before)=before at enc
  simp only [Option.bind_some,res,enc,List.drop_length,List.map_nil]
  simp only [Bool.true_and,decide_eq_true_eq,if_pos classification.1]
  rfl

theorem static_empty (failed : Bool) (G : Glob env) (depth : Nat) (bounded : depth<1024)
    (s : EMState env []) (sender target : Address) (v gas : Word)
    (classification : target.val≠0 ∧ (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=false)
    (code : (s.2.ex.world.accounts target).code=some 0)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) :
    invoke failed G depth o (enter s r (parent s sender v true) .delegatecall target 0 (input G))
      .delegatecall target gas (input G) ⟨⟨s,r⟩,b⟩=
      some ((.ok (.revert []),⟨⟨s,r⟩,b⟩),[]) := by
  unfold invoke
  simp only [enter,parent,childContext,ExecState.enter,classification.2,bounded,decide_true,Bool.not_false,Bool.and_true,if_true,bind]
  rw [DelegateStatic.execute_revert failed G account sender target v (depth+1) s code]
  simp only [Option.bind_some,StateCallPort.staticPack,List.drop_length,List.map_nil]
  simp only [Bool.true_and,decide_eq_true_eq,if_pos classification.1]
  rfl
theorem precompile_refused (failed : Bool) (G : Glob env) (depth : Nat) (o frame target gas bytes c)
    (precompile : (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=true) :
    invoke failed G depth o frame .delegatecall target gas bytes c=none := by
  simp only [invoke,precompile,Bool.not_true,Bool.and_false,Bool.false_and,Bool.false_eq_true,if_false]

theorem depth_refused (failed : Bool) (G : Glob env) (depth : Nat) (o frame target gas bytes c)
    (limit : ¬depth<1024) : invoke failed G depth o frame .delegatecall target gas bytes c=none := by
  simp only [invoke,limit,decide_false,Bool.and_false,Bool.false_and,Bool.false_eq_true,if_false]

theorem zero_refused (failed : Bool) (G : Glob env) (depth : Nat) (o frame gas bytes c) :
    invoke failed G depth o frame .delegatecall 0 gas bytes c=none := by
  simp only [invoke,show ¬(0 : Address).val≠0 from by decide,decide_false,Bool.and_false,Bool.false_and,Bool.false_eq_true,if_false]

theorem owner_refused (failed : Bool) (G : Glob env) (depth : Nat) (o frame target gas bytes c)
    (owner : frame.source.this≠account) : invoke failed G depth o frame .delegatecall target gas bytes c=none := by
  simp only [invoke,owner,decide_false,Bool.false_and,Bool.false_eq_true,if_false]

theorem payload_refused (failed : Bool) (G : Glob env) (depth : Nat) (o frame target gas bytes c)
    (wrong : bytes≠input G) : invoke failed G depth o frame .delegatecall target gas bytes c=none := by
  simp only [invoke,wrong,decide_false,Bool.and_false,Bool.false_eq_true,if_false]

theorem padding_refused (failed : Bool) (G : Glob env) (depth : Nat) (o frame target gas bytes c)
    (nonstatic : frame.source.static=false) (padding : c.1.2.cells (complementKey false account 7)≠(0xaabbcc00 : Word)) :
    invoke failed G depth o frame .delegatecall target gas bytes c=none := by
  dsimp only [invoke]
  split
  · simp only [nonstatic,Bool.false_eq_true,if_false]
  · rfl
end Solidity.Yul.World.DelegatePort
