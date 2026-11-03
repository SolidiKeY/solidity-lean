import Solidity.Yul.World.DelegatePort
namespace Solidity.Yul.World.DelegatePort
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.DelegatePhysical

def successful {Γ} (s : EMState env Γ) (r : ResidualJournal complementCarrierOwnership)
    (o : ObservedEffects env.layout env.lay env.lay) : Result env Γ :=
  (carrier s r,⟨⟨(changed s account).2.ex,committedLogs o.trace,ReturningCall.output⟩,o.trace,rfl⟩)
def reverted {Γ} (s : EMState env Γ) (r : ResidualJournal complementCarrierOwnership)
    (b : BoolEncodingJournal) (o : ObservedEffects env.layout env.lay env.lay) (data : Bytes) : Result env Γ :=
  (⟨⟨s,r⟩,b⟩,⟨⟨s.2.ex,committedLogs o.trace,data⟩,o.trace,rfl⟩)

theorem success_actual (G : Glob env) (depth : Nat) (bounded : depth<1024) {Γ} (s : EMState env Γ)
    (sender target : Address) (v gas : Word)
    (classification : target.val≠0 ∧ (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=false)
    (code : (s.2.ex.world.accounts target).code=some 0)
    (r : ResidualJournal complementCarrierOwnership)
    (padding : r.cells (complementKey false account 7)=0xaabbcc00)
    (o : ObservedEffects env.layout env.lay env.lay) :
    CallerFrame.liftInvoke (invoke false G depth) o
      (enter s r (parent s sender v false) .delegatecall target 0 (input G))
      .delegatecall target gas (input G) ⟨⟨s,r⟩,before⟩=some ((.ok (.success ReturningCall.output),carrier s r),[]) :=
  CallerFrame.liftInvoke_exact (invoke false G depth) o
    (enter s r (parent s sender v false) .delegatecall target 0 (input G))
    .delegatecall target gas (input G) ⟨⟨s,r⟩,before⟩ (.ok (.success ReturningCall.output))
    (carrier ⟨Source.L0 env,s.2⟩ r) [] (success_empty G depth bounded ⟨Source.L0 env,s.2⟩ sender target v gas classification code r padding o)

theorem revert_actual (G : Glob env) (depth : Nat) (bounded : depth<1024) {Γ} (s : EMState env Γ)
    (sender target : Address) (v gas : Word)
    (classification : target.val≠0 ∧ (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=false)
    (code : (s.2.ex.world.accounts target).code=some 0)
    (r : ResidualJournal complementCarrierOwnership)
    (padding : r.cells (complementKey false account 7)=0xaabbcc00)
    (o : ObservedEffects env.layout env.lay env.lay) :
    CallerFrame.liftInvoke (invoke true G depth) o
      (enter s r (parent s sender v false) .delegatecall target 0 (input G))
      .delegatecall target gas (input G) ⟨⟨s,r⟩,before⟩=some ((.ok (.revert (errorData G)),⟨⟨s,r⟩,before⟩),[]) :=
  CallerFrame.liftInvoke_exact (invoke true G depth) o
    (enter s r (parent s sender v false) .delegatecall target 0 (input G))
    .delegatecall target gas (input G) ⟨⟨s,r⟩,before⟩ (.ok (.revert (errorData G)))
    (⟨⟨⟨Source.L0 env,s.2⟩,r⟩,before⟩) [] (revert_empty G depth bounded ⟨Source.L0 env,s.2⟩ sender target v gas classification code r padding o)

theorem call_success (G : Glob env) (depth : Nat) (bounded : depth<1024) {Γ} (s : EMState env Γ)
    (sender target : Address) (v gas : Word)
    (classification : target.val≠0 ∧ (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=false)
    (code : (s.2.ex.world.accounts target).code=some 0)
    (r : ResidualJournal complementCarrierOwnership)
    (padding : r.cells (complementKey false account 7)=0xaabbcc00)
    (o : ObservedEffects env.layout env.lay env.lay)
    (shared : o.effects.execution=s.2.ex) (m : ByteView) (offset size : Word)
    (loaded : PhysicalHeapPort.port.load m offset size=some (input G)) :
    call (CallerFrame.liftInvoke (invoke false G depth)) s r before o shared m
      (parent s sender v false) .delegatecall target gas 0 offset size=
      some (.ok (.success ReturningCall.output),successful s r o) := by
  rw [call_normal_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl loaded
    (success_actual G depth bounded s sender target v gas classification code r padding o)]
  rw [finish_success]
  simp only [List.append_nil]
  rfl

theorem call_revert (G : Glob env) (depth : Nat) (bounded : depth<1024) {Γ} (s : EMState env Γ)
    (sender target : Address) (v gas : Word)
    (classification : target.val≠0 ∧ (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=false)
    (code : (s.2.ex.world.accounts target).code=some 0)
    (r : ResidualJournal complementCarrierOwnership)
    (padding : r.cells (complementKey false account 7)=0xaabbcc00)
    (o : ObservedEffects env.layout env.lay env.lay)
    (shared : o.effects.execution=s.2.ex) (m : ByteView) (offset size : Word)
    (loaded : PhysicalHeapPort.port.load m offset size=some (input G)) :
    call (CallerFrame.liftInvoke (invoke true G depth)) s r before o shared m
      (parent s sender v false) .delegatecall target gas 0 offset size=
      some (.ok (.revert (errorData G)),reverted s r before o (errorData G)) := by
  rw [call_normal_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl loaded
    (revert_actual G depth bounded s sender target v gas classification code r padding o)]
  have clean:=finish_runs_revert s r before o [] [] [] account sender v (input G) false [] (errorData G)
  simpa only [ExecState.run,residualRun,boolEncodingRun,rollbackTrace,discardLogs,List.append_nil] using
    congrArg (fun x=>some ((Except.ok (.revert (errorData G)) : Except Halt Outcome),x)) clean

theorem enclosing_revert {Γ} (s : EMState env Γ) (sender target : Address) (v : Word)
    (r : ResidualJournal complementCarrierOwnership) (o : ObservedEffects env.layout env.lay env.lay) (data : Bytes) :
    finish s before o (enter s r (parent s sender v false) .delegatecall target 0 [])
      (successful s r o).1 [] (.revert data)=reverted s r before o data :=
  DelegatePhysical.outer_rollback s sender v r o data

theorem static_actual (failed : Bool) (G : Glob env) (depth : Nat) (bounded : depth<1024)
    {Γ} (s : EMState env Γ) (sender target : Address) (v gas : Word)
    (classification : target.val≠0 ∧ (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=false)
    (code : (s.2.ex.world.accounts target).code=some 0)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) :
    CallerFrame.liftInvoke (invoke failed G depth) o (enter s r (parent s sender v true) .delegatecall target 0 (input G))
      .delegatecall target gas (input G) ⟨⟨s,r⟩,b⟩=some ((.ok (.revert []),⟨⟨s,r⟩,b⟩),[]) :=
  CallerFrame.liftInvoke_exact (invoke failed G depth) o (enter s r (parent s sender v true) .delegatecall target 0 (input G))
    .delegatecall target gas (input G) ⟨⟨s,r⟩,b⟩ (.ok (.revert []))
    ⟨⟨⟨Source.L0 env,s.2⟩,r⟩,b⟩ [] (static_empty failed G depth bounded ⟨Source.L0 env,s.2⟩ sender target v gas classification code r b o)

theorem call_static (failed : Bool) (G : Glob env) (depth : Nat) (bounded : depth<1024)
    {Γ} (s : EMState env Γ) (sender target : Address) (v gas : Word)
    (classification : target.val≠0 ∧ (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=false)
    (code : (s.2.ex.world.accounts target).code=some 0)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (offset size : Word) (loaded : PhysicalHeapPort.port.load m offset size=some (input G)) :
    call (CallerFrame.liftInvoke (invoke failed G depth)) s r b o shared m
      (parent s sender v true) .delegatecall target gas 0 offset size=some (.ok (.revert []),reverted s r b o []) := by
  rw [call_normal_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl loaded
    (static_actual failed G depth bounded s sender target v gas classification code r b o)]
  have clean:=finish_runs_revert s r b o [] [] [] account sender v (input G) true [] []
  simpa only [ExecState.run,residualRun,boolEncodingRun,rollbackTrace,discardLogs,List.append_nil] using
    congrArg (fun x=>some ((Except.ok (.revert []) : Except Halt Outcome),x)) clean

end Solidity.Yul.World.DelegatePort
