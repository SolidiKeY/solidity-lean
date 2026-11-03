import Solidity.Yul.World.DelegateOutputRules

/-! Actual selected ordinary revert over arbitrary caller/physical prefixes.
The checked preparation premise is the real VY2 Option equality, not a run,
outcome or world adequacy certificate. No producer bodies are changed. -/
namespace Solidity.Yul.World.DelegateRevertBoundary
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.StateCallPhysical (registry)
open Solidity.Yul.World.DelegatePhysical
open Solidity.Yul.World.DelegatePort

theorem invoke_empty (G : Glob env) (depth : Nat) (bounded : depth<1024)
    (s : EMState env []) (sender target : Address) (v gas : Word)
    (classification : target.val≠0 ∧ (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=false)
    (code : (s.2.ex.world.accounts target).code=some 0)
    (r : ResidualJournal complementCarrierOwnership)
    (padding : r.cells (complementKey false account 7)=0xaabbcc00)
    (o : ObservedEffects env.layout env.lay env.lay) (b : BoolEncodingJournal)
    (p : RepresentedSlotPlan (E:=env) registry registry request b)
    (prepared : prepareRepresentedSlot (E:=env) registry registry request b=some p) :
    invoke true G depth o (enter s r (parent s sender v false) .delegatecall target 0 (input G))
      .delegatecall target gas (input G) ⟨⟨s,r⟩,b⟩=
      some ((.ok (.revert (errorData G)),⟨⟨s,r⟩,b⟩),[]) := by
  unfold invoke
  simp only [enter,parent,childContext,ExecState.enter,classification.2,bounded,decide_true,Bool.not_false,Bool.and_true,Bool.false_eq_true,if_false,prepared,if_pos padding,bind,Option.bind_some]
  rw [DelegateEntry.revert_exact G account sender target v (depth+1) s code]
  have physical : (PhysicalSlotPort.step registry registry request b
      (DelegateBody.frame account sender v (depth+1)) p s r
      ({o with effects:={o.effects with execution:=s.2.ex}} : ObservedEffects env.layout env.lay env.lay) rfl rfl).1=
      (((.ok (),(s.1,{s.2 with ex:=s.2.ex.apply p.packed.sourceOp})),residualWrite r p.packed.residualUpdate),
        requestEncoding (E:=env) registry registry request b) := by
    unfold PhysicalSlotPort.step
    rw [representedSourceStep_nonstatic _ _ _ _ rfl]
  rw [physical]
  have res:=residualRollback_run r [p.packed.residualUpdate]
  have enc:=boolEncodingRollback_run b
    (encodingWrites (selectedSlotPaths (registry request.address) request.slot) false request.address (fun _=>request.raw) b)
  simp only [residualRun] at res
  change boolEncodingRollback b.journal.length (requestEncoding (E:=env) registry registry request b)=b at enc
  simp only [Option.bind_some,res,enc,List.drop_length,List.map_nil]
  simp only [Bool.true_and,decide_eq_true_eq,if_pos classification.1]
  rfl

theorem invoke_actual (G : Glob env) (depth : Nat) (bounded : depth<1024) {Γ} (s : EMState env Γ)
    (sender target : Address) (value gas : Word)
    (classification : target.val≠0 ∧ (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=false)
    (code : (s.2.ex.world.accounts target).code=some 0)
    (r : ResidualJournal complementCarrierOwnership)
    (padding : r.cells (complementKey false account 7)=0xaabbcc00)
    (b : BoolEncodingJournal) (p : RepresentedSlotPlan (E:=env) registry registry request b)
    (prepared : prepareRepresentedSlot (E:=env) registry registry request b=some p)
    (o : ObservedEffects env.layout env.lay env.lay) :
    CallerFrame.liftInvoke (invoke true G depth) o
      (enter s r (parent s sender value false) .delegatecall target 0 (input G))
      .delegatecall target gas (input G) ⟨⟨s,r⟩,b⟩=
      some ((.ok (.revert (errorData G)),⟨⟨s,r⟩,b⟩),[]) :=
  CallerFrame.liftInvoke_exact (invoke true G depth) o
    (enter s r (parent s sender value false) .delegatecall target 0 (input G))
    .delegatecall target gas (input G) ⟨⟨s,r⟩,b⟩ (.ok (.revert (errorData G)))
    ⟨⟨⟨Source.L0 env,s.2⟩,r⟩,b⟩ []
    (invoke_empty G depth bounded ⟨Source.L0 env,s.2⟩ sender target value gas classification code r padding o b p prepared)

theorem call_revert (G : Glob env) (depth : Nat) (bounded : depth<1024) {Γ} (s : EMState env Γ)
    (sender target : Address) (value gas : Word)
    (classification : target.val≠0 ∧ (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=false)
    (code : (s.2.ex.world.accounts target).code=some 0)
    (r : ResidualJournal complementCarrierOwnership)
    (padding : r.cells (complementKey false account 7)=0xaabbcc00)
    (b : BoolEncodingJournal) (p : RepresentedSlotPlan (E:=env) registry registry request b)
    (prepared : prepareRepresentedSlot (E:=env) registry registry request b=some p)
    (o : ObservedEffects env.layout env.lay env.lay)
    (shared : o.effects.execution=s.2.ex) (m : ByteView) (inputOffset inputSize : Word)
    (loaded : PhysicalHeapPort.port.load m inputOffset inputSize=some (input G)) :
    call (CallerFrame.liftInvoke (invoke true G depth)) s r b o shared m
      (parent s sender value false) .delegatecall target gas 0 inputOffset inputSize=
      some (.ok (.revert (errorData G)),reverted s r b o (errorData G)) := by
  rw [call_normal_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl loaded
    (invoke_actual G depth bounded s sender target value gas classification code r padding b p prepared o)]
  have clean:=finish_runs_revert s r b o [] [] [] account sender value (input G) false [] (errorData G)
  simpa only [ExecState.run,residualRun,boolEncodingRun,rollbackTrace,discardLogs,List.append_nil] using
    congrArg (fun x=>some ((Except.ok (.revert (errorData G)) : Except Halt Outcome),x)) clean
end Solidity.Yul.World.DelegateRevertBoundary
