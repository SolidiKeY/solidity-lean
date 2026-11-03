import Solidity.Yul.World.DelegateChecks
namespace Solidity.Yul.World.DelegatePending
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.DelegatePhysical
open Solidity.Yul.World.DelegatePort

/-- Same real selected body with a smaller horizon. No write has occurred;
all physical banks and the old returndata remain pending, not reverted. -/
def invoke (failed : Bool) (G : Glob env) (depth : Nat) : Invoke env [] :=
  fun _ frame kind target _ bytes c=>match kind with
  | .delegatecall =>
    if decide (frame.source.this=account) && decide (target.val≠0) && !(Roadmap.Evm.Precompile.ofAddress? target.val).isSome &&
      decide (depth<1024) && decide (bytes=input G) && !frame.source.static then do
      let actual ← DelegateEntry.execute failed G account frame.source.caller target frame.source.value (depth+1) 5 bytes c.1.1
      pure (StateCallPort.staticPack c actual)
    else none
  | .call | .staticcall => none

theorem empty_actual (failed : Bool) (G : Glob env) (depth : Nat) (bounded : depth<1024)
    (s : EMState env []) (sender target : Address) (v gas : Word)
    (classification : target.val≠0 ∧ (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=false)
    (code : (s.2.ex.world.accounts target).code=some 0)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) :
    invoke failed G depth o (enter s r (parent s sender v false) .delegatecall target 0 (input G))
      .delegatecall target gas (input G) ⟨⟨s,r⟩,b⟩=some ((.error .timeout,⟨⟨s,r⟩,b⟩),[]) := by
  simp only [invoke,enter,parent,childContext,ExecState.enter,classification.2,bounded,decide_true,
    Bool.not_false,Bool.and_true]
  rw [DelegateEntry.timeout failed G account sender target v (depth+1) s code]
  simp only [bind,Option.bind_some,StateCallPort.staticPack,List.drop_length,List.map_nil]
  simp only [Bool.true_and,decide_eq_true_eq,if_pos classification.1]
  rfl

theorem actual (failed : Bool) (G : Glob env) (depth : Nat) (bounded : depth<1024)
    {Γ} (s : EMState env Γ) (sender target : Address) (v gas : Word)
    (classification : target.val≠0 ∧ (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=false)
    (code : (s.2.ex.world.accounts target).code=some 0)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) :
    CallerFrame.liftInvoke (invoke failed G depth) o (enter s r (parent s sender v false) .delegatecall target 0 (input G))
      .delegatecall target gas (input G) ⟨⟨s,r⟩,b⟩=some ((.error .timeout,⟨⟨s,r⟩,b⟩),[]) :=
  CallerFrame.liftInvoke_exact (invoke failed G depth) o (enter s r (parent s sender v false) .delegatecall target 0 (input G))
    .delegatecall target gas (input G) ⟨⟨s,r⟩,b⟩ (.error .timeout)
    ⟨⟨⟨Source.L0 env,s.2⟩,r⟩,b⟩ [] (empty_actual failed G depth bounded ⟨Source.L0 env,s.2⟩ sender target v gas classification code r b o)

theorem call_pending (failed : Bool) (G : Glob env) (depth : Nat) (bounded : depth<1024)
    {Γ} (s : EMState env Γ) (sender target : Address) (v gas : Word)
    (classification : target.val≠0 ∧ (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=false)
    (code : (s.2.ex.world.accounts target).code=some 0)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (offset size : Word) (loaded : PhysicalHeapPort.port.load m offset size=some (input G)) :
    call (CallerFrame.liftInvoke (invoke failed G depth)) s r b o shared m
      (parent s sender v false) .delegatecall target gas 0 offset size=
      some (.error .timeout,pending o ⟨⟨s,r⟩,b⟩ []) :=
  call_exact _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl loaded
    (actual failed G depth bounded s sender target v gas classification code r b o)

theorem witnessed (failed : Bool) (G : Glob env) :
    call (CallerFrame.liftInvoke (invoke failed G 0)) (StateCallChecks.caller G) StateCallChecks.residual before
      StateCallChecks.observed rfl (StateCallChecks.memory G)
      (parent (StateCallChecks.caller G) DelegateChecks.sender DelegateChecks.value false)
      .delegatecall DelegateChecks.target 10000 0 160 4=
      some (.error .timeout,pending StateCallChecks.observed ⟨⟨StateCallChecks.caller G,StateCallChecks.residual⟩,before⟩ []) :=
  call_pending failed G 0 (by decide) _ _ _ _ _ (by decide) rfl _ _ _ rfl _ _ _ (StateCallChecks.loaded G)
end Solidity.Yul.World.DelegatePending
