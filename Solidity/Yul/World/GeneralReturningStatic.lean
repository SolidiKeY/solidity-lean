import Solidity.Yul.World.GeneralReturningFrame

namespace Solidity.Yul.World.GeneralReturning
open Solidity.Source
open Solidity.Roadmap (Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.ReturningCall (env glob input output)

/-- Real selected STATICCALL source body for arbitrary initial execution.
The zero transfer result is explicit, including its actual journal entries. -/
theorem static_source (G : Glob env) (s : EMState env [])
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 0=some next) :
    (Source.callAddr (glob G) ReturningCall.parentFrame 10 CallerFrameChecks.receiver 0 (input G) true).run s=
      (.ok (.success output),after s next) := by
  simp only [Source.callAddr,ReturningCall.parentFrame,show ¬(0 ≥ 1024) from by decide,if_false,
    Bool.false_and,Bool.false_eq_true,Source.Hoare.run_bind,ReturningCall.run_pure,
    SourceBoundaryRules.selected_at_code G s code,ReturningCall.run_mark,ReturningCall.run_st,
    show CallerFrameChecks.receiver≠CallerFrameChecks.owner from by decide,transfer,
    ReturningCall.run_modSt,Bool.not_true,Bool.true_or,after]
  rw [ReturningStatic.enter_run]

theorem static_invoke_empty (G : Glob env) (s : EMState env [])
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 0=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (gas : Word) :
    ReturningStatic.invoke G o (enter s r (ReturningCall.parent s) .staticcall CallerFrameChecks.receiver 0 (input G))
      .staticcall CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩=
      some ((.ok (.success output),⟨⟨after s next,r⟩,b⟩),[]) := by
  have ran := static_source G s next code transfer
  unfold ReturningStatic.invoke ReturningStatic.invokeAt
  change (if decide ((s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0) then
    some (ReturningCall.pack ⟨⟨s,r⟩,b⟩ ((Source.callAddr (glob G) ReturningCall.parentFrame 10
      CallerFrameChecks.receiver 0 (input G) true).run s)) else none)=_
  rw [code]
  change some (ReturningCall.pack ⟨⟨s,r⟩,b⟩ ((Source.callAddr (glob G) ReturningCall.parentFrame 10
      CallerFrameChecks.receiver 0 (input G) true).run s))=_
  rw [ran]
  simp only [ReturningCall.pack,after,List.drop_length,List.map_nil]

theorem static_invoke (G : Glob env) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 0=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (gas : Word) :
    CallerFrame.liftInvoke (ReturningStatic.invoke G) o
      (enter s r (ReturningCall.parent s) .staticcall CallerFrameChecks.receiver 0 (input G))
      .staticcall CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩=
      some ((.ok (.success output),⟨⟨after s next,r⟩,b⟩),[]) :=
  CallerFrame.liftInvoke_exact (ReturningStatic.invoke G) o
    (enter s r (ReturningCall.parent s) .staticcall CallerFrameChecks.receiver 0 (input G))
    .staticcall CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩ (.ok (.success output))
    ⟨⟨after (⟨Source.L0 env,s.2⟩ : EMState env []) next,r⟩,b⟩ []
    (static_invoke_empty G ⟨Source.L0 env,s.2⟩ next code transfer r b o gas)

theorem static_call (G : Glob env) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 0=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (gas offset size : Word)
    (loaded : PhysicalHeapPort.port.load m offset size=some (input G)) :
    call (CallerFrame.liftInvoke (ReturningStatic.invoke G)) s r b o shared m (ReturningCall.parent s)
      .staticcall CallerFrameChecks.receiver gas 0 offset size=some (.ok (.success output),successResult s next r b o) := by
  rw [call_normal_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl loaded
    (static_invoke G s next code transfer r b o gas)]
  simp only [finish_success,List.append_nil,successResult,after]

theorem static_encoded (G : Glob env) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 0=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (p : Placement s.2.heap) (es : List (HeapByteEntry s.2.heap))
    (distinct : (es.map HeapByteEntry.id).Nodup) (e : HeapByteEntry s.2.heap)
    (member : e ∈ es) (bytes : e.bytes=input G) (background : ByteView) (gas : Word) :
    call (CallerFrame.liftInvoke (ReturningStatic.invoke G)) s r b o shared (encodeByteHeap p es background)
      (ReturningCall.parent s) .staticcall CallerFrameChecks.receiver gas 0
      (PhysicalHeapPort.payloadOffset s.2.heap p e.id e.string e.bytes e.found)
      ⟨e.bytes.length,heapByte_length_bound s.2.heap p e.id e.string e.bytes e.found⟩=
      some (.ok (.success output),successResult s next r b o) := by
  apply static_call G s next code transfer r b o shared
  exact (PhysicalHeapPort.load_encoded s.2.heap p es distinct e member background).trans (congrArg some bytes)

/-- Same actual re-encoders under zero-value transfer; no cleaning/projection. -/
theorem static_represented_views {Γ} (s : EMState env Γ) (next : ExecState env.layout env.lay env.lay)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 0=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (ps ts : (a : Roadmap.Address) → List (ScalarPath env.layout (env.lay a))) (a : Roadmap.Address) (q : Word) :
    reencodePersistentSlot (representedBanks ps false b) ⟨next,r⟩ a q=
      reencodePersistentSlot (representedBanks ps false b) ⟨s.2.ex,r⟩ a q ∧
    reencodeTransientSlot (representedBanks ts true b) ⟨next,r⟩ a q=
      reencodeTransientSlot (representedBanks ts true b) ⟨s.2.ex,r⟩ a q := by
  have keep := transfer_storage s.2.ex next CallerFrameChecks.owner CallerFrameChecks.receiver 0 (by decide) transfer
  constructor
  · unfold reencodePersistentSlot
    rw [keep.1 a]
  · unfold reencodeTransientSlot
    rw [keep.2]

end Solidity.Yul.World.GeneralReturning
