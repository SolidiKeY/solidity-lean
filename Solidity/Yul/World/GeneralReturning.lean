import Solidity.Yul.World.SourceBoundaryRules

/-! Actual selected Source producer -> full physical call adapter, with
arbitrary caller worlds, locals/heaps and all journal/observation prefixes.
The existing ReturningCall.invoke is executed unchanged. Code/transfer facts
are real source-operation premises, not supplied outcomes or adequacy laws.
The program/selector/owner/receiver/value/depth/horizon stay selected; no gas,
generic callee, universal layout or full Source/Yul/G01 adequacy is inferred. -/
namespace Solidity.Yul.World.GeneralReturning
open Solidity.Source
open Solidity.Roadmap (Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.ReturningCall (env glob input output)

/-- Same source state carrier, with only the actual returned execution changed. -/
def after {Γ} (s : EMState env Γ) (next : ExecState env.layout env.lay env.lay) : EMState env Γ :=
  ⟨s.1,{s.2 with ex:=next}⟩

def successResult {Γ} (s : EMState env Γ) (next : ExecState env.layout env.lay env.lay)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) : Result env Γ :=
  (⟨⟨after s next,r⟩,b⟩,⟨⟨next,committedLogs o.trace,output⟩,o.trace,rfl⟩)

theorem invoke_empty (G : Glob env) (s : EMState env [])
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (gas : Word) :
    ReturningCall.invoke G o (enter s r (ReturningCall.parent s) .call CallerFrameChecks.receiver 7 (input G))
      .call CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩=
      some ((.ok (.success output),⟨⟨after s next,r⟩,b⟩),[]) := by
  have ran := SourceBoundaryRules.source_success_at_transfer G s next code transfer
  unfold ReturningCall.invoke ReturningCall.invokeAt ReturningCall.invokeTemplateAt ReturningCall.template
  change (if decide ((s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0) then
    some (ReturningCall.pack ⟨⟨s,r⟩,b⟩ ((Source.callAddr (glob G) ReturningCall.parentFrame 10
      CallerFrameChecks.receiver 7 (input G) false).run s)) else none)=_
  rw [code]
  change some (ReturningCall.pack ⟨⟨s,r⟩,b⟩ ((Source.callAddr (glob G) ReturningCall.parentFrame 10
      CallerFrameChecks.receiver 7 (input G) false).run s))=_
  rw [ran]
  simp only [ReturningCall.pack,after,List.drop_length,List.map_nil]

theorem invoke_actual (G : Glob env) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (gas : Word) :
    CallerFrame.liftInvoke (ReturningCall.invoke G) o
      (enter s r (ReturningCall.parent s) .call CallerFrameChecks.receiver 7 (input G))
      .call CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩=
      some ((.ok (.success output),⟨⟨after s next,r⟩,b⟩),[]) :=
  CallerFrame.liftInvoke_exact (ReturningCall.invoke G) o
    (enter s r (ReturningCall.parent s) .call CallerFrameChecks.receiver 7 (input G))
    .call CallerFrameChecks.receiver gas (input G) ⟨⟨s,r⟩,b⟩ (.ok (.success output))
    ⟨⟨after (⟨Source.L0 env,s.2⟩ : EMState env []) next,r⟩,b⟩ []
    (invoke_empty G ⟨Source.L0 env,s.2⟩ next code transfer r b o gas)

/-- Actual complete call result for arbitrary source worlds and contexts. The
input-load premise is discharged constructively from a real VY2 heap below. -/
theorem call_actual (G : Glob env) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (gas offset size : Word)
    (loaded : PhysicalHeapPort.port.load m offset size=some (input G)) :
    call (CallerFrame.liftInvoke (ReturningCall.invoke G)) s r b o shared m (ReturningCall.parent s)
      .call CallerFrameChecks.receiver gas 7 offset size=some (.ok (.success output),successResult s next r b o) := by
  rw [call_normal_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl loaded
    (invoke_actual G s next code transfer r b o gas)]
  simp only [finish_success,List.append_nil,successResult,after]

/-- Real finite heap byte image, actual placement-derived offset and bounds.
No arbitrary-byte-view-for-arbitrary-source-heap identification is assumed. -/
theorem call_encoded (G : Glob env) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (p : Placement s.2.heap) (es : List (HeapByteEntry s.2.heap))
    (distinct : (es.map HeapByteEntry.id).Nodup) (e : HeapByteEntry s.2.heap)
    (member : e ∈ es) (bytes : e.bytes=input G) (background : ByteView) (gas : Word) :
    call (CallerFrame.liftInvoke (ReturningCall.invoke G)) s r b o shared (encodeByteHeap p es background)
      (ReturningCall.parent s) .call CallerFrameChecks.receiver gas 7
      (PhysicalHeapPort.payloadOffset s.2.heap p e.id e.string e.bytes e.found)
      ⟨e.bytes.length,heapByte_length_bound s.2.heap p e.id e.string e.bytes e.found⟩=
      some (.ok (.success output),successResult s next r b o) := by
  apply call_actual G s next code transfer r b o shared
  exact (PhysicalHeapPort.load_encoded s.2.heap p es distinct e member background).trans (congrArg some bytes)

theorem full_frame {Γ} (s : EMState env Γ) next r b o :
    (successResult s next r b o).1.1.1.1=s.1 ∧
    (successResult s next r b o).1.1.1.2.heap=s.2.heap ∧
    (successResult s next r b o).1.1.1.2.fnLocals=s.2.fnLocals ∧
    (successResult s next r b o).1.1.1.2.events=s.2.events ∧
    (successResult s next r b o).1.1.1.2.logs=s.2.logs ∧
    (successResult s next r b o).1.1.2=r ∧ (successResult s next r b o).1.2=b ∧
    (successResult s next r b o).2.trace=o.trace ∧
    (successResult s next r b o).2.effects.returndata=output :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Actual bounded output writeback after the concrete source-produced full
result. Exact heap ownership/placement/header/payload/extent remain explicit. -/
theorem copy_output {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay)
    (p : Placement s.2.heap) (a : Nat) (string : Bool) (old : Bytes)
    (found : s.2.heap.get a=some ⟨heapByteType string,heapByteData env.layout string old⟩)
    (m : ByteView) (offset capacity : Word)
    (inside : offset.val+min capacity.val output.length≤old.length)
    (header : (mload m (p.address a)).val=old.length)
    (payload : readBytes m (p.address a+32) old.length=old) :
    copyOutput (successResult s next r b o) rfl p a string old found m offset capacity=
      (successResult s next r b o,some
        ((Solidity.Backend.Environment.writeBytes m (p.address a+32+offset.val) (callOutput output capacity.val),
          withSourceHeap (after s next) (s.2.heap.write a
            (heapByteData env.layout string (HeapWindow.splice old offset.val (callOutput output capacity.val)))
            (heap_ty_of_get _ a _ _ found))),(r,b),(successResult s next r b o).2)) :=
  copyOutput_exact (successResult s next r b o) rfl p a string old found m offset capacity inside header payload

end Solidity.Yul.World.GeneralReturning
