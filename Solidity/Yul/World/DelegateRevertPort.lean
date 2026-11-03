import Solidity.Yul.World.DelegateRevertBoundary

namespace Solidity.Yul.World.DelegateRevertPort
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.StateCallPhysical (registry)
open Solidity.Yul.World.DelegatePhysical
open Solidity.Yul.World.DelegatePort

def completed {Γ} (G : Glob env) (s : EMState env Γ) (r : ResidualJournal complementCarrierOwnership)
    (b : BoolEncodingJournal) (o : ObservedEffects env.layout env.lay env.lay) := reverted s r b o (errorData G)

theorem heap_eq {Γ} (G : Glob env) (s : EMState env Γ) (r : ResidualJournal complementCarrierOwnership)
    (b : BoolEncodingJournal) (o : ObservedEffects env.layout env.lay env.lay) :
    s.2.heap=(completed G s r b o).1.1.1.2.heap := rfl

/-- Actual selected ordinary revert and strict caller-memory copy, retaining
arbitrary three-journal prefixes. Preparation is the concrete checked Option. -/
def run (G : Glob env) (depth : Nat) (bounded : depth<1024) {Γ} (s : EMState env Γ)
    (sender target : Address) (value gas : Word)
    (classification : target.val≠0 ∧ (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=false)
    (code : (s.2.ex.world.accounts target).code=some 0)
    (r : ResidualJournal complementCarrierOwnership)
    (padding : r.cells (complementKey false account 7)=0xaabbcc00)
    (b : BoolEncodingJournal) (plan : RepresentedSlotPlan (E:=env) registry registry request b)
    (prepared : prepareRepresentedSlot (E:=env) registry registry request b=some plan)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (inputOffset inputSize : Word) (loaded : PhysicalHeapPort.port.load m inputOffset inputSize=some (input G))
    (p : Placement s.2.heap) (e : HeapByteEntry s.2.heap) (outputOffset source size : Word) :=
  HeapOutputTransport.sequenceWindow
    (call (CallerFrame.liftInvoke (invoke true G depth)) s r b o shared m
      (parent s sender value false) .delegatecall target gas 0 inputOffset inputSize)
    (.revert (errorData G),completed G s r b o)
    (DelegateRevertBoundary.call_revert G depth bounded s sender target value gas classification code r padding b plan prepared o shared m inputOffset inputSize loaded)
    rfl s.2.heap (heap_eq G s r b o) p e m outputOffset source size

/-- Full exact state, not event/log projections or a supplied Source run. -/
theorem run_exact (G : Glob env) (depth : Nat) (bounded : depth<1024) {Γ} (s : EMState env Γ)
    (sender target : Address) (value gas : Word)
    (classification : target.val≠0 ∧ (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=false)
    (code : (s.2.ex.world.accounts target).code=some 0)
    (r : ResidualJournal complementCarrierOwnership)
    (padding : r.cells (complementKey false account 7)=0xaabbcc00)
    (b : BoolEncodingJournal) (plan : RepresentedSlotPlan (E:=env) registry registry request b)
    (prepared : prepareRepresentedSlot (E:=env) registry registry request b=some plan)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (inputOffset inputSize : Word) (loaded : PhysicalHeapPort.port.load m inputOffset inputSize=some (input G))
    (p : Placement s.2.heap) (e : HeapByteEntry s.2.heap) (outputOffset source size : Word) (bytes : Bytes)
    (sourceWindow : returnWindow (errorData G) source.val size.val=some bytes)
    (inside : outputOffset.val+bytes.length≤e.bytes.length)
    (header : (mload m (p.address e.id)).val=e.bytes.length)
    (reads : readBytes m (p.address e.id+32) e.bytes.length=e.bytes) :
    run G depth bounded s sender target value gas classification code r padding b plan prepared o shared m inputOffset inputSize loaded p e outputOffset source size=
      some (.ok (.revert (errorData G)),HeapOutputTransport.image (completed G s r b o)
        s.2.heap (heap_eq G s r b o) p e m outputOffset bytes) := by
  rw [run,HeapOutputTransport.sequenceWindow_exact]
  exact congrArg (fun x=>some ((Except.ok (Outcome.revert (errorData G)) : Except Halt Outcome),x))
    (HeapOutputTransport.window_exact (completed G s r b o) rfl s.2.heap (heap_eq G s r b o) p e m outputOffset source size bytes sourceWindow inside header reads)

theorem argument_copy (G : Glob env) (depth : Nat) (bounded : depth<1024) {Γ} (s : EMState env Γ)
    (sender target : Address) (value gas : Word)
    (classification : target.val≠0 ∧ (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=false)
    (code : (s.2.ex.world.accounts target).code=some 0)
    (r : ResidualJournal complementCarrierOwnership)
    (padding : r.cells (complementKey false account 7)=0xaabbcc00)
    (b : BoolEncodingJournal) (plan : RepresentedSlotPlan (E:=env) registry registry request b)
    (prepared : prepareRepresentedSlot (E:=env) registry registry request b=some plan)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (inputOffset inputSize : Word) (loaded : PhysicalHeapPort.port.load m inputOffset inputSize=some (input G))
    (p : Placement s.2.heap) (e : HeapByteEntry s.2.heap) (outputOffset : Word)
    (inside : outputOffset.val+2≤e.bytes.length)
    (header : (mload m (p.address e.id)).val=e.bytes.length)
    (reads : readBytes m (p.address e.id+32) e.bytes.length=e.bytes) :
    run G depth bounded s sender target value gas classification code r padding b plan prepared o shared m inputOffset inputSize loaded p e outputOffset 4 2=
      some (.ok (.revert (errorData G)),HeapOutputTransport.image (completed G s r b o)
        s.2.heap (heap_eq G s r b o) p e m outputOffset [0x11,0x22]) := by
  apply run_exact
  · exact StateCallExtra.error_window G
  · simpa only [List.length_cons,List.length_nil,Nat.add_zero] using inside
  · exact header
  · exact reads

theorem exact_end_zero (G : Glob env) (depth : Nat) (bounded : depth<1024) {Γ} (s : EMState env Γ)
    (sender target : Address) (value gas : Word)
    (classification : target.val≠0 ∧ (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=false)
    (code : (s.2.ex.world.accounts target).code=some 0)
    (r : ResidualJournal complementCarrierOwnership)
    (padding : r.cells (complementKey false account 7)=0xaabbcc00)
    (b : BoolEncodingJournal) (plan : RepresentedSlotPlan (E:=env) registry registry request b)
    (prepared : prepareRepresentedSlot (E:=env) registry registry request b=some plan)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (inputOffset inputSize : Word) (loaded : PhysicalHeapPort.port.load m inputOffset inputSize=some (input G))
    (p : Placement s.2.heap) (e : HeapByteEntry s.2.heap) (outputOffset : Word)
    (inside : outputOffset.val≤e.bytes.length)
    (header : (mload m (p.address e.id)).val=e.bytes.length)
    (reads : readBytes m (p.address e.id+32) e.bytes.length=e.bytes) :
    run G depth bounded s sender target value gas classification code r padding b plan prepared o shared m inputOffset inputSize loaded p e outputOffset 36 0=
      some (.ok (.revert (errorData G)),HeapOutputTransport.image (completed G s r b o)
        s.2.heap (heap_eq G s r b o) p e m outputOffset []) := by
  apply run_exact
  · exact DelegateOutputFailure.exact_end_window G
  · simpa only [List.length_cons,List.length_nil,Nat.add_zero] using inside
  · exact header
  · exact reads

theorem out_of_source_zero (G : Glob env) (depth : Nat) (bounded : depth<1024) {Γ} (s : EMState env Γ)
    (sender target : Address) (value gas : Word)
    (classification : target.val≠0 ∧ (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=false)
    (code : (s.2.ex.world.accounts target).code=some 0)
    (r : ResidualJournal complementCarrierOwnership)
    (padding : r.cells (complementKey false account 7)=0xaabbcc00)
    (b : BoolEncodingJournal) (plan : RepresentedSlotPlan (E:=env) registry registry request b)
    (prepared : prepareRepresentedSlot (E:=env) registry registry request b=some plan)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (inputOffset inputSize : Word) (loaded : PhysicalHeapPort.port.load m inputOffset inputSize=some (input G))
    (p : Placement s.2.heap) (e : HeapByteEntry s.2.heap) (outputOffset : Word) :
    run G depth bounded s sender target value gas classification code r padding b plan prepared o shared m inputOffset inputSize loaded p e outputOffset 37 0=some (.ok (.revert (errorData G)),(completed G s r b o,none)) := by
  rw [run,HeapOutputTransport.sequenceWindow_exact]
  apply congrArg (fun x=>some ((Except.ok (Outcome.revert (errorData G)) : Except Halt Outcome),x))
  apply HeapOutputTransport.window_bad_source
  change (errorData G).length<(37 : Word).val+(0 : Word).val
  rw [StateCallExtra.error_length]
  decide

/-- Existing fixed encoding specialization reuses DelegatePort.call_revert
DIRECTLY; arbitrary-prefix run above extends the same actual producer. -/
def runBefore (G : Glob env) (depth : Nat) (bounded : depth<1024) {Γ} (s : EMState env Γ)
    (sender target : Address) (value gas : Word)
    (classification : target.val≠0 ∧ (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=false)
    (code : (s.2.ex.world.accounts target).code=some 0)
    (r : ResidualJournal complementCarrierOwnership)
    (padding : r.cells (complementKey false account 7)=0xaabbcc00)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (inputOffset inputSize : Word) (loaded : PhysicalHeapPort.port.load m inputOffset inputSize=some (input G))
    (p : Placement s.2.heap) (e : HeapByteEntry s.2.heap) (outputOffset source size : Word) :=
  HeapOutputTransport.sequenceWindow
    (call (CallerFrame.liftInvoke (invoke true G depth)) s r before o shared m
      (parent s sender value false) .delegatecall target gas 0 inputOffset inputSize)
    (.revert (errorData G),completed G s r before o)
    (DelegatePort.call_revert G depth bounded s sender target value gas classification code r padding o shared m inputOffset inputSize loaded)
    rfl s.2.heap (heap_eq G s r before o) p e m outputOffset source size

theorem before_agrees (G : Glob env) (depth : Nat) (bounded : depth<1024) {Γ} (s : EMState env Γ)
    (sender target : Address) (value gas : Word)
    (classification : target.val≠0 ∧ (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=false)
    (code : (s.2.ex.world.accounts target).code=some 0)
    (r : ResidualJournal complementCarrierOwnership)
    (padding : r.cells (complementKey false account 7)=0xaabbcc00)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (inputOffset inputSize : Word) (loaded : PhysicalHeapPort.port.load m inputOffset inputSize=some (input G))
    (p : Placement s.2.heap) (e : HeapByteEntry s.2.heap) (outputOffset source size : Word) :
    runBefore G depth bounded s sender target value gas classification code r padding o shared m inputOffset inputSize loaded p e outputOffset source size=
    run G depth bounded s sender target value gas classification code r padding before DelegatePhysical.plan
      (Option.some_get DelegatePhysical.ready).symm o shared m inputOffset inputSize loaded p e outputOffset source size := rfl

end Solidity.Yul.World.DelegateRevertPort
