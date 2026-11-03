import Solidity.Yul.World.DelegateSuccessBoundary

namespace Solidity.Yul.World.DelegateSuccessPort
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.StateCallPhysical (registry)
open Solidity.Yul.World.DelegatePhysical
open Solidity.Yul.World.DelegatePort

open Solidity.Yul.World.DelegateSuccessBoundary (completed)

theorem heap_eq {Γ} (s : EMState env Γ) (r : ResidualJournal complementCarrierOwnership)
    (b : BoolEncodingJournal) (plan : RepresentedSlotPlan (E:=env) registry registry request b)
    (o : ObservedEffects env.layout env.lay env.lay) :
    s.2.heap=(completed s r b plan o).1.1.1.2.heap := rfl

/-- Actual selected ordinary success and strict caller-memory copy, retaining
successful changes to all three journals, with arbitrary prefixes. Preparation is the concrete checked Option. -/
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
    (call (CallerFrame.liftInvoke (invoke false G depth)) s r b o shared m
      (parent s sender value false) .delegatecall target gas 0 inputOffset inputSize)
    (.success ReturningCall.output,completed s r b plan o)
    (DelegateSuccessBoundary.call_success G depth bounded s sender target value gas classification code r padding b plan prepared o shared m inputOffset inputSize loaded)
    rfl s.2.heap (heap_eq s r b plan o) p e m outputOffset source size

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
    (sourceWindow : returnWindow ReturningCall.output source.val size.val=some bytes)
    (inside : outputOffset.val+bytes.length≤e.bytes.length)
    (header : (mload m (p.address e.id)).val=e.bytes.length)
    (reads : readBytes m (p.address e.id+32) e.bytes.length=e.bytes) :
    run G depth bounded s sender target value gas classification code r padding b plan prepared o shared m inputOffset inputSize loaded p e outputOffset source size=
      some (.ok (.success ReturningCall.output),HeapOutputTransport.image (completed s r b plan o)
        s.2.heap (heap_eq s r b plan o) p e m outputOffset bytes) := by
  rw [run,HeapOutputTransport.sequenceWindow_exact]
  exact congrArg (fun x=>some ((Except.ok (Outcome.success ReturningCall.output) : Except Halt Outcome),x))
    (HeapOutputTransport.window_exact (completed s r b plan o) rfl s.2.heap (heap_eq s r b plan o) p e m outputOffset source size bytes sourceWindow inside header reads)

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
    run G depth bounded s sender target value gas classification code r padding b plan prepared o shared m inputOffset inputSize loaded p e outputOffset 0 2=
      some (.ok (.success ReturningCall.output),HeapOutputTransport.image (completed s r b plan o)
        s.2.heap (heap_eq s r b plan o) p e m outputOffset [0x11,0x22]) := by
  apply run_exact
  · exact (by decide : returnWindow ReturningCall.output 0 2=some [0x11,0x22])
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
    run G depth bounded s sender target value gas classification code r padding b plan prepared o shared m inputOffset inputSize loaded p e outputOffset 32 0=
      some (.ok (.success ReturningCall.output),HeapOutputTransport.image (completed s r b plan o)
        s.2.heap (heap_eq s r b plan o) p e m outputOffset []) := by
  apply run_exact
  · exact (by decide : returnWindow ReturningCall.output 32 0=some [])
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
    run G depth bounded s sender target value gas classification code r padding b plan prepared o shared m inputOffset inputSize loaded p e outputOffset 33 0=some (.ok (.success ReturningCall.output),(completed s r b plan o,none)) := by
  rw [run,HeapOutputTransport.sequenceWindow_exact]
  apply congrArg (fun x=>some ((Except.ok (Outcome.success ReturningCall.output) : Except Halt Outcome),x))
  apply HeapOutputTransport.window_bad_source
  change ReturningCall.output.length<(33 : Word).val+(0 : Word).val
  decide

end Solidity.Yul.World.DelegateSuccessPort
