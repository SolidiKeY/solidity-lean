import Solidity.Yul.World.DelegateSuccessPort

/-! Actual low-level output truncation also happens on ordinary success.
This is separate from strict RETURNDATACOPY and never shrinks the last buffer. -/
namespace Solidity.Yul.World.DelegateSuccessOutput
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.StateCallPhysical (registry)
open Solidity.Yul.World.DelegatePhysical
open Solidity.Yul.World.DelegatePort
open Solidity.Yul.World.DelegateSuccessPort
open Solidity.Yul.World.DelegateSuccessBoundary (completed)

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
    (p : Placement s.2.heap) (e : HeapByteEntry s.2.heap) (outputOffset capacity : Word) :=
  HeapOutputTransport.sequence
    (call (CallerFrame.liftInvoke (invoke false G depth)) s r b o shared m
      (parent s sender value false) .delegatecall target gas 0 inputOffset inputSize)
    (.success ReturningCall.output,completed s r b plan o)
    (DelegateSuccessBoundary.call_success G depth bounded s sender target value gas classification code r padding b plan prepared o shared m inputOffset inputSize loaded)
    rfl s.2.heap (heap_eq s r b plan o) p e m outputOffset capacity

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
    (p : Placement s.2.heap) (e : HeapByteEntry s.2.heap) (outputOffset capacity : Word)
    (inside : outputOffset.val+min capacity.val ReturningCall.output.length≤e.bytes.length)
    (header : (mload m (p.address e.id)).val=e.bytes.length)
    (reads : readBytes m (p.address e.id+32) e.bytes.length=e.bytes) :
    run G depth bounded s sender target value gas classification code r padding b plan prepared o shared m inputOffset inputSize loaded p e outputOffset capacity=
      some (.ok (.success ReturningCall.output),HeapOutputTransport.image (completed s r b plan o)
        s.2.heap (heap_eq s r b plan o) p e m outputOffset (callOutput ReturningCall.output capacity.val)) := by
  rw [run,HeapOutputTransport.sequence_exact]
  exact congrArg (fun x=>some ((Except.ok (Outcome.success ReturningCall.output) : Except Halt Outcome),x))
    (HeapOutputTransport.exact_copy (completed s r b plan o) rfl s.2.heap (heap_eq s r b plan o) p e m outputOffset capacity inside header reads)

/-- Local postcondition substitution rule over the actual complete result;
Lean-only, not an intrinsic Yul/G51 calculus certificate. -/
theorem post_rule (G : Glob env) (depth : Nat) (bounded : depth<1024) {Γ} (s : EMState env Γ)
    (sender target : Address) (value gas : Word)
    (classification : target.val≠0 ∧ (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=false)
    (code : (s.2.ex.world.accounts target).code=some 0)
    (r : ResidualJournal complementCarrierOwnership)
    (padding : r.cells (complementKey false account 7)=0xaabbcc00)
    (b : BoolEncodingJournal) (plan : RepresentedSlotPlan (E:=env) registry registry request b)
    (prepared : prepareRepresentedSlot (E:=env) registry registry request b=some plan)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (inputOffset inputSize : Word) (loaded : PhysicalHeapPort.port.load m inputOffset inputSize=some (input G))
    (p : Placement s.2.heap) (e : HeapByteEntry s.2.heap) (outputOffset capacity : Word)
    (inside : outputOffset.val+min capacity.val ReturningCall.output.length≤e.bytes.length)
    (header : (mload m (p.address e.id)).val=e.bytes.length)
    (reads : readBytes m (p.address e.id+32) e.bytes.length=e.bytes)
    (post : HeapOutputTransport.CopyResult env Γ→Prop)
    (holds : post (HeapOutputTransport.image (completed s r b plan o) s.2.heap (heap_eq s r b plan o) p e m outputOffset
      (callOutput ReturningCall.output capacity.val))) :
    ∀ result,run G depth bounded s sender target value gas classification code r padding b plan prepared o shared m inputOffset inputSize loaded p e outputOffset capacity=some (.ok (.success ReturningCall.output),result)→post result := by
  intro result step
  rw [run_exact G depth bounded s sender target value gas classification code r padding b plan prepared o shared m inputOffset inputSize loaded p e outputOffset capacity inside header reads] at step
  have same:=((Prod.mk.inj (Option.some.inj step)).2).symm
  rw [same]
  exact holds

end Solidity.Yul.World.DelegateSuccessOutput
