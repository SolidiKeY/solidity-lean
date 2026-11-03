import Solidity.Yul.World.DelegateOutputChecks
namespace Solidity.Yul.World.DelegateOutputPort
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.DelegatePhysical
open Solidity.Yul.World.DelegatePort

theorem heap_eq {Γ} (s : EMState env Γ) (r : ResidualJournal complementCarrierOwnership)
    (o : ObservedEffects env.layout env.lay env.lay) : s.2.heap=(successful s r o).1.1.1.2.heap := rfl

/-- Actual selected body over arbitrary caller worlds/heaps/journal prefixes,
followed by output into a real typed owned object. No run/outcome premise. -/
def run (G : Glob env) (depth : Nat) (bounded : depth<1024) {Γ} (s : EMState env Γ)
    (sender target : Address) (value gas : Word)
    (classification : target.val≠0 ∧ (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=false)
    (code : (s.2.ex.world.accounts target).code=some 0)
    (r : ResidualJournal complementCarrierOwnership)
    (padding : r.cells (complementKey false account 7)=0xaabbcc00)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (inputOffset inputSize : Word) (loaded : PhysicalHeapPort.port.load m inputOffset inputSize=some (input G))
    (p : Placement s.2.heap) (e : HeapByteEntry s.2.heap) (outputOffset capacity : Word) :=
  HeapOutputTransport.sequence
    (call (CallerFrame.liftInvoke (invoke false G depth)) s r before o shared m
      (parent s sender value false) .delegatecall target gas 0 inputOffset inputSize)
    (.success ReturningCall.output,successful s r o)
    (call_success G depth bounded s sender target value gas classification code r padding o shared m inputOffset inputSize loaded)
    rfl s.2.heap (heap_eq s r o) p e m outputOffset capacity

/-- Full post-state, including all source fields/physical journals/observer;
window/ownership/view facts are actual explicit premises, not allocation laws. -/
theorem run_exact (G : Glob env) (depth : Nat) (bounded : depth<1024) {Γ} (s : EMState env Γ)
    (sender target : Address) (value gas : Word)
    (classification : target.val≠0 ∧ (Roadmap.Evm.Precompile.ofAddress? target.val).isSome=false)
    (code : (s.2.ex.world.accounts target).code=some 0)
    (r : ResidualJournal complementCarrierOwnership)
    (padding : r.cells (complementKey false account 7)=0xaabbcc00)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (m : ByteView) (inputOffset inputSize : Word) (loaded : PhysicalHeapPort.port.load m inputOffset inputSize=some (input G))
    (p : Placement s.2.heap) (e : HeapByteEntry s.2.heap) (outputOffset capacity : Word)
    (inside : outputOffset.val+min capacity.val (successful s r o).2.effects.returndata.length≤e.bytes.length)
    (header : (mload m (p.address e.id)).val=e.bytes.length)
    (reads : readBytes m (p.address e.id+32) e.bytes.length=e.bytes) :
    run G depth bounded s sender target value gas classification code r padding o shared m inputOffset inputSize loaded p e outputOffset capacity=
      some (.ok (.success ReturningCall.output),
        HeapOutputTransport.image (successful s r o) s.2.heap (heap_eq s r o) p e m outputOffset
          (callOutput (successful s r o).2.effects.returndata capacity.val)) := by
  rw [run,HeapOutputTransport.sequence_exact]
  exact congrArg (fun x=>some ((Except.ok (Outcome.success ReturningCall.output) : Except Halt Outcome),x))
    (HeapOutputTransport.exact_copy (successful s r o) rfl s.2.heap (heap_eq s r o) p e m outputOffset capacity inside header reads)
end Solidity.Yul.World.DelegateOutputPort
