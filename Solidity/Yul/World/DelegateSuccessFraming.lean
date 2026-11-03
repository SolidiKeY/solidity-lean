import Solidity.Yul.World.DelegateSuccessWitness

/-! Complete framing of the selected actual success and owned caller copy.
These preparation/consumer laws are not universal allocation or Yul/G51 rules. -/
namespace Solidity.Yul.World.DelegateSuccessFraming
open Solidity.Source
open Solidity.Roadmap (Word Bytes Outcome Address)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.StateCallPhysical (registry)
open Solidity.Yul.World.DelegatePhysical
open Solidity.Yul.World.DelegateSuccessBoundary (completed)
open Solidity.Yul.World.DelegateSuccessPort (heap_eq)

theorem image_empty {Γ} (s : EMState env Γ) (r : ResidualJournal complementCarrierOwnership)
    (b : BoolEncodingJournal) (plan : RepresentedSlotPlan (E:=env) registry registry request b)
    (o : ObservedEffects env.layout env.lay env.lay) (p : Placement s.2.heap)
    (e : HeapByteEntry s.2.heap) (m : ByteView) (offset : Word) :
    HeapOutputTransport.image (completed s r b plan o) s.2.heap (heap_eq s r b plan o) p e m offset []=
      (completed s r b plan o,some ((m,changed s account),
        ((completed s r b plan o).1.1.2,(completed s r b plan o).1.2),(completed s r b plan o).2)) := by
  simp only [HeapOutputTransport.image,completed,DelegateSuccessBoundary.updated,changed,Solidity.Backend.Environment.writeBytes,
    HeapWindow.splice_empty,heap_write_unchanged _ _ _ _ e.found,
    withSourceHeap_unchanged]

/-- Every logical heap cell other than the selected output is preserved. -/
theorem other {Γ} (s : EMState env Γ) (e : HeapByteEntry s.2.heap) (offset : Word) (bytes : Bytes)
    (a : Nat) (different : a≠e.id) :
    (DelegateRevertHeap.copied (changed s account) e offset bytes).2.heap.get a=s.2.heap.get a :=
  DelegateRevertHeap.other (changed s account) e offset bytes a different

/-- Caller locals/function locals and every nonheap field retain the actual
successful Source mutation, while only the selected output object is written. -/
theorem fields {Γ} (s : EMState env Γ) (e : HeapByteEntry s.2.heap) (offset : Word) (bytes : Bytes) :
    let copied:=DelegateRevertHeap.copied (changed s account) e offset bytes
    copied.1=s.1 ∧ copied.2.ex=(changed s account).2.ex ∧ copied.2.events=s.2.events ∧
      copied.2.fnLocals=s.2.fnLocals ∧ copied.2.logs=s.2.logs ∧ copied.2.heap.next=s.2.heap.next := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem raw_outside (m : ByteView) (start : Nat) (bytes : Bytes) (i : Nat)
    (outside : i<start ∨ start+bytes.length≤i) :
    Solidity.Backend.Environment.writeBytes m start bytes i=m i :=
  Solidity.Backend.Environment.writeBytes_frame bytes start i m outside

/-- An enclosing frame reverts all three successful child journals; caller
memory copies remain governed by the actual caller heap policy, not this law. -/
theorem witness_outer (G : Glob env) (data : Bytes) :
    finish (DelegateRevertWitness.source G) DelegateRevertControls.encoding DelegateRevertControls.observer
      (companionEnter ⟨(DelegateRevertWitness.source G).2.ex,DelegateRevertControls.residue⟩ account DelegateChecks.sender DelegateChecks.value [] false)
      (DelegateSuccessWitness.result G).1 [] (.revert data)=
      DelegatePort.reverted (DelegateRevertWitness.source G) DelegateRevertControls.residue
        DelegateRevertControls.encoding DelegateRevertControls.observer data :=
  DelegateSuccessBoundary.enclosing_revert (DelegateRevertWitness.source G) DelegateChecks.sender DelegateChecks.value
    DelegateRevertControls.residue DelegateRevertControls.encoding DelegateRevertControls.plan DelegateRevertControls.observer data
end Solidity.Yul.World.DelegateSuccessFraming
