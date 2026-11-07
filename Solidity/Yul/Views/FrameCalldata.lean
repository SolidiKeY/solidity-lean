import Solidity.Yul.Views.ResidualMemoryWriteback
import Solidity.Yul.Views.Inputs

namespace Solidity.Yul.Views

/-- Bind raw calldata to the ACTUAL existing source call frame. Source offsets
are words, but source+i is mathematical Nat: missing bytes zero-pad rather
than wrap. There is deliberately no MCOPY-style source-end range premise. -/
def frameCalldataCopy {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (frame : Source.CallFrame) (plan : ResidualWindowPlan p) (residual : ByteView) (source : Roadmap.Word) : ByteView :=
  calldatacopy residual frame.input plan.destination.val source.val plan.size.val

theorem frameCalldata_whole_map {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (frame : Source.CallFrame) (plan : ResidualWindowPlan p) (residual : ByteView) (source : Roadmap.Word) :
    calldatacopy (encodeMixedHeap p plan.entries residual) frame.input plan.destination.val source.val plan.size.val=
      encodeMixedHeap p plan.entries (frameCalldataCopy frame plan residual source) :=
  plan.whole_map residual (calldataBytes frame.input) source.val

/-- Real canonical source writeback, with existing preparation/error results. -/
def frameCalldataWriteback {E Γ origin} (frame : Source.CallFrame)
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (plan : ResidualWindowPlan p)
    (residual : ByteView) (source : Roadmap.Word) :=
  residualMemoryWriteback s allocated p history plan residual (calldataBytes frame.input) source.val

theorem frameCalldataWriteback_exact {E Γ origin} (frame : Source.CallFrame)
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (plan : ResidualWindowPlan p) (residual : ByteView) (source : Roadmap.Word)
    (supported : ∀ a ty d, s.2.heap.get a=some ⟨ty,d⟩ → InventoryTypeSupported E ty) :
    frameCalldataWriteback frame s allocated p history plan residual source=
      .ok (some ((.ok (),s),frameCalldataCopy frame plan residual source)) :=
  residualMemoryWriteback_exact s allocated p history plan residual (calldataBytes frame.input) source.val supported

theorem frameCalldataWriteback_every_H {E Γ origin} (frame : Source.CallFrame)
    (H : Source.HeapTy) (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (plan : ResidualWindowPlan p) (residual : ByteView) (source : Roadmap.Word)
    (supported : ∀ a ty d, s.2.heap.get a=some ⟨ty,d⟩ → InventoryTypeSupported E ty) (ok : Source.MemOK E H s) :
    ∃ after, frameCalldataWriteback frame s allocated p history plan residual source=.ok (some after) ∧
      Source.MemOK E H after.1.2 :=
  ⟨((.ok (),s),frameCalldataCopy frame plan residual source),
    frameCalldataWriteback_exact frame s allocated p history plan residual source supported,ok⟩

theorem frameCalldata_reserved {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (frame : Source.CallFrame) (plan : ResidualWindowPlan p) (residual : ByteView) (source : Roadmap.Word)
    (reserved : ReservedOK residual p.free) : ReservedOK (frameCalldataCopy frame plan residual source) p.free :=
  plan.reserved residual (calldataBytes frame.input) source.val reserved

theorem frameCalldata_copy_byte {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (frame : Source.CallFrame) (plan : ResidualWindowPlan p) (residual : ByteView) (source : Roadmap.Word)
    (i : Nat) (inside : i<plan.size.val) :
    frameCalldataCopy frame plan residual source (plan.destination.val+i)=frame.input[source.val+i]?.getD 0 :=
  calldatacopy_payload residual frame.input plan.destination.val source.val plan.size.val i inside

theorem frameCalldata_padded_byte {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (frame : Source.CallFrame) (plan : ResidualWindowPlan p) (residual : ByteView) (source : Roadmap.Word)
    (i : Nat) (inside : i<plan.size.val) (past : frame.input.length≤source.val+i) :
    frameCalldataCopy frame plan residual source (plan.destination.val+i)=0 :=
  calldatacopy_padded_byte residual frame.input plan.destination.val source.val plan.size.val i inside past

theorem frameCalldata_readBytes {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (frame : Source.CallFrame) (plan : ResidualWindowPlan p) (physical : ByteView) (source : Roadmap.Word) :
    readBytes (calldatacopy physical frame.input plan.destination.val source.val plan.size.val) plan.destination.val plan.size.val=
      readBytes (calldataBytes frame.input) source.val plan.size.val :=
  calldatacopy_readBytes physical frame.input plan.destination.val source.val plan.size.val

/-- Approved SAME Fixed hash over exactly the copied bytes, including all zero
padding. No collision premise, original-input/selector-strip substitution,
allocation policy or compiler correspondence assumption. -/
theorem frameCalldata_hash {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (frame : Source.CallFrame) (fixed : Roadmap.Evm.Fixed) (plan : ResidualWindowPlan p) (residual : ByteView) (source : Roadmap.Word) :
    keccak256 fixed (encodeMixedHeap p plan.entries (frameCalldataCopy frame plan residual source))
      plan.destination.val plan.size.val=
        ⟨fixed.keccak (readBytes (calldataBytes frame.input) source.val plan.size.val),fixed.keccak_lt _⟩ := by
  rw [←frameCalldata_whole_map]
  apply Fin.ext
  exact congrArg fixed.keccak (frameCalldata_readBytes frame plan (encodeMixedHeap p plan.entries residual) source)

theorem frameCalldata_zero_copy {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (frame : Source.CallFrame) (plan : ResidualWindowPlan p) (residual : ByteView) (source : Roadmap.Word)
    (empty : plan.size.val=0) : frameCalldataCopy frame plan residual source=residual := by
  unfold frameCalldataCopy
  rw [empty]
  exact calldatacopy_zero residual frame.input plan.destination.val source.val

end Solidity.Yul.Views
