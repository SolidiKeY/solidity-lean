import Solidity.Yul.Adapters.PhysicalSnapshotSlice
import Solidity.Yul.Compilation.PhysicalStore
import Solidity.Yul.Views.NominalInventoryUnchanged

/-! Consume the published physical-store compiler, retaining its exact selector
and actual byte-slice execution. A word is32generated MSTORE8 stores, not one
native MSTORE. Canonical writeback is a separate final boundary. Initial typed
view reads and genuine outside-image separation derive residual-only Source
identity; neither reserved-memory validity nor allocation/resource/compiler
adequacy follows merely from byte separation. -/
namespace Solidity.Yul.Adapters.SelectedPhysicalStore
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Yul.Compilation

/-- Reuse the existing instruction-class proof and materializer bodies. -/
theorem word_slice (F : Environment.Frame) (address : Nat) (value : Roadmap.Word)
    (initial : Environment.Slice) (fits : address+32≤2^256) :
    Environment.runSlice F (PhysicalStore.wordCode address value) initial=
      some {initial with memory:=mstore initial.memory address value} := by
  first
  | solve | rfl
  | rw [PhysicalStore.wordCode,Environment.runSlice_data F _ _
      (Environment.materialize_supported address (PhysicalStore.bytesOf value))]
    have actual := Environment.materialize_correct (PhysicalStore.bytesOf value) address initial
      (by simpa only [PhysicalStore.bytesOf,List.length_ofFn] using fits)
    simpa only [PhysicalStore.word_memory] using actual

/-- Keep the producer selector's full span bound, including the last valid word. -/
theorem select_facts (address : Nat) (value : Roadmap.Word) (code : Program)
    (selected : PhysicalStore.selectWord address value=some code) :
    address+32≤2^256 ∧ code=PhysicalStore.wordCode address value := by
  first
  | solve | simp only [PhysicalStore.selectWord] at selected ⊢
  | unfold PhysicalStore.selectWord at selected
    split at selected
    · rename_i fits
      exact ⟨fits,(Option.some.inj selected).symm⟩
    · cases selected

/-- Exact synchronization for any successfully selected compiled word store,
including unsupported canonical preparation of the actually reached bytes. -/
theorem word_apply {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (F : Environment.Frame) (address : Nat) (value : Roadmap.Word) (code : Program)
    (selected : PhysicalStore.selectWord address value=some code) (initial : Environment.Slice) :
    PhysicalSnapshotSlice.applySlice allocated s c F code initial=
      some ({initial with memory:=mstore initial.memory address value},
        snapshotStep allocated s c (mstore initial.memory address value)) := by
  first
  | solve | rfl
  | obtain ⟨fits,same⟩ := select_facts address value code selected
    subst code
    unfold PhysicalSnapshotSlice.applySlice
    rw [word_slice F address value initial fits]
    rfl

/-- Low-byte truncation is the actual compiler body and existing data slice. -/
theorem byte_slice (F : Environment.Frame) (address value : Roadmap.Word)
    (initial : Environment.Slice) :
    Environment.runSlice F (PhysicalStore.byteCode address value) initial=
      some {initial with memory:=mstore8 initial.memory address.val value} := by
  rw [Environment.runSlice_data F _ _ (by rfl)]
  exact PhysicalStore.byte_run address value initial

/-- No successful target byte output is discarded when preparation is None. -/
theorem byte_apply {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (F : Environment.Frame) (address value : Roadmap.Word) (initial : Environment.Slice) :
    PhysicalSnapshotSlice.applySlice allocated s c F (PhysicalStore.byteCode address value) initial=
      some ({initial with memory:=mstore8 initial.memory address.val value},
        snapshotStep allocated s c (mstore8 initial.memory address.val value)) := by
  simp only [PhysicalSnapshotSlice.applySlice,byte_slice,Option.map_some]

/-- A genuinely residual byte update changes the raw map while actual typed
writeback preserves the WHOLE Source state, including administrative defaults.
Coverage is needed for references; outside-image separation is not memory safety. -/
theorem byte_residual_identity {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (es : List (MixedHeapEntry p))
    (coverage : CoversMixedHeap es) (distinct : (es.map MixedHeapEntry.id).Nodup)
    (supported : ∀ e ∈ es,TypeSupported E e.ty) (residual : ByteView)
    (F : Environment.Frame) (address value : Roadmap.Word) (tail : List Environment.Word)
    (outside : ∀ e ∈ es,address.val<p.address e.id ∨ p.address e.id+e.image.span≤address.val) :
    ∃ next,PhysicalSnapshotSlice.applySlice allocated s ⟨p,history,es⟩ F
      (PhysicalStore.byteCode address value) ⟨tail,encodeMixedHeap p es residual⟩=
        some (⟨tail,mstore8 (encodeMixedHeap p es residual) address.val value⟩,some next) ∧ next.1=s := by
  first
  | solve | simp only [byte_apply]
  | let raw := mstore8 (encodeMixedHeap p es residual) address.val value
    have reads : ∀ e ∈ es,e.image.Reads raw (p.address e.id) := by
      intro e member
      apply e.image.reads_congr raw (encodeMixedHeap p es residual) (p.address e.id)
      · intro i inside
        exact find_saveByte_other _ (UInt8.ofNat value.val) (by have no := outside e member;omega)
      · exact encodeMixedHeap_reads p es distinct residual e member
    have unchanged := writeback_unchanged s allocated p history es coverage supported raw reads
    have actual := (snapshotStep_source allocated s ⟨p,history,es⟩ raw).trans unchanged
    obtain ⟨next,prepared,same⟩ := Option.map_eq_some_iff.mp actual
    refine ⟨next,?_,congrArg Prod.snd same⟩
    rw [byte_apply]
    change some (Environment.Slice.mk tail raw,snapshotStep allocated s (⟨p,history,es⟩ : SnapshotCursor allocated s) raw)=
      some (Environment.Slice.mk tail raw,some next)
    rw [prepared]

end Solidity.Yul.Adapters.SelectedPhysicalStore
