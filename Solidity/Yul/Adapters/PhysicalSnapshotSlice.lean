import Solidity.Yul.Views.InventorySnapshotHistory
import Solidity.Backend.Environment.Composition

/-! Boundary synchronization from the ACTUAL byte-addressed environment slice
into the typed Source heap. The existing evaluator supplies the reached bytes;
no target evaluator, Source state or instruction AST is duplicated. Outer None
is the partial slice result. Some (reached, none) retains its complete physical
output when canonical preparation is unsupported, without inventing a Source
or Yul refusal. This does not assert initial view, allocation/gas, intermediate
capture, program correspondence or whole-EVM adequacy. -/
namespace Solidity.Yul.Adapters.PhysicalSnapshotSlice
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend

/-- The two existing byte writers agree on the ENTIRE mathematical map.
This introduces no wrapping, capacity or allocator policy. -/
theorem writeBytes_mstore (m : ByteView) (offset : Nat) (value : Roadmap.Word) :
    Environment.writeBytes m offset (Semantics.wordBytes value.val)=mstore m offset value := by
  first
  | solve | rfl
  | solve | simp only [Environment.writeBytes,mstore]
  | funext b
    by_cases inside : offset≤b ∧ b<offset+32
    · have j : b-offset<32 := by omega
      have actual := Environment.writeBytes_at (Semantics.wordBytes value.val) offset (b-offset) m
        (by simpa only [Semantics.wordBytes,List.length_map,List.length_range] using j)
      rw [Nat.add_sub_of_le inside.1] at actual
      rw [actual]
      simp only [Semantics.wordBytes,List.getElem_map,List.getElem_range,mstore,dif_pos inside,wordByte]
      exact UInt8.ofNat_mod_size
    · rw [Environment.writeBytes_frame (Semantics.wordBytes value.val) offset b m (by
        simp only [Semantics.wordBytes,List.length_map,List.length_range]
        omega),mstore_outside m offset b value inside]

/-- Actual byte-addressed MSTORE preserves the stack tail and supplies exactly
that map to snapshot preparation; no target opcode is reimplemented. -/
theorem mstore_step (F : Environment.Frame) (m : ByteView)
    (offset value : Roadmap.Word) (tail : List Environment.Word) :
    Environment.sliceStep F (.op .MSTORE)
      ⟨lenU offset.val offset.isLt::lenU value.val value.isLt::tail,m⟩=
      some ⟨tail,mstore m offset.val value⟩ := by
  first
  | solve | rfl
  | change some (Environment.Slice.mk tail
      (Environment.writeBytes m offset.val (Semantics.wordBytes value.val)))=_
    rw [writeBytes_mstore]

/-- Run the existing physical program ONCE, then prepare its final memory.
Source execution occurs only inside successful existing snapshot preparation. -/
def applySlice {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (F : Environment.Frame) (code : Program) (initial : Environment.Slice) :
    Option (Environment.Slice × Option (Σ next : Source.EMState E Γ, SnapshotCursor allocated next)) :=
  (Environment.runSlice F code initial).map fun reached =>
    (reached,snapshotStep allocated s c reached.memory)

/-- Complete target stack and memory are retained in BOTH preparation outcomes. -/
theorem result_iff {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (F : Environment.Frame) (code : Program) (initial reached : Environment.Slice)
    (prepared : Option (Σ next : Source.EMState E Γ,SnapshotCursor allocated next)) :
    applySlice allocated s c F code initial=some (reached,prepared) ↔
      Environment.runSlice F code initial=some reached ∧
      snapshotStep allocated s c reached.memory=prepared := by
  first
  | solve | simp only [applySlice,Option.map_eq_some_iff,Prod.mk.injEq]
  | constructor
    · intro result
      obtain ⟨actual,run,same⟩ := Option.map_eq_some_iff.mp result
      have target : actual=reached := congrArg Prod.fst same
      subst actual
      exact ⟨run,congrArg Prod.snd same⟩
    · rintro ⟨run,prepared⟩
      unfold applySlice
      rw [run]
      simp only [Option.map_some,prepared]

/-- A failed partial target run is distinct from unsupported canonical decoding. -/
theorem target_none_iff {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (F : Environment.Frame) (code : Program) (initial : Environment.Slice) :
    applySlice allocated s c F code initial=none ↔ Environment.runSlice F code initial=none := by
  simp only [applySlice,Option.map_eq_none_iff]

/-- Actual target sequencing precedes this SINGLE final synchronization. A dirty
intermediate map need not decode when a later actual instruction repairs it. -/
theorem append {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (F : Environment.Frame) (a b : Program) (initial : Environment.Slice) :
    applySlice allocated s c F (a++b) initial=
      (Environment.runSlice F a initial).bind (fun mid => applySlice allocated s c F b mid) := by
  first
  | solve | simp only [applySlice,Environment.runSlice_append]
  | unfold applySlice
    rw [Environment.runSlice_append]
    cases Environment.runSlice F a initial <;> rfl

/-- Constructive source/physical closure for the actual reached bytes. All final
readback/reencoding facts follow the existing concrete codecs and real writes. -/
theorem success {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (F : Environment.Frame) (code : Program) (initial reached : Environment.Slice)
    (next : Σ t : Source.EMState E Γ,SnapshotCursor allocated t)
    (result : applySlice allocated s c F code initial=some (reached,some next)) :
    Environment.runSlice F code initial=some reached ∧
    writeback s allocated c.placement c.history c.entries reached.memory=some (.ok (),next.1) ∧
    encodeMixedHeap next.2.placement next.2.entries reached.memory=reached.memory ∧
    next.1=withSourceHeap s next.1.2.heap ∧
    (∀ H : Source.HeapTy,Source.MemOK E H s → Source.MemOK E H next.1) ∧
    (CoversMixedHeap c.entries → CoversMixedHeap next.2.entries) ∧
    next.2.entries.map MixedHeapEntry.id=c.entries.map MixedHeapEntry.id := by
  obtain ⟨target,prepared⟩ := (result_iff allocated s c F code initial reached _).mp result
  have actual := (snapshotStep_source allocated s c reached.memory).symm.trans
    (congrArg (Option.map (fun n => ((.ok () : Except Source.Halt Unit),n.1))) prepared)
  have stable := snapshotStep_preserves allocated s c reached.memory next prepared
  exact ⟨target,actual,snapshotStep_reencode allocated s c reached.memory next prepared,
    stable.1,fun H ok => snapshotStep_MemOK allocated s c reached.memory next prepared H ok,
    stable.2.2.2.2.2.2,stable.2.2.2.2.2.1⟩

end Solidity.Yul.Adapters.PhysicalSnapshotSlice
