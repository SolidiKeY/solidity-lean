import Solidity.Yul.Views.MixedNominalRetainedAllocation
import Solidity.Yul.Views.MixedNominalRealizationControls

/-! A genuine earlier mixed struct write is retained across new allocation.
The allocation extends the original origin, not the reached snapshot, and keeps
both old aliases and reserved words while constructing the new raw view. -/
namespace Solidity.Yul.Views.MixedNominalInventory.RetainedAllocationControls
open Solidity.Yul.Views
open Solidity.Yul.Views.FixedNominalMember.StructControls

def current := expected
def p := retainedWritePlacement placement placement .initial 0 (Source.Data.struct newFields)
  (by rfl) (.strct 3) (.strct _) (by decide)
def history : RetainedAllocation placement p := retainWritten placement placement .initial 0
  (Source.Data.struct newFields) (by rfl) (.strct 3) (.strct _) (by decide)
def fresh : ∀ a,(heap.cells a).isSome → placement.address a≠256 := heap_later_fresh heap placement 256 (by decide)
def originNext := heapAllocPlacement heap placement (Source.Data.struct (l:=.memory) oldFields) (.strct 3) (.strct _)
  256 352 (by decide) fresh (by decide)
def q := retainedAllocationPlacement placement p history (Source.Data.struct (l:=.memory) oldFields) (.strct 3) (.strct _)
  256 352 (by decide) fresh (by decide)
def lineage : RetainedAllocation originNext q := retainAllocated placement p history
  (Source.Data.struct (l:=.memory) oldFields) (.strct 3) (.strct _) 256 352 (by decide) fresh (by decide)
def after := objectAllocatedState current (Source.Data.struct (l:=.memory) oldFields)
def buffer := encodeMixedHeap p (generatedHeapEntries p) (mstore (fun _=>0) 64 p.free)

theorem current_MemOK : Source.MemOK env heap.ty current :=
  writeback_MemOK heap.ty state placement placement .initial [entry] (changed (fun _=>165)) _
    (Controls.changed_source _) GeneratedControls.actual_MemOK

theorem current_profile : ∀ a τ d,current.2.heap.get a=some ⟨τ,d⟩ → TypeSupported env τ := by
  apply profile_of_types heap current.2.heap
  · exact funext (fun a=>Source.Heap.write_ty heap 0 a (Source.Data.struct newFields) (by rfl))
  · exact GeneratedControls.heap_profile

theorem reserved : ReservedOK buffer p.free := by
  apply encodeMixedHeap_reserved
  constructor
  · exact congrArg Fin.val (mload_mstore (fun _=>0) 64 p.free)
  · intro i
    rw [mstore_outside _ _ _ _ (by have bound:=i.isLt;omega)]

theorem allocation_retains_prior_write : ∃ raw,
    (Source.allocRef (Source.Data.struct (l:=.memory) oldFields)).run current=(.ok (.memRef rfl 1),after) ∧
    encodeMixedHeap q (generatedHeapEntries q) raw=raw ∧
    writeback after originNext q lineage (generatedHeapEntries q) raw=some (.ok (),after) ∧ ReservedOK raw 352 := by
  have ready := owner_prepares heap.ty current p current_MemOK current_profile
  have facts := prepareHeapInventory_ok p _ ready
  have inner : Source.Data.Inner (E:=env) (Source.Data.struct (l:=.memory) oldFields) :=
    ⟨⟨_,rfl⟩,⟨⟨_,rfl⟩,⟨⟨_,rfl⟩,trivial⟩⟩⟩
  have valid : Source.DataOK env current.2.heap.ty (Source.Data.struct (l:=.memory) oldFields) :=
    .struct (.cons (.val trivial) (.cons (.val trivial) (.cons (.val trivial) .nil)))
  obtain ⟨raw,_,run,_,_,_,_,whole,replay,saved⟩ := retained_allocation_physical heap.ty current placement p history
    (Source.Data.struct (l:=.memory) oldFields) rfl (.strct 3) (.strct _) inner valid profile
    256 352 (by decide) fresh (by decide) buffer current_MemOK current_profile
    (encodeMixedHeap_reads p (generatedHeapEntries p) facts.2.2 _) reserved
  exact ⟨raw,run,whole,replay,saved⟩

theorem prior_origin_is_preserved : originNext.shape 0=placement.shape 0 ∧
    q.address 0=p.address 0 ∧ q.address 1=256 ∧ after.1=state.1 := by
  first | solve | rfl
        | exact ⟨rfl,rfl,rfl,rfl⟩

theorem no_snapshot_reset : current≠state := RealizationControls.stale_state_rejected

end Solidity.Yul.Views.MixedNominalInventory.RetainedAllocationControls
