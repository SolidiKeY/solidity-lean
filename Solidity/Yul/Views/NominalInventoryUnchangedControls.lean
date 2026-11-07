import Solidity.Yul.Views.NominalInventoryPreparation
import Solidity.Yul.Views.NominalMemoryControls
import Solidity.Yul.Views.ComputedAllocation

/-! A two-object heap with real nominal aliases and an unrelated byte object.
The placement is computed from this actual heap; it is not an allocator policy
or a nominal computed-inventory completeness witness. -/
namespace Solidity.Yul.Views.NominalInventory.UnchangedControls
open Solidity.Yul.Views

def payload : Source.Data NominalMemory.Controls.env.layout (.bytes .memory) := .bytes [7,0,255]
def state := objectAllocatedState NominalMemory.Controls.state payload

def placement : Placement state.2.heap :=
  ComputedPlacement.build state.2.heap (by decide) (by decide)

def words : Fin 2 → Roadmap.Word := fun i => if i.val=0 then ⟨2^256-1,by decide⟩ else 32767

def nominal : MixedHeapEntry placement :=
  ⟨0,NominalMemory.Controls.arrayTy,NominalMemory.Controls.data,rfl,
    .words _ _ (.array 2 NominalMemory.Controls.lengthOK (by decide)
      NominalMemory.Controls.values words (fun i => .scalar _ _
        ((show ∀ j,(NominalMemory.Controls.values j).word=some (words j) from by decide) i)))⟩

def bytes : MixedHeapEntry placement := ⟨1,.bytes .memory,payload,rfl,.bytes [7,0,255] (by decide)⟩
def entries := [nominal,bytes]
def reverseEntries := [bytes,nominal]
def residual : ByteView := fun a => if a=0 then 238 else 165

theorem coverage : CoversMixedHeap entries := by
  intro a present
  have bound := ComputedPlacement.occupied_lt state.2.heap a present
  change a<2 at bound
  have choices : a=0 ∨ a=1 := by omega
  rcases choices with zero | one
  · subst a
    exact ⟨nominal,List.mem_cons_self,rfl⟩
  · subst a
    exact ⟨bytes,List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩

theorem supported : ∀ e ∈ entries,TypeSupported NominalMemory.Controls.env e.ty := by
  intro e member
  rcases List.mem_cons.mp member with same | later
  · subst e
    exact ⟨rfl,by trivial⟩
  · have same := List.mem_singleton.mp later
    subst e
    trivial

/-- Complete source identity, not just equality of alias-read projections. -/
theorem whole_state :
    writeback state placement placement .initial entries (encodeMixedHeap placement entries residual)=
      some (.ok (),state) :=
  writeback_encoded state placement placement .initial entries coverage (by decide) supported residual

/-- The encoded result retains the actual owner invariant. -/
theorem actual_MemOK : Source.MemOK NominalMemory.Controls.env state.2.heap.ty state :=
  (objectAllocRef_MemOK NominalMemory.Controls.heap.ty NominalMemory.Controls.state payload rfl
    trivial trivial (.bytes _) NominalMemory.Controls.actual_MemOK).1.self

/-- info: true -/
#guard_msgs in #eval decide (NominalMemory.Controls.aliasRead state .here 0=some ⟨2^256-1,by decide⟩ ∧
  NominalMemory.Controls.aliasRead state (.there .here) 0=some ⟨2^256-1,by decide⟩)
/-- info: [238, 165, 165] -/
#guard_msgs in #eval [0,227,300].map (fun a => ((encodeMixedHeap placement entries residual) a).toNat)
/-- info: [2, 3, 7, 0, 255] -/
#guard_msgs in #eval [state.2.heap.next,(mload (encodeMixedHeap placement entries residual) 192).val] ++
  (readBytes (encodeMixedHeap placement entries residual) 224 3).map UInt8.toNat

theorem reverse_coverage : CoversMixedHeap reverseEntries := by
  intro a present
  obtain ⟨e,member,same⟩ := coverage a present
  exact ⟨e,List.mem_reverse.mpr member,same⟩

theorem reverse_supported : ∀ e ∈ reverseEntries,TypeSupported NominalMemory.Controls.env e.ty :=
  fun e member => supported e (List.mem_reverse.mp member)

/-- The same physical snapshot and complete source result in the opposite order. -/
theorem reverse_whole_state :
    writeback state placement placement .initial reverseEntries (encodeMixedHeap placement entries residual)=
      some (.ok (),state) :=
  writeback_unchanged state placement placement .initial reverseEntries reverse_coverage reverse_supported _
    (fun e member => encodeMixedHeap_reads placement entries (by decide) residual e (List.mem_reverse.mp member))

def repeatedEntries := entries ++ [nominal]

theorem repeated_coverage : CoversMixedHeap repeatedEntries := by
  intro a present
  obtain ⟨e,member,same⟩ := coverage a present
  exact ⟨e,List.mem_append_left _ member,same⟩

theorem repeated_supported : ∀ e ∈ repeatedEntries,TypeSupported NominalMemory.Controls.env e.ty := by
  intro e member
  rcases List.mem_append.mp member with old | extra
  · exact supported e old
  · have same := List.mem_singleton.mp extra
    subst e
    exact ⟨rfl,by trivial⟩

/-- Repeated actual objects do not require a false distinct-root premise. -/
theorem repeated_whole_state :
    writeback state placement placement .initial repeatedEntries (encodeMixedHeap placement entries residual)=
      some (.ok (),state) := by
  apply writeback_unchanged state placement placement .initial repeatedEntries repeated_coverage repeated_supported
  intro e member
  rcases List.mem_append.mp member with old | extra
  · exact encodeMixedHeap_reads placement entries (by decide) residual e old
  · have same := List.mem_singleton.mp extra
    subst e
    exact encodeMixedHeap_reads placement entries (by decide) residual nominal List.mem_cons_self

theorem repeated_roots : ¬ (repeatedEntries.map MixedHeapEntry.id).Nodup := by decide

/-- info: false -/
#guard_msgs in #eval (snapshot placement NominalMemory.Controls.small (some 2)
  (mstore (encodeMixedHeap placement entries residual) 128 65535) 128).isSome

theorem heap_profile (a : Nat) (τ : Source.STy) (d : Source.Data NominalMemory.Controls.env.layout τ)
    (found : state.2.heap.get a=some ⟨τ,d⟩) : TypeSupported NominalMemory.Controls.env τ := by
  have present : (state.2.heap.get a).isSome := by rw [found]; rfl
  have bound := ComputedPlacement.occupied_lt state.2.heap a present
  change a<2 at bound
  have choices : a=0 ∨ a=1 := by omega
  rcases choices with zero | one
  · subst a
    change (some ⟨NominalMemory.Controls.arrayTy,NominalMemory.Controls.data⟩ :
      Option (Σ t,Source.Data NominalMemory.Controls.env.layout t))=some ⟨τ,d⟩ at found
    cases found
    exact ⟨rfl,by trivial⟩
  · subst a
    change (some ⟨.bytes .memory,payload⟩ :
      Option (Σ t,Source.Data NominalMemory.Controls.env.layout t))=some ⟨τ,d⟩ at found
    cases found
    trivial

/-- Complete inventory, uniqueness and source identity are derived rather than
supplied by the witness. This uses the existing actual heap enumerator. -/
theorem generated_whole_state :
    prepareHeapInventory placement=.ok (generatedHeapEntries placement) ∧
    writeback state placement placement .initial (generatedHeapEntries placement)
      (encodeMixedHeap placement (generatedHeapEntries placement) residual)=some (.ok (),state) :=
  generated_roundtrip state.2.heap.ty state placement placement .initial actual_MemOK heap_profile residual

/-- info: [0, 1] -/
#guard_msgs in #eval (generatedHeapEntries placement).map MixedHeapEntry.id

/-- Empty arrays still cannot invent a missing nominal declaration. -/
theorem missing_metadata : ¬ TypeSupported NominalMemory.Controls.env
    (.array .memory (.udvt NominalMemory.Controls.missing) (some 0)) := by
  intro supported
  have bad : (false : Bool)=true := supported.1
  cases bad

end Solidity.Yul.Views.NominalInventory.UnchangedControls
