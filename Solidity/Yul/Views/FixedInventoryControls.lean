import Solidity.Yul.Views.FixedInventoryUnchanged
import Solidity.Yul.Views.FixedMemoryControls
import Solidity.Yul.Views.ComputedAllocation

/-! Whole-inventory controls combine an actual fixed array and a byte object.
Coverage/placement use the actual finite heap. Scalar signs, aliases and residual
bytes remain distinct from allocator or universal inventory completeness. -/
namespace Solidity.Yul.Views.FixedInventory.Controls
open Solidity.Yul.Views

def payload : Source.Data FixedMemory.Controls.env.layout (.bytes .memory) := .bytes [7,0,255]
def state := objectAllocatedState FixedMemory.Controls.state payload

def placement : Placement state.2.heap :=
  ComputedPlacement.build state.2.heap (by decide) (by decide)

def words : Fin 2 → Roadmap.Word := fun i => if i.val=0 then Source.intWord (-125) else 32767

def nominal : MixedHeapEntry placement :=
  ⟨0,FixedMemory.Controls.ty,FixedMemory.Controls.data,rfl,
    .words _ _ (.array 2 FixedMemory.Controls.lengthOK (by decide)
      FixedMemory.Controls.values words (fun i => .scalar _ _
        (by by_cases zero : i.val=0 <;> simp only [FixedMemory.Controls.values,words,zero,if_true,if_false,Source.Val.word] <;> rfl)))⟩

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

theorem supported : ∀ e ∈ entries,TypeSupported FixedMemory.Controls.env e.ty := by
  intro e member
  rcases List.mem_cons.mp member with same | later
  · subst e
    trivial
  · have same := List.mem_singleton.mp later
    subst e
    trivial

/-- Complete source identity, not just equality of alias-read projections. -/
theorem whole_state :
    writeback state placement placement .initial entries (encodeMixedHeap placement entries residual)=
      some (.ok (),state) :=
  writeback_encoded state placement placement .initial entries coverage (by decide) supported residual

theorem reverse_coverage : CoversMixedHeap reverseEntries := by
  intro a present
  obtain ⟨e,member,same⟩ := coverage a present
  exact ⟨e,List.mem_reverse.mpr member,same⟩

theorem reverse_supported : ∀ e ∈ reverseEntries,TypeSupported FixedMemory.Controls.env e.ty :=
  fun e member => supported e (List.mem_reverse.mp member)

/-- The same physical snapshot and complete source result in the opposite order. -/
theorem reverse_whole_state :
    writeback state placement placement .initial reverseEntries (encodeMixedHeap placement entries residual)=
      some (.ok (),state) :=
  writeback_unchanged state placement placement .initial reverseEntries reverse_coverage reverse_supported _
    (fun e member => encodeMixedHeap_reads placement entries (by decide) residual e (List.mem_reverse.mp member))


theorem residual_byte : (encodeMixedHeap placement entries residual) 300=165 := by decide

theorem fixed_source_cells : state.2.heap.get 0=some ⟨FixedMemory.Controls.ty,FixedMemory.Controls.data⟩ ∧
    state.2.heap.get 1=some ⟨.bytes .memory,payload⟩ := ⟨rfl,rfl⟩

theorem old_nominal_decoder_rejects :
    (NominalInventory.writeback state placement placement .initial entries
      (encodeMixedHeap placement entries residual)).isNone=true := by decide
end Solidity.Yul.Views.FixedInventory.Controls
