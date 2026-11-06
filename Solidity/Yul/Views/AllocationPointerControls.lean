import Solidity.Yul.Views.AllocationPointer
import Solidity.Yul.Views.AllocationSequenceControls
import Solidity.Yul.Views.NewMemoryControls

/-! A new expression returns logical ID 3 at physical word 288, then updates
an actual pointer array. Aliases read the new child; bounds failure preserves
the allocation and remains a real Source panic, unlike preparation None. -/
namespace Solidity.Yul.Views.AllocationPointer.Controls
abbrev E := AllocationRefresh.Controls.E
abbrev F := NewMemory.Controls.F

def initial : Source.EMState E [.int Source.IntTy.u256] :=
  (.cons (.int 3 (by decide)) .nil,AllocationSequence.Controls.final.2)
def data : Source.Data E.layout (.bytes .memory) := .bytes [0,0,0]
def p : Placement initial.2.heap := ComputedPlacement.build _ rfl (by decide)
def input := encodeMixedHeap p (generatedHeapEntries p) (mstore (fun i=>if i=383 then 99 else 0) 64 p.free)
def raw := (ComputedAllocationWrite.prepare initial.2.heap p rfl data (.bytes 3) rfl (by decide) input).getD input
def after := objectAllocatedState initial data
def q : Placement after.2.heap := ComputedAllocationWrite.placement initial.2.heap p rfl data (.bytes 3) rfl (by decide)

theorem prepared : ComputedAllocationWrite.prepare initial.2.heap p rfl data (.bytes 3) rfl (by decide) input=some raw := rfl

theorem pointer_decoded : decodeMemoryPointer q (generatedHeapEntries q) (.bytes .memory) rfl 288=
    some (Source.Val.memRef rfl 3) :=
  decode initial p rfl data (.bytes 3) rfl (by decide) _ rfl input raw prepared

theorem actual_bridge (G : Source.Glob E) (n index : Nat) :
    pointerStateWriteback after q (generatedHeapEntries q) F 0 2 index (.bytes .memory) rfl 288=
      some ((writeNew G F (n+1) 0 (τ:=.bytes .memory) rfl (.local .here) rfl 2 index).run initial) :=
  write_new G F (n+1) 0 initial initial rfl (.local .here) rfl
    (.val (Source.Val.int 3 (by decide))) rfl 3 rfl (by decide) data rfl (.bytes 3) rfl p rfl
    (by decide) _ rfl input raw prepared 2 index

def written := ((Source.writeLoc F 0 (.mem 2 0) (Source.Val.memRef (τ:=.bytes .memory) rfl 3)).run after).2

theorem actual_success (G : Source.Glob E) (n : Nat) :
    (writeNew G F (n+1) 0 (τ:=.bytes .memory) rfl (.local .here) rfl 2 0).run initial=(.ok (),written) := rfl

theorem aliases :
    (Source.readLoc (E:=E) F (.mem (τ:=.bytes .memory) 2 0)).run written=(.ok (.memRef rfl 3),written) ∧
    (Source.bytesOfRV F 0 (.val (Source.Val.memRef (τ:=.bytes .memory) rfl 3))).run written=(.ok [0,0,0],written) ∧
    written.2.heap.next=4 := ⟨rfl,rfl,rfl⟩

theorem out_of_bounds (G : Source.Glob E) (n : Nat) :
    (writeNew G F (n+1) 0 (τ:=.bytes .memory) rfl (.local .here) rfl 2 1).run initial=
      (.error (.revert (Source.panicData .index)),after) := rfl

theorem interior_none : decodeMemoryPointer q (generatedHeapEntries q) (.bytes .memory) rfl 289=none := rfl

theorem wrong_type_none : decodeMemoryPointer q (generatedHeapEntries q) (.array .memory .bool none) rfl 288=none := rfl
theorem initial_safe : Source.MemOK E initial.2.heap.ty initial := by
  let start := AllocationRefresh.Controls.initial
  have empty : Source.MemOK E start.2.heap.ty start :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have one := (objectAllocRef_MemOK start.2.heap.ty start AllocationRefresh.Controls.first rfl trivial trivial (.bytes _) empty).1
  have two := (objectAllocRef_MemOK start.2.heap.ty AllocationRefresh.Controls.one AllocationRefresh.Controls.second
    rfl trivial trivial (.string _) one).1
  have three := (objectAllocRef_MemOK start.2.heap.ty AllocationSequence.Controls.two AllocationSequence.Controls.third rfl trivial
    (fun _ => ⟨_,rfl⟩) (.array (fun _ => .val ⟨.bytes .memory,rfl,rfl⟩)) two).1.self
  exact ⟨⟨three.1.1,⟨trivial,trivial⟩⟩,three.2⟩

theorem actual_safe (G : Source.Glob E) (n index : Nat) :
    Source.MemOK E initial.2.heap.ty
      ((writeNew G F (n+1) 0 (τ:=.bytes .memory) rfl (.local .here) rfl 2 index).run initial).2 :=
  MemOK G F (n+1) 0 initial initial rfl (.local .here) rfl
    (.val (Source.Val.int 3 (by decide))) rfl 3 rfl (by decide) data rfl rfl trivial trivial (.bytes _)
    _ initial_safe 2 index
end Solidity.Yul.Views.AllocationPointer.Controls
