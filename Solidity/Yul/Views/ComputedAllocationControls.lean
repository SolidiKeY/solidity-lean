import Solidity.Yul.Views.ComputedAllocation
import Solidity.Source.Semantics

/-! Actual logical allocations and stable computed geometric witnesses.
No target-chosen placement or whole allocator refinement is asserted. -/
namespace Solidity.Yul.Views.ComputedPlacement.Controls
private def E : Source.Env := ⟨[]⟩
private def empty : Source.EMState E [] := (.nil,Source.St.init E)
private def bytes : Source.Data E.layout (.bytes .memory) := .bytes [17]
private def text : Source.Data E.layout (.string .memory) := .string [255,0]
private def first := objectAllocatedState empty bytes
private def initial : Source.EMState E [.bytes .memory,.bytes .memory] :=
  (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) .nil),first.2)
private theorem initial_MemOK : Source.MemOK E initial.2.heap.ty initial := by
  have start : Source.MemOK E empty.2.heap.ty empty :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have one := (objectAllocRef_MemOK empty.2.heap.ty empty bytes rfl trivial trivial (.bytes _) start).1.self
  exact ⟨⟨one.1.1,⟨⟨.bytes .memory,rfl,rfl⟩,⟨⟨.bytes .memory,rfl,rfl⟩,trivial⟩⟩⟩,one.2⟩

theorem actual_allocation :
    ∃ (p : Placement initial.2.heap) (q : Placement (objectAllocatedState initial text).2.heap),
      prepare initial.2.heap=.ok p ∧ prepare (objectAllocatedState initial text).2.heap=.ok q ∧
      (Source.allocRef text).run initial=(.ok (.memRef rfl 1),objectAllocatedState initial text) ∧
      q.address 1=192 ∧ q.free.val=256 ∧ q.address 0=p.address 0 ∧ q.shape 0=p.shape 0 ∧
      Source.MemOK E initial.2.heap.ty (objectAllocatedState initial text) := by
  obtain ⟨p,q,old,next,run,base,free,others,mem⟩ := allocRef_geometry initial text (.bytes 2) rfl rfl
    (by decide) (by decide) (.string _) trivial
  have oldfree : p.free.val=192 := (prepare_choices initial.2.heap p old).2.2.1
  have newfree : q.free.val=256 := by rw [free,oldfree];rfl
  exact ⟨p,q,old,next,run,base.trans oldfree,newfree,(others 0 rfl).1,(others 0 rfl).2,mem _ initial_MemOK⟩

private def F : Source.Fr := {this:=1,sender:=2,value:=0,static:=false,contract:="Allocation",cd:=[]}

theorem retained_aliases (horizon : Nat) :
    let after:=objectAllocatedState initial text
    (Source.bytesOfRV (E:=E) F horizon (.val (after.1.get .here))).run after=(.ok [17],after) ∧
    (Source.bytesOfRV (E:=E) F horizon (.val (after.1.get (.there .here)))).run after=(.ok [17],after) ∧
    (Source.heapBytes (E:=E) (Γ:=[.bytes .memory,.bytes .memory]) 1).run after=(.ok [255,0],after) := ⟨rfl,rfl,rfl⟩

private def zero : Source.Data E.layout (.array .memory .bool (some 0)) :=
  .array 0 (fun _ h=>(Option.some.inj h).symm) Fin.elim0
private def zeroState := objectAllocatedState initial zero
private def thirdState := objectAllocatedState zeroState text
private def zeroPlacement : Placement zeroState.2.heap := build _ rfl (by decide)
private def thirdPlacement : Placement thirdState.2.heap := build _ rfl (by decide)

theorem zero_actual_run : (Source.allocRef zero).run initial=(.ok (.memRef rfl 1),zeroState) :=
  objectAllocRef_run initial zero rfl

theorem zero_then_next : zeroPlacement.address 1=192 ∧ zeroPlacement.free.val=193 ∧
    thirdPlacement.address 2=193 ∧ thirdPlacement.address 0=128 ∧ thirdPlacement.address 1=192 := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem unsupported_recorded : unsupported (initial.2.heap.alloc ⟨.bool,.val (.bool true)⟩).1=[1] := by
  rw [alloc_unsupported]
  rfl

/-- info: (192, 193, 193, 128) -/
#guard_msgs in #eval
  (zeroPlacement.address 1,zeroPlacement.free.val,thirdPlacement.address 2,thirdPlacement.address 0)
/-- info: (false, false) -/
#guard_msgs in #eval
  (thirdPlacement.address 2==192,thirdPlacement.address 0==193)
end Solidity.Yul.Views.ComputedPlacement.Controls
