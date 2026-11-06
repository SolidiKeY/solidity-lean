import Solidity.Yul.Views.ComputedPlacement
import Solidity.Source.Semantics

/-! Computed placement witnesses and exact preparation failures. These heaps
are intrinsically typed test states, not claims about reachable allocator runs. -/
namespace Solidity.Yul.Views.ComputedPlacement.Controls
private def E : Source.Env := ⟨[]⟩
private def zeroArray : Source.Data E.layout (.array .memory .bool (some 0)) :=
  .array 0 (fun _ h=>(Option.some.inj h).symm) Fin.elim0

def sparse : Source.Heap E.layout where
  cells a := if a=2 then some ⟨.bytes .memory,.bytes [1,2,3]⟩ else
    if a=4 then some ⟨_,zeroArray⟩ else if a=7 then some ⟨.string .memory,.string [255,0]⟩ else none
  next := 9
  bounded a large := by
    simp only [if_neg (show a≠2 by omega),if_neg (show a≠4 by omega),if_neg (show a≠7 by omega)]

def placement : Placement sparse := build sparse rfl (by decide)

theorem sparse_prepared : prepare sparse=.ok placement := prepare_success sparse rfl (by decide)

theorem sparse_coordinates : placement.address 2=128 ∧ placement.address 4=192 ∧
    placement.address 7=193 ∧ placement.free.val=257 := ⟨rfl,rfl,rfl,rfl⟩

/-- The actual zero-size shape remains zero; only address reservation is1. -/
theorem zero_footprint : (placement.shape 4).size=0 ∧ placement.address 4≠placement.address 7 := by decide

private def scalar : Source.Heap E.layout :=
  (Source.Heap.empty.alloc ⟨.bool,.val (.bool true)⟩).1

theorem scalar_error : prepare scalar=.error (.unsupported [0]) := rfl

private def huge : Source.Heap E.layout :=
  (Source.Heap.empty.alloc ⟨.array .memory .bool none,
    .array (2^256) (fun _ h=>nomatch h) (fun _=>.val (.bool false))⟩).1

theorem huge_error : prepare huge=.error (.overflow (128+32+(2^256)*32)) := rfl

private def empty : Source.Heap E.layout := Source.Heap.empty

theorem empty_prepared : prepare empty=.ok (build empty rfl (by decide)) := rfl

/-- info: ([128, 192, 193], 257, []) -/
#guard_msgs in #eval
  ([placement.address 2,placement.address 4,placement.address 7],placement.free.val,unsupported sparse)
/-- info: false -/
#guard_msgs in #eval placement.address 7==192
end Solidity.Yul.Views.ComputedPlacement.Controls
