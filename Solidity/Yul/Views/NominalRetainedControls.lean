import Solidity.Yul.Views.NominalRetained
import Solidity.Yul.Views.NominalMemoryControls

/-! Actual retained nominal arrays: shrink to zero and recover the same nonzero
canonical tail from the original allocation. Synthetic byte seeds are separate
from compiler/EVM observations; preparation None has no language verdict. -/
namespace Solidity.Yul.Views.NominalMemory.RetainedControls
open Solidity.Yul.Views
abbrev env := Controls.env
abbrev small := Controls.small
abbrev values := Controls.values

def arrayTy : Source.STy := .array .memory (.udvt small) none
def data : Source.Data env.layout arrayTy := dynamicMemberData env.layout (.udvt small) 2 values
def heap : Source.Heap env.layout := (Source.Heap.empty.alloc ⟨arrayTy,data⟩).1
def placement : Placement heap where
  address a := 128+a*128
  shape _ := .array true 2
  free := 256
  free_start := by decide
  distinct a b _ _ same := by omega
  typed a ty d found := by
    by_cases zero : a=0
    · subst a
      change (some ⟨arrayTy,data⟩ : Option (Σ t,Source.Data env.layout t))=some ⟨ty,d⟩ at found
      cases found
      exact .array 2 (fun z (h : (none : Option Nat)=some z) => nomatch h) _
    · have high : heap.next≤a := by change 1≤a;omega
      have absent := heap.bounded a high
      change heap.cells a=some ⟨ty,d⟩ at found
      rw [absent] at found
      cases found
  starts a _ := by omega
  ends a present := by
    have low : a<heap.next := Nat.lt_of_not_le (fun high => by rw [heap.bounded a high] at present;cases present)
    change a<1 at low
    have zero : a=0 := by omega
    subst a
    decide
  separate a b _ _ distinct := by
    change 128+a*128+96≤128+b*128 ∨ 128+b*128+96≤128+a*128
    omega


def state : Source.EMState env [arrayTy,arrayTy] :=
  ⟨.cons (.memRef rfl 0) (.cons (.memRef rfl 0) .nil),
    ⟨⟨⟨fun _ => Source.Account.empty _⟩,.empty,[]⟩,heap,[],[],⟨[],.nil⟩, Source.FailureExecution.Cursor.empty⟩⟩
def raw : ByteView := mstore (mstore (mstore (mstore (mstore (fun _=>165) 64 256) 96 0) 128 2) 160 ⟨2^256-1,by decide⟩) 192 32767
def shrunkRaw : ByteView := mstore raw 128 0
def regrownRaw : ByteView := mstore shrunkRaw 128 2

def emptyData : Source.Data env.layout arrayTy := dynamicMemberData env.layout (.udvt small) 0 Fin.elim0
def shrunkHeap : Source.Heap env.layout := heap.write 0 emptyData (heap_ty_of_get heap 0 _ data rfl)
def shrunkState : Source.EMState env [arrayTy,arrayTy] := withSourceHeap state shrunkHeap
noncomputable def shrunkPlacement : Placement shrunkHeap :=
  retainedMemberArrayPlacement placement placement (retainInitial heap placement) 0 (.udvt small) 2 values rfl 0 Fin.elim0 (by decide)
theorem shrunkHistory : RetainedAllocation placement shrunkPlacement :=
  retainedMemberArray_history placement placement (retainInitial heap placement) 0 (.udvt small) 2 values rfl 0 Fin.elim0 (by decide)
def regrownHeap : Source.Heap env.layout := shrunkHeap.write 0 data (heap_ty_of_get shrunkHeap 0 _ emptyData (Source.Heap.write_get _ _ _ _))
def regrownState : Source.EMState env [arrayTy,arrayTy] := withSourceHeap shrunkState regrownHeap

/-- Actual source shrink; current logical length becomes zero. -/
theorem shrink_source : retainedState state placement placement (retainInitial heap placement)
    0 small shrunkRaw=some (.ok (),shrunkState) := by
  rfl

/-- Regrowth uses original ownership, not the smaller current shape. -/
theorem regrow_source : retainedState shrunkState placement shrunkPlacement shrunkHistory
    0 small regrownRaw=some (.ok (),regrownState) := by
  unfold retainedState
  simp only [show declaredUDVT env small=true from rfl,↓reduceIte]
  rw [show mload regrownRaw (shrunkPlacement.address 0)=2 from rfl]
  simp only [show (2 : Solidity.Roadmap.Word).val=2 from rfl]
  rw [if_pos (by decide)]
  change Option.map (fun (values : Fin 2 → Solidity.Source.Val env.layout (.udvt small)) => (Solidity.Source.heapPut 0 ⟨_,dynamicMemberData env.layout (.udvt small) 2 values⟩).run shrunkState) (decodeArray env.layout small 2 regrownRaw (shrunkPlacement.address 0+32))=some (.ok (),regrownState)
  have decoded : decodeArray env.layout small 2 regrownRaw (shrunkPlacement.address 0+32)=some values := array_decode_encode env.layout small (by trivial) 2 regrownRaw _ values (by decide)
  rw [decoded]
  simp only [Option.map_some]
  exact congrArg some (memberArrayHeapPut_run shrunkState 0 (.udvt small) none 2 (fun _ h => nomatch h) values (by rfl))

def aliasRead (s : Source.EMState env [arrayTy,arrayTy]) (alias : Source.Idx [arrayTy,arrayTy] arrayTy)
    (index : Nat) : Option Roadmap.Word :=
  match ((do
    let loc ← Source.indexLoc Controls.readFrame (s.1.get alias) index
    Source.readLoc Controls.readFrame loc) : Source.EM env [arrayTy,arrayTy] (Source.Val env.layout (.udvt small))).run s with
  | (.ok v,_) => v.word
  | _ => none

/-- info: true -/
#guard_msgs in #eval decide
  (aliasRead state .here 0=some ⟨2^256-1,by decide⟩ ∧
   aliasRead shrunkState .here 0=none ∧
   aliasRead regrownState .here 0=some ⟨2^256-1,by decide⟩ ∧
   aliasRead regrownState (.there .here) 1=some 32767)
/-- info: true -/
#guard_msgs in #eval decide
  (mload shrunkRaw 160=⟨2^256-1,by decide⟩ ∧ mload regrownRaw 192=32767 ∧
   shrunkRaw 240=165 ∧ regrownRaw 240=165 ∧ mload shrunkRaw 64=256 ∧ mload regrownRaw 96=0)
/-- info: true -/
#guard_msgs in #eval (retainedState state placement placement (retainInitial heap placement)
  0 small (mstore raw 128 3)).isNone
/-- info: true -/
#guard_msgs in #eval (retainedState state placement placement (retainInitial heap placement)
  0 small (mstore (mstore raw 128 1) 160 65535)).isNone
/-- info: true -/
#guard_msgs in #eval (retainedState state placement placement (retainInitial heap placement)
  0 Controls.missing raw).isNone

/- A wrong nominal array type reaches the actual source error, not preparation None. -/
/-- info: true -/
#guard_msgs in #eval match retainedState state placement placement (retainInitial heap placement)
    0 Controls.other raw with
  | some (.error (.stuck "memory write type"),_) => true
  | _ => false

/-- The populated actual source state satisfies the unchanged owner's invariant. -/
theorem actual_MemOK : Source.MemOK env heap.ty state := by
  refine ⟨⟨⟨?_,Solidity.Source.HeapTy.Le.refl _⟩,?_⟩,?_,?_⟩
  · apply Solidity.Source.HeapOK.alloc Solidity.Source.HeapOK.empty
    exact .array (fun i => .val (by trivial))
  · exact ⟨⟨Solidity.Yul.Views.NominalMemory.RetainedControls.arrayTy,rfl,rfl⟩,⟨⟨Solidity.Yul.Views.NominalMemory.RetainedControls.arrayTy,rfl,rfl⟩,trivial⟩⟩
  · apply Solidity.Source.HeapShaped.alloc Solidity.Source.HeapShaped.empty
    trivial
  · apply Solidity.Source.HeapInner.alloc (fun a x found => by cases found)
    exact fun i => ⟨Solidity.Yul.Views.NominalMemory.RetainedControls.values i,rfl⟩

end Solidity.Yul.Views.NominalMemory.RetainedControls
