import Solidity.Yul.Views.NominalMemory

/-! Canonical nominal-word, actual allocated-array, alias-read and source-error controls. -/

namespace Solidity.Yul.Views.NominalMemory.Controls
open Solidity.Yul.Views

def small : Source.DeclName := ⟨none,"Small"⟩
def other : Source.DeclName := ⟨none,"Other"⟩
def tag : Source.DeclName := ⟨none,"Tag"⟩
def flag : Source.DeclName := ⟨none,"Flag"⟩
def missing : Source.DeclName := ⟨none,"Missing"⟩
def i16 : Source.IntTy := ⟨true,16,by decide⟩
def env : Source.Env := ⟨[
  ⟨.udvt,"Small",none,true,.udvt "Small" (.int true 16 (by decide))⟩,
  ⟨.udvt,"Other",none,true,.udvt "Other" (.int true 16 (by decide))⟩,
  ⟨.udvt,"Tag",none,true,.udvt "Tag" (.fixedBytes 3 (by decide))⟩,
  ⟨.udvt,"Flag",none,true,.udvt "Flag" .bool⟩]⟩

def inspect (name : Source.DeclName) (w : Roadmap.Word) : Option Roadmap.Word :=
  (decodeDeclared env name w).bind Source.Val.word
/-- info: true -/
#guard_msgs in #eval decide (declaredUDVT env small=true ∧ env.layout.underlying small=.int i16)
/-- info: true -/
#guard_msgs in #eval decide (inspect small ⟨2^256-1,by decide⟩=some ⟨2^256-1,by decide⟩)
/-- info: true -/
#guard_msgs in #eval decide (inspect small ⟨2^256-32768,by decide⟩=some ⟨2^256-32768,by decide⟩)
/-- info: true -/
#guard_msgs in #eval decide (inspect small 32767=some 32767 ∧ inspect small 65535=none)
/-- info: true -/
#guard_msgs in #eval decide (inspect flag 1=some 1 ∧ inspect flag 2=none)
/-- info: true -/
#guard_msgs in #eval decide (inspect tag ⟨0x112233*2^232,by decide⟩=some ⟨0x112233*2^232,by decide⟩ ∧ inspect tag 0x112233=none)
/- Missing metadata must not use Layout's bool fallback as a declaration. -/
/-- info: true -/
#guard_msgs in #eval decide (env.layout.underlying missing=.bool ∧ declaredUDVT env missing=false ∧ inspect missing 0=none)
/-- info: false -/
#guard_msgs in #eval decide (small=other)

def arrayTy : Source.STy := .array .memory (.udvt small) (some 2)
def lengthOK : ∀ z,(some 2:Option Nat)=some z → z=2 := fun _ h => (Option.some.inj h).symm
def values : Fin 2 → Source.Val env.layout (.udvt small) := fun i =>
  .udvt (.int (if i.val=0 then -1 else 32767) (by split <;> decide))
def data : Source.Data env.layout arrayTy := memberArrayData env.layout (.udvt small) (some 2) 2 lengthOK values
def heap : Source.Heap env.layout := (Source.Heap.empty.alloc ⟨arrayTy,data⟩).1

def placement : Placement heap where
  address a := 128+a*128
  shape _ := .array false 2
  free := 256
  free_start := by decide
  distinct a b _ _ same := by omega
  typed a ty d found := by
    by_cases zero : a=0
    · subst a
      change (some ⟨arrayTy,data⟩ : Option (Σ t,Source.Data env.layout t))=some ⟨ty,d⟩ at found
      cases found
      exact .array 2 lengthOK _
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
    change 128+a*128+64≤128+b*128 ∨ 128+b*128+64≤128+a*128
    omega

def state : Source.EMState env [arrayTy,arrayTy] :=
  ⟨.cons (.memRef rfl 0) (.cons (.memRef rfl 0) .nil),
    ⟨⟨⟨fun _ => Source.Account.empty _⟩,.empty,[]⟩,heap,[],[],⟨[],.nil⟩⟩⟩
def oldRaw : ByteView := mstore (mstore (fun _=>165) 128 ⟨2^256-1,by decide⟩) 160 32767
def newRaw : ByteView := mstore (mstore oldRaw 128 ⟨2^256-32768,by decide⟩) 160 0
def newValues : Fin 2 → Source.Val env.layout (.udvt small) := fun i =>
  .udvt (.int (if i.val=0 then -32768 else 0) (by split <;> decide))
def newData : Source.Data env.layout arrayTy :=
  memberArrayData env.layout (.udvt small) (some 2) 2 lengthOK newValues
def newHeap : Source.Heap env.layout := heap.write 0 newData (heap_ty_of_get heap 0 _ data rfl)
def newState : Source.EMState env [arrayTy,arrayTy] := withSourceHeap state newHeap

def observe (root : Nat) (m : ByteView) : List Nat :=
  match arrayState state placement root small (some 2) 2 lengthOK m with
  | some (.ok (),after) =>
    match after.2.heap.get root with
    | some ⟨.array _ _ _,.array _ _ _⟩ =>
      [1,after.2.heap.next,(m 212).toNat]
    | _ => [2]
  | some (.error _,_) => [3]
  | none => [0]
/-- info: [1, 1, 165] -/
#guard_msgs in #eval observe 0 oldRaw
/-- info: [1, 1, 165] -/
#guard_msgs in #eval observe 0 newRaw
/-- info: [3] -/
#guard_msgs in #eval observe 1 (mstore (mstore oldRaw 256 0) 288 1)
/-- info: [0] -/
#guard_msgs in #eval observe 0 (mstore oldRaw 128 65535)

def readFrame : Source.Fr :=
  {this:=0,sender:=0,value:=0,static:=false,contract:="Nominal",checked:=true,depth:=0,cd:=[]}
def aliasRead (s : Source.EMState env [arrayTy,arrayTy]) (alias : Source.Idx [arrayTy,arrayTy] arrayTy)
    (index : Nat) : Option Roadmap.Word :=
  match ((do
    let loc ← Source.indexLoc readFrame (s.1.get alias) index
    Source.readLoc readFrame loc) : Source.EM env [arrayTy,arrayTy] (Source.Val env.layout (.udvt small))).run s with
  | (.ok v,_) => v.word
  | _ => none

def aliasesAgree (m : ByteView) (a b : Roadmap.Word) : Bool :=
  match arrayState state placement 0 small (some 2) 2 lengthOK m with
  | some (.ok (),after) => decide (aliasRead after .here 0=some a ∧ aliasRead after (.there .here) 0=some a ∧
      aliasRead after .here 1=some b ∧ aliasRead after (.there .here) 1=some b)
  | _ => false
/-- info: true -/
#guard_msgs in #eval aliasesAgree oldRaw ⟨2^256-1,by decide⟩ 32767
/-- info: true -/
#guard_msgs in #eval aliasesAgree newRaw ⟨2^256-32768,by decide⟩ 0
/-- info: false -/
#guard_msgs in #eval aliasesAgree newRaw 32768 0
/-- info: true -/
#guard_msgs in #eval match arrayState state placement 0 other (some 2) 2 lengthOK newRaw with
  | some (.error (.stuck "memory write type"),_) => true
  | _ => false

/-- A changed canonical snapshot executes a genuine typed source heap update. -/
theorem changed_source :
    arrayState state placement 0 small (some 2) 2 lengthOK newRaw=some (.ok (),newState) := by
  unfold arrayState
  simp only [show declaredUDVT env small=true from rfl,
    show arrayLengthChoice (some 2) newRaw (placement.address 0)=2 from rfl,
    BEq.rfl,Bool.and_self,↓reduceIte]
  rw [array_decode_encode env.layout small (by trivial) 2 newRaw _ newValues (by decide)]
  simp only [Option.map_some]
  exact congrArg some (memberArrayHeapPut_run state 0 (.udvt small) (some 2) 2 lengthOK newValues (by rfl))

/-- Kernel equality of the complete source result and state, not only alias reads. -/
theorem unchanged_whole_state :
    arrayState state placement 0 small (some 2) 2 lengthOK oldRaw=some (.ok (),state) := by
  apply arrayState_unchanged (old := values)
  · decide
  · trivial
  · rfl
  · rfl
  · decide

/-- Missing metadata cannot use the layout bool fallback, even for zero elements. -/
theorem missing_declaration :
    arrayState state placement 0 missing (some 2) 2 lengthOK oldRaw=none := by
  rfl

theorem empty_still_checks_declaration :
    arrayState state placement 0 missing (some 0) 0
      (fun z h => (Option.some.inj h).symm) oldRaw=none := by
  rfl

theorem actual_MemOK : Source.MemOK env heap.ty state := by
  refine ⟨⟨⟨?_,Solidity.Source.HeapTy.Le.refl _⟩,?_⟩,?_,?_⟩
  · apply Solidity.Source.HeapOK.alloc Solidity.Source.HeapOK.empty
    exact .array (fun i => .val (by trivial))
  · exact ⟨⟨Solidity.Yul.Views.NominalMemory.Controls.arrayTy,rfl,rfl⟩,⟨⟨Solidity.Yul.Views.NominalMemory.Controls.arrayTy,rfl,rfl⟩,trivial⟩⟩
  · apply Solidity.Source.HeapShaped.alloc Solidity.Source.HeapShaped.empty
    trivial
  · apply Solidity.Source.HeapInner.alloc (fun a x found => by cases found)
    exact fun i => ⟨Solidity.Yul.Views.NominalMemory.Controls.values i,rfl⟩

end Solidity.Yul.Views.NominalMemory.Controls
