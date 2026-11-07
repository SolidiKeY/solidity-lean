import Solidity.Yul.Views.SharedZeroRead
import Solidity.Source.Semantics

/-! Two distinct empty-array identities produced by actual Source.allocRef.
A reserved-zero header agrees with their reads, but is not a physical allocator
or invertible pointer encoding. Exact Source Panic bytes and corrupted-header
negatives distinguish these limited observations from whole view adequacy. -/
namespace Solidity.Yul.Views.SharedZeroRead.Controls

def E : Source.Env := ⟨[]⟩
def element : Source.STy := .int Source.IntTy.u256
def ty : Source.STy := .array .memory element none
def frame : Source.Fr :=
  {this:=1,sender:=2,value:=0,static:=false,contract:="ZeroRead",checked:=true,depth:=0,cd:=[]}
def start : Source.EMState E [] := (.nil,Source.St.init E)
def allocations : Source.EM E [] (Source.Val E.layout ty × Source.Val E.layout ty) := do
  let one ← Source.allocRef (emptyArray E.layout element)
  let two ← Source.allocRef (emptyArray E.layout element)
  pure (one,two)
def allocated := (allocations.run start).2

theorem actual_producer : allocations.run start=
    (.ok (.memRef rfl 0,.memRef rfl 1),allocated) := rfl

theorem found_zero : allocated.2.heap.get 0=some ⟨ty,emptyArray E.layout element⟩ := rfl
theorem found_one : allocated.2.heap.get 1=some ⟨ty,emptyArray E.layout element⟩ := rfl

def memory : ByteView := mstore (fun _=>0) 64 128
theorem reserved : ReservedOK memory 128 := by
  first | (simp only;done) | decide | omega | rfl | skip
  constructor
  · exact congrArg Fin.val (mload_mstore (fun _=>0) 64 128)
  · intro i
    exact mstore_outside (fun _=>0) 64 (96+i.val) 128 (by omega)

theorem shared_reads :
    (Source.lengthOf frame (.memRef (τ:=ty) rfl 0)).run allocated=(.ok 0,allocated) ∧
    (Source.lengthOf frame (.memRef (τ:=ty) rfl 1)).run allocated=(.ok 0,allocated) ∧
    mload memory pointer.val=0 := by
  first | omega | decide | skip
  exact ⟨length allocated frame 0 element found_zero,length allocated frame 1 element found_one,
    header memory 128 reserved⟩

theorem all_indices_fail (i : Nat) :
    (Source.indexLoc frame (.memRef (τ:=ty) rfl 0) i).run allocated=
      (.error (.revert (Source.panicData .index)),allocated) ∧
    (Source.indexLoc frame (.memRef (τ:=ty) rfl 1) i).run allocated=
      (.error (.revert (Source.panicData .index)),allocated) := by
  first | omega | decide | skip
  exact ⟨index allocated frame 0 i element found_zero,index allocated frame 1 i element found_one⟩

theorem full_panic : Source.panicData .index=
    [78,72,123,113,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,50] := by decide

theorem no_ordinary (p : Placement allocated.2.heap) : p.address 0≠96 ∧ p.address 1≠96 := by
  first | omega | decide | skip
  exact ⟨not_ordinary p 0 element found_zero,not_ordinary p 1 element found_one⟩

theorem no_both_inverse (decode : Roadmap.Word → Option (Source.Val E.layout ty)) :
    ¬(decode pointer=some (.memRef rfl 0) ∧ decode pointer=some (.memRef rfl 1)) :=
  no_identity_inverse E.layout element 0 1 (by decide) decode

/-- Actual Source identities are distinct even though the header reads agree. -/
theorem distinct_source : (Source.Val.memRef (D:=E.layout) (τ:=ty) rfl 0)≠.memRef rfl 1 := by
  first | (simp only;done) | decide | omega | rfl | skip
  intro same
  injection same with typeEqual ids
  omega

def corrupted := saveByte memory 96 1
theorem wrong_header : mload corrupted 96≠0 := by decide

theorem corrupted_not_reserved : ¬ReservedOK corrupted 128 := by
  first | omega | decide | skip
  intro bad
  have byte := bad.2 ⟨0,by decide⟩
  change (1:UInt8)=0 at byte
  exact (by decide : (1:UInt8)≠0) byte
end Solidity.Yul.Views.SharedZeroRead.Controls
