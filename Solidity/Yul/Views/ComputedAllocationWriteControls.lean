import Solidity.Yul.Views.ComputedAllocationWrite
import Solidity.Source.Semantics

/-! Incremental allocation changes only the new object and free-pointer bytes.
Actual source contents, prior bytes, dirty padding and unrelated tail survive. -/
namespace Solidity.Yul.Views.ComputedAllocationWrite.Controls
private def E : Source.Env := ⟨[]⟩
private def initial : Source.EMState E [] := (.nil,Source.St.init E)
private def bytes : Source.Data E.layout (.bytes .memory) := .bytes [17]
private def text : Source.Data E.layout (.string .memory) := .string [255,0]
private def p : Placement initial.2.heap := ComputedPlacement.build _ rfl (by decide)
private def input : ByteView := mstore (fun k=>if k=319 then 170 else if k=191 then 99 else 0) 64 128
private def one := objectAllocatedState initial bytes
private def q : Placement one.2.heap := ComputedPlacement.build _ rfl (by decide)
private def two := objectAllocatedState one text
private def rawOne : ByteView := (prepare initial.2.heap p rfl bytes (.bytes 1) rfl (by decide) input).getD input
private def rawTwo : ByteView := (prepare one.2.heap q rfl text (.bytes 2) rfl (by decide) rawOne).getD rawOne

theorem first_step : prepare initial.2.heap p rfl bytes (.bytes 1) rfl (by decide) input=some rawOne := rfl
theorem second_step : prepare one.2.heap q rfl text (.bytes 2) rfl (by decide) rawOne=some rawTwo := rfl

theorem actual_source :
    (Source.allocRef bytes).run initial=(.ok (.memRef rfl 0),one) ∧
    (Source.allocRef text).run one=(.ok (.memRef rfl 1),two) ∧
    (Source.heapBytes (E:=E) (Γ:=[]) 0).run two=(.ok [17],two) ∧
    (Source.heapBytes (E:=E) (Γ:=[]) 1).run two=(.ok [255,0],two) := ⟨rfl,rfl,rfl,rfl⟩

theorem old_region (i : Nat) (low : i<192) (notFree : i<64 ∨ 96≤i) : rawTwo i=rawOne i :=
  residual one.2.heap q rfl text (.bytes 2) rfl (by decide) rawOne rawTwo second_step i (Or.inl low) notFree

theorem unchanged_source :
    let allocated:=placement initial.2.heap p rfl bytes (.bytes 1) rfl (by decide)
    encodeMixedHeap allocated (generatedHeapEntries allocated) rawOne=rawOne ∧
    enumeratedMemoryWriteback one allocated allocated (retainInitial _ _) rawOne=.ok (some (.ok (),one)) := by
  have ok : Source.MemOK E initial.2.heap.ty initial :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have supported : ∀ a τ d,initial.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ := by
    intro a τ d found
    cases found
  have reads : ∀ e∈generatedHeapEntries p,e.image.Reads input (p.address e.id) := by
    intro e member
    cases member
  have result := sound initial.2.heap.ty initial p rfl bytes (.bytes 1) rfl (by decide)
    input rawOne first_step ok trivial (.bytes _) trivial supported reads
  exact ⟨result.2.2.2.1,result.2.2.2.2⟩

theorem reserved_words : ReservedOK rawTwo 256 := by
  have start : ReservedOK input p.free := by
    constructor
    · exact congrArg Fin.val (mload_mstore (fun k=>if k=319 then 170 else if k=191 then 99 else 0) 64 128)
    · intro i
      rw [input,mstore_outside _ _ _ _ (by have hi:=i.isLt;omega)]
      have hi:=i.isLt
      rw [if_neg (by omega),if_neg (by omega)]
  have first : ReservedOK rawOne q.free :=
    reserved initial.2.heap p rfl bytes (.bytes 1) rfl (by decide) input rawOne first_step start
  exact reserved one.2.heap q rfl text (.bytes 2) rfl (by decide) rawOne rawTwo second_step first

private def observed : List Nat :=
  [(mload rawOne 64).val,(mload rawTwo 64).val,(mload rawTwo 128).val,
   (rawTwo 160).toNat,(rawTwo 191).toNat,(mload rawTwo 192).val,
   (rawTwo 224).toNat,(rawTwo 225).toNat,(rawTwo 319).toNat]
/-- info: [192, 256, 1, 17, 99, 2, 255, 0, 170] -/
#guard_msgs in #eval observed
/-- info: false -/
#guard_msgs in #eval observed==[192,256,1,17,0,2,255,0,0]
end Solidity.Yul.Views.ComputedAllocationWrite.Controls
