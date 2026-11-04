import Solidity.Yul.Views.AllocationSequence
import Solidity.Yul.Views.AllocationRefreshControls

/-! Three actual allocations return typed references; the last object contains
a real pointer to the first. Finite certification is not Source admission.
Initial arbitrary bytes, padding and reserved words are genuine inputs. -/
namespace Solidity.Yul.Views.AllocationSequence.Controls
open AllocationRefresh.Controls

def third : Source.Data E.layout (.array .memory (.bytes .memory) (some 1)) :=
  .array 1 (fun _ same => (Option.some.inj same).symm) (fun _ => .val (.memRef rfl 0))
def two := objectAllocatedState one second
def final := objectAllocatedState two third

def requests : List (Request E) := [⟨_,first⟩,⟨_,second⟩,⟨_,third⟩]

theorem certified : Certified initial p rfl requests := by
  unfold requests
  apply Certified.cons first (.bytes 3) rfl (by decide) trivial (.bytes _) trivial
  apply Certified.cons second (.bytes 1) rfl (by decide) trivial (.string _) trivial
  apply Certified.cons third (.array false 1) rfl (by decide)
    (fun _ => ⟨_,rfl⟩) (.array (fun _ => .val ⟨.bytes .memory,rfl,rfl⟩))
    (Or.inl (Or.inr (Or.inr rfl)))
  exact Certified.nil _ _ _

def returned : Source.Vals E.layout (requests.map Sigma.fst) :=
  .cons (.memRef rfl 0) (.cons (.memRef rfl 1) (.cons (.memRef rfl 2) .nil))

theorem actual : (program requests).run initial=(.ok returned,final) := rfl

theorem realized : ∃ (q : Placement final.2.heap) (raw : ByteView),
    encodeMixedHeap q (generatedHeapEntries q) raw=raw ∧
    enumeratedMemoryWriteback final q q (retainInitial _ _) raw=.ok (some (.ok (),final)) ∧
    ReservedOK raw q.free ∧ Source.RValsOK E final.2.heap.ty returned.toR := by
  have ok : Source.MemOK E initial.2.heap.ty initial :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have supported : ∀ a τ d,initial.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ := by
    intro a τ d found
    cases found
  have reads : ∀ e∈generatedHeapEntries p,e.image.Reads input (p.address e.id) := by
    intro e member
    cases member
  have reserved : ReservedOK input p.free := by
    constructor
    · exact congrArg Fin.val (mload_mstore (fun i=>if i=191 then 99 else if i=255 then 77 else if i=319 then 170 else 0) 64 128)
    · intro i
      rw [input,mstore_outside _ _ _ _ (by have hi:=i.isLt;omega)]
      have hi:=i.isLt
      rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  obtain ⟨after,values,q,raw,run,computed,safe,whole,writeback,validReserved,validResults⟩ :=
    realize certified initial.2.heap.ty ok input supported reads reserved
  have stateEq : after=final := congrArg Prod.snd (run.symm.trans actual)
  subst after
  have valuesEq : values=returned := Except.ok.inj (congrArg Prod.fst (run.symm.trans actual))
  subst values
  exact ⟨q,raw,whole,writeback,validReserved,validResults⟩

/-- No physical certificate means neither refusal nor a successful no-op. -/
theorem uncertified_actual_halt :
    (program (E:=E) (Γ:=[]) [⟨.bool,.val (.bool true)⟩]).run initial=
      (.error (.stuck "memory reference type"),objectAllocatedState initial (.val (.bool true))) := rfl
theorem empty_identity : (program (E:=E) (Γ:=[]) []).run initial=(.ok .nil,initial) ∧
    input 191=99 ∧ input 255=77 ∧ input 319=170 := ⟨rfl,by decide,by decide,by decide⟩

theorem dangling_source_success :
    (program (E:=E) (Γ:=[]) [⟨_,third⟩]).run initial=
      (.ok (.cons (.memRef rfl 0) .nil),objectAllocatedState initial third) := rfl

theorem dangling_not_owner_valid : ¬Source.DataOK E initial.2.heap.ty third := by
  first | (simp only;done) | decide | omega | rfl | skip
  intro invalid
  cases invalid with
  | array elements =>
    have element := elements ⟨0,by decide⟩
    cases element with
    | val reference =>
      obtain ⟨τ,found,shape⟩ := reference
      cases found
end Solidity.Yul.Views.AllocationSequence.Controls
