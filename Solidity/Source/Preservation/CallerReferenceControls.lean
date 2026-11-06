import Solidity.Source.Preservation.FrameControls

/-! An inhabited caller memory reference survives callee heap growth. -/
namespace Solidity.Source.Preservation.CallerReferenceControls
open EM
variable {E : Env}

def original : St E := {St.init E with heap :=
  (Heap.empty.alloc ⟨.bytes .memory, Data.bytes [1]⟩).1}
def caller : Locals E.layout [.bytes .memory] := .cons (.memRef rfl 0) .nil

theorem caller_valid : MemOK E (Heap.empty : Heap E.layout).ty (caller, original) := by
  have h0 : MemOK E (Heap.empty : Heap E.layout).ty (.nil, St.init E) :=
    ⟨⟨⟨HeapOK.empty, HeapTy.Le.refl _⟩, trivial⟩, HeapShaped.empty, HeapInner.empty⟩
  have ha := allocBytes_mem (E := E) (Γ := []) (H := (Heap.empty : Heap E.layout).ty) [1] _ h0
  change MemOK E (Heap.empty : Heap E.layout).ty (.nil, original) ∧
    (Val.memRef rfl 0 : Val E.layout (.bytes .memory)).RefOK E (original (E := E)).heap.ty at ha
  exact relocalize ha.1 caller ⟨ha.2, trivial⟩

theorem run_preserves_caller :
    ((sub (.nil : Locals E.layout []) (allocRef (FrameControls.bytes [7, 9]))) :
      EM E [.bytes .memory] (Val E.layout (.bytes .memory) × Locals E.layout [])).run (caller, original) =
    (.ok (.memRef rfl 1, .nil), (caller, {original with heap :=
      ((original (E := E)).heap.alloc ⟨.bytes .memory, FrameControls.bytes [7, 9]⟩).1})) :=
  FrameControls.allocation_success caller original

theorem distinct_contents :
    ((original (E := E)).heap.alloc ⟨.bytes .memory, FrameControls.bytes [7, 9]⟩).1.get 0 =
      some ⟨.bytes .memory, Data.bytes [1]⟩ ∧
    ((original (E := E)).heap.alloc ⟨.bytes .memory, FrameControls.bytes [7, 9]⟩).1.get 1 =
      some ⟨.bytes .memory, Data.bytes [7, 9]⟩ := ⟨rfl, rfl⟩

#print axioms caller_valid
#print axioms run_preserves_caller
#print axioms distinct_contents
end Solidity.Source.Preservation.CallerReferenceControls
