import Solidity.Source.Preservation.AllocationSites
import Solidity.Source.Semantics

/-! Exact actual allocation-before-success and allocation-before-revert controls.
The complete caller locals are restored and the grown heap persists on both.
-/
namespace Solidity.Source.Preservation.FrameControls
open EM
variable {E : Env} {Γ : RCtx}

def bytes (bs : Roadmap.Bytes) : Data E.layout (.bytes .memory) := .bytes bs

theorem allocation_success (l : Locals E.layout Γ) (s : St E) :
    ((sub (.nil : Locals E.layout []) (allocRef (bytes [7, 9]))) :
      EM E Γ (Val E.layout (.bytes .memory) × Locals E.layout [])).run (l, s) =
    (.ok (.memRef rfl (s.heap.alloc ⟨_, bytes [7, 9]⟩).2, .nil),
      (l, {s with heap := (s.heap.alloc ⟨_, bytes [7, 9]⟩).1})) := by rfl

def allocatingRevert : EM E [] Unit := do
  let _ ← allocRef (bytes [7, 9])
  halt (.revert [11])

theorem allocation_revert (l : Locals E.layout Γ) (s : St E) :
    ((sub (.nil : Locals E.layout []) allocatingRevert) :
      EM E Γ (Unit × Locals E.layout [])).run (l, s) =
    (.error (.revert [11]), (l, {s with heap := (s.heap.alloc ⟨_, bytes [7, 9]⟩).1})) := by rfl

theorem callee_preserves (H : HeapTy) : Hoare (MemOK E H) allocatingRevert
    (fun _ y => MemOK E H y) (fun _ y => MemOK E H y) := by
  unfold allocatingRevert
  exact Hoare.bind (allocBytes_mem [7, 9]) fun _ => Hoare.halt' fun _ h => h.1

theorem framed_preserves (H : HeapTy) : Hoare (MemOK E H)
    (sub (.nil : Locals E.layout []) allocatingRevert : EM E Γ _)
    (fun _ y => MemOK E H y) (fun _ y => MemOK E H y) :=
  Hoare.conseq (sub_mem .nil allocatingRevert callee_preserves)
    (fun _ h => ⟨h, trivial⟩) (fun _ _ h => h) (fun _ _ h => h)

theorem inhabited : MemOK E (Heap.empty : Heap E.layout).ty
    (.cons (.bool false) .nil, St.init E) :=
  ⟨⟨⟨HeapOK.empty, HeapTy.Le.refl _⟩, ⟨trivial, trivial⟩⟩, HeapShaped.empty, HeapInner.empty⟩

theorem wrong_revert (l : Locals E.layout Γ) (s : St E) :
    (((sub (.nil : Locals E.layout []) allocatingRevert) : EM E Γ _).run (l, s)).1 ≠ .ok ((), .nil) := by
  rw [allocation_revert]
  intro h
  cases h

#print axioms allocation_success
#print axioms allocation_revert
#print axioms framed_preserves
#print axioms inhabited
end Solidity.Source.Preservation.FrameControls
