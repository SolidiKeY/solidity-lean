import Solidity.Backend.MemoryCopies.SourceDefaultFrames
import Solidity.Backend.MemoryCopies.SourceRootCopies
import Solidity.Source.Eval

/-! Nonempty, nested and partial-allocation controls for the Source frame laws.
The declared storage root is an array of bytes; both child objects and the
copied parent have fresh, distinct identities. No emitted-code claim is made. -/
namespace Solidity.Backend.MemoryCopies.SourceFramesControls

private def rootDecl : Source.Decl :=
  ⟨.stateVar, "root", none, true,
    .stateVar (.array (.elem .bytes) .none) none none none false "root" .none⟩
private def E : Source.Env := ⟨[rootDecl]⟩
private def path : Source.SPath := ⟨⟨none, "root"⟩, []⟩
private def frame : Source.Fr :=
  {this := ⟨1, by decide⟩, sender := ⟨2, by decide⟩, value := ⟨0, by decide⟩,
    static := false, contract := "C"}
private def T : Source.STy := .array .memory (.bytes .memory) none
private def child : Source.Data E.layout (.bytes .memory) := .bytes []
private def storage : Source.Storage E.layout E.cellTy :=
  ((Source.Storage.empty.write path (.int 2 (by decide))).write
    (path.go (.index 0)) (.int 0 (by decide))).write
    (path.go (.index 1)) (.int 0 (by decide))
private def before : Source.EMState E [.bool] :=
  (.cons (.bool true) .nil,
   {ex := ⟨⟨fun _ => ⟨⟨17, by decide⟩, 3, some 9, storage⟩⟩,
      Source.Transient.empty, [.account ⟨99, by decide⟩ (Source.Account.empty _)]⟩,
    heap := (Source.Heap.empty.alloc ⟨.bool, .val (.bool true)⟩).1,
    events := [], logs := [(⟨13, by decide⟩, [1,2])],
    fnLocals := ⟨[.bool], .cons (.bool false) .nil⟩})
private def oneChild : Source.EMState E [.bool] := allocatedState child before
private def twoChildren : Source.EMState E [.bool] := allocatedState child oneChild
private def data : Source.Data E.layout T :=
  .array 2 (fun _ impossible => nomatch impossible)
    (Source.finCons (.val (.memRef rfl before.2.heap.next))
      (Source.finCons (.val (.memRef rfl oneChild.2.heap.next)) Fin.elim0))
private def after : Source.EMState E [.bool] := allocatedState data twoChildren
private def fixedT : Source.STy := .array .memory (.bytes .memory) (some 2)
private def fixedData : Source.Data E.layout fixedT :=
  .array 2 (fun _ equality => by cases equality; rfl)
    (Source.finCons (.val (.memRef rfl before.2.heap.next))
      (Source.finCons (.val (.memRef rfl oneChild.2.heap.next)) Fin.elim0))
private def fixedAfter : Source.EMState E [.bool] := allocatedState fixedData twoChildren

/-- The fixture uses a declared dynamic storage array of reference elements. -/
theorem declared : E.pathTy path = some (.array .storage (.bytes .storage) none) := rfl

theorem default_frames_inhabited : Nonempty (DefaultTraversalFrameCertificate E [.bool]) :=
  ⟨defaultTraversalFrames E [.bool]⟩

theorem storage_frames_inhabited : Nonempty (StorageTraversalFrameCertificate E [.bool] frame) :=
  ⟨storageTraversalFrames E [.bool] frame⟩

/-- The second child times out after the first bytes object has been allocated. -/
theorem default_partial_timeout :
    (Source.zeroVal (E := E) (Γ := [.bool]) 5
      (.array .memory (.bytes .memory) (some 2))).run before =
        (.error .timeout, oneChild) := rfl

theorem load_partial_timeout :
    (Source.loadMem (E := E) (Γ := [.bool]) frame 5 T path).run before =
      (.error .timeout, oneChild) := rfl

theorem partial_timeout_keeps_allocation : oneChild.2.heap.next = before.2.heap.next + 1 ∧
    oneChild.2.heap.get before.2.heap.next = some ⟨.bytes .memory, child⟩ ∧
    oneChild.2.heap.get 0 = before.2.heap.get 0 := ⟨rfl, rfl, rfl⟩

/-- Rolling the timed-out frame back to its input would lose a real child. -/
theorem partial_state_ne_input : oneChild ≠ before := by
  intro equality
  have frontier : oneChild.2.heap.next = before.2.heap.next :=
    congrArg (fun state : Source.EMState E [.bool] => state.2.heap.next) equality
  change 2 = 1 at frontier
  contradiction

theorem nested_default :
    (Source.zeroVal (E := E) (Γ := [.bool]) 6 fixedT).run before =
      (.ok (.memRef rfl 3), fixedAfter) := rfl

def nested_default_certificate :
    SourceDefaultCertificate 6 fixedT rfl before fixedAfter 3 fixedData := by
  have preserved : AllocationExtension before fixedAfter := by
    have result : AllocationExtension before
        ((Source.zeroVal (E := E) (Γ := [.bool]) 6 fixedT).run before).2 :=
      zeroVal_allocates 6 fixedT before
    rw [nested_default] at result
    exact result
  exact ⟨nested_default, preserved.frame, preserved.growth, by decide, rfl, preserved.old⟩

theorem nested_load :
    (Source.loadMem (E := E) (Γ := [.bool]) frame 6 T path).run before =
      (.ok data, twoChildren) := rfl

def nested_copy_certificate :
    SourceStorageCopyCertificate frame 6 T rfl path before twoChildren after
      twoChildren.2.heap.next data :=
  storageCopyCertificate frame 6 T rfl path before twoChildren data nested_load

theorem nested_root_and_children :
    after.2.heap.get 1 = some ⟨.bytes .memory, child⟩ ∧
    after.2.heap.get 2 = some ⟨.bytes .memory, child⟩ ∧
    after.2.heap.get 3 = some ⟨T, data⟩ ∧
    after.2.heap.get 0 = before.2.heap.get 0 ∧ after.2.heap.next = 4 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem nested_reference_observations :
    (Source.memElem (E := E) (Γ := [.bool]) 3 0 (.bytes .memory)).run after =
      (.ok (.memRef rfl 1), after) ∧
    (Source.memElem (E := E) (Γ := [.bool]) 3 1 (.bytes .memory)).run after =
      (.ok (.memRef rfl 2), after) ∧
    (Source.memElem (E := E) (Γ := [.bool]) 3 2 (.bytes .memory)).run after =
      (Source.panic .index, after) := ⟨rfl, rfl, rfl⟩

#print axioms default_frames_inhabited
#print axioms storage_frames_inhabited
#print axioms default_partial_timeout
#print axioms load_partial_timeout
#print axioms partial_timeout_keeps_allocation
#print axioms partial_state_ne_input
#print axioms nested_default
#print axioms nested_default_certificate
#print axioms nested_load
#print axioms nested_copy_certificate
#print axioms nested_root_and_children
#print axioms nested_reference_observations
end Solidity.Backend.MemoryCopies.SourceFramesControls
