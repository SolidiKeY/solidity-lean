import Solidity.Backend.MemoryCopies.SourceStoredFieldsInterface
import Solidity.Backend.MemoryCopies.SourceNestedBytes
import Solidity.Backend.MemoryCopies.SourceStrings

/-! Existing Source heterogeneous storage traversal and fresh struct copying. -/
namespace Solidity.Backend.MemoryCopies

def SourceStoredValue.primitive {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    {frame : Source.Fr} {path : Source.SPath} {before : Source.EMState E Γ}
    (value : Source.Val E.layout τ) (nonref : τ.byRef = false)
    (cell : PersistentSourceCell frame path before value) : SourceStoredValue frame path before τ where
  horizon := 1
  objects := 0
  horizon_positive := by decide
  execution := by
    intro input extension slack
    refine ⟨value,input,?_,AllocationExtension.refl input,rfl⟩
    have budget : 1 + slack = slack + 1 := by omega
    rw [budget,Source.loadElem]
    simp only [nonref,Bool.false_eq_true,if_false]
    exact (cell.transport extension).read

def SourceStoredValue.bytes {E : Source.Env} {Γ : Source.RCtx} {frame : Source.Fr}
    {path : Source.SPath} {before : Source.EMState E Γ} {bytes : List UInt8}
    (stored : StoredSourceBytes frame path before bytes) : SourceStoredValue frame path before (.bytes .memory) where
  horizon := bytes.length + 3
  objects := 1
  horizon_positive := by omega
  execution := by
    intro input extension slack
    have actual : StoredSourceBytes frame path input bytes := stored.transport extension
    have copy : SourceStorageCopyCertificate frame (bytes.length + 2 + slack) (.bytes .memory) rfl path
        input input (allocatedState (Source.Data.bytes (l := .memory) bytes) input) input.2.heap.next
        (Source.Data.bytes bytes) := sourceBytesCopy frame path input bytes slack actual.range actual.length actual.payload
    refine ⟨.memRef rfl input.2.heap.next,allocatedState (Source.Data.bytes (l := .memory) bytes) input,?_,
      AllocatesOnly.alloc (Source.Data.bytes (l := .memory) bytes) input,rfl⟩
    have budget : bytes.length + 2 + slack + 1 = bytes.length + 3 + slack := by omega
    simpa only [budget] using copy.execution

def SourceStoredValue.string {E : Source.Env} {Γ : Source.RCtx} {frame : Source.Fr}
    {path : Source.SPath} {before : Source.EMState E Γ} {bytes : List UInt8}
    (stored : StoredSourceBytes frame path before bytes) : SourceStoredValue frame path before (.string .memory) where
  horizon := bytes.length + 3
  objects := 1
  horizon_positive := by omega
  execution := by
    intro input extension slack
    have actual : StoredSourceBytes frame path input bytes := stored.transport extension
    have copy : SourceStorageCopyCertificate frame (bytes.length + 2 + slack) (.string .memory) rfl path
        input input (allocatedState (Source.Data.string (l := .memory) bytes) input) input.2.heap.next
        (Source.Data.string bytes) := sourceStringCopies.copy E Γ frame path input bytes slack actual.range actual.length actual.payload
    refine ⟨.memRef rfl input.2.heap.next,allocatedState (Source.Data.string (l := .memory) bytes) input,?_,
      AllocatesOnly.alloc (Source.Data.string (l := .memory) bytes) input,rfl⟩
    have budget : bytes.length + 2 + slack + 1 = bytes.length + 3 + slack := by omega
    simpa only [budget] using copy.execution

def SourceStoredFields.nil {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
    (path : Source.SPath) (before : Source.EMState E Γ) (start : Nat) :
    SourceStoredFields frame path before start [] where
  horizon := 1
  objects := 0
  horizon_positive := by decide
  execution := by
    intro input extension slack
    refine ⟨.nil,input,?_,AllocationExtension.refl input,rfl⟩
    have budget : 1 + slack = slack + 1 := by omega
    rw [budget]
    rfl

def SourceStoredFields.cons {E : Source.Env} {Γ : Source.RCtx} {frame : Source.Fr}
    {path : Source.SPath} {before : Source.EMState E Γ} {start : Nat} {τ : Source.STy} {types : List Source.STy}
    (head : SourceStoredValue frame (path.go (.field start)) before τ)
    (tail : SourceStoredFields frame path before (start + 1) types) :
    SourceStoredFields frame path before start (τ :: types) where
  horizon := head.horizon + tail.horizon + 1
  objects := head.objects + tail.objects
  horizon_positive := by omega
  execution := by
    intro input extension slack
    obtain ⟨value,middle,first,firstFrame,firstCount⟩ := head.execution input extension (tail.horizon + slack)
    obtain ⟨data,after,rest,restFrame,restCount⟩ := tail.execution middle (extension.trans firstFrame) (head.horizon + slack)
    have firstRun : (Source.loadElem (E := E) (Γ := Γ) frame (head.horizon + tail.horizon + slack)
        τ (path.go (.field start))).run input = (.ok value,middle) := by
      simpa only [Nat.add_assoc] using first
    have restRun : (Source.loadFields (E := E) (Γ := Γ) frame (head.horizon + tail.horizon + slack)
        types path (start + 1)).run middle = (.ok data,after) := by
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using rest
    refine ⟨.cons (.val value) data,after,?_,firstFrame.trans restFrame,?_⟩
    · have budget : head.horizon + tail.horizon + 1 + slack = (head.horizon + tail.horizon + slack) + 1 := by omega
      rw [budget,Source.loadFields,Source.Hoare.run_bind,firstRun]
      dsimp only
      rw [Source.Hoare.run_bind,restRun]
      rfl
    · rw [restCount,firstCount]
      omega

/-- The exact environment layout indexes the traversal. Its aggregate load and
fresh parent allocation are derived, not assumed as a Source run premise. -/
theorem SourceStoredFields.structCopy {E : Source.Env} {Γ : Source.RCtx} {frame : Source.Fr}
    {path : Source.SPath} {before : Source.EMState E Γ} (name : Source.DeclName)
    (fields : SourceStoredFields frame path before 0 (E.layout.fields name))
    (input : Source.EMState E Γ) (extension : AllocationExtension before input) (slack : Nat) :
    ∃ (data : Source.Data E.layout (.struct .memory name)) (loaded : Source.EMState E Γ),
      SourceStorageCopyCertificate frame (fields.horizon + 1 + slack) (.struct .memory name) rfl path
        input loaded (allocatedState data loaded) loaded.2.heap.next data ∧
      loaded.2.heap.next = input.2.heap.next + fields.objects := by
  obtain ⟨values,loaded,execution,_,count⟩ := fields.execution input extension slack
  let data : Source.Data E.layout (.struct .memory name) := .struct values
  have load : (Source.loadMem (E := E) (Γ := Γ) frame (fields.horizon + 1 + slack)
      (.struct .memory name) path).run input = (.ok data,loaded) := by
    have budget : fields.horizon + 1 + slack = (fields.horizon + slack) + 1 := by omega
    rw [budget,Source.loadMem,Source.Hoare.run_bind,execution]
    rfl
  exact ⟨data,loaded,storageCopyCertificate frame _ _ rfl path input loaded data load,count⟩

#print axioms SourceStoredValue.primitive
#print axioms SourceStoredValue.bytes
#print axioms SourceStoredValue.string
#print axioms SourceStoredFields.nil
#print axioms SourceStoredFields.cons
#print axioms SourceStoredFields.structCopy
end Solidity.Backend.MemoryCopies
