import Solidity.Backend.MemoryCopies.SourceStoredElementsInterface

/-! Generic element traversal and array closure over proved existing Source copies. -/
namespace Solidity.Backend.MemoryCopies

def SourceStoredElements.nil {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
    (path : Source.SPath) (before : Source.EMState E Γ) (start : Nat) (element : Source.STy) :
    SourceStoredElements frame path before start element 0 where
  horizon := 1
  objects := 0
  horizon_positive := by decide
  execution := by
    intro input extension slack
    refine ⟨Fin.elim0,input,?_,AllocationExtension.refl input,rfl⟩
    have budget : 1 + slack = slack + 1 := by omega
    rw [budget]
    rfl

def SourceStoredElements.cons {E : Source.Env} {Γ : Source.RCtx} {frame : Source.Fr}
    {path : Source.SPath} {before : Source.EMState E Γ} {start count : Nat} {element : Source.STy}
    (head : SourceStoredValue frame (path.go (.index start)) before element)
    (tail : SourceStoredElements frame path before (start + 1) element count) :
    SourceStoredElements frame path before start element (count + 1) where
  horizon := head.horizon + tail.horizon + 1
  objects := head.objects + tail.objects
  horizon_positive := by omega
  execution := by
    intro input extension slack
    obtain ⟨value,middle,first,firstFrame,firstCount⟩ := head.execution input extension (tail.horizon + slack)
    obtain ⟨values,after,rest,restFrame,restCount⟩ := tail.execution middle (extension.trans firstFrame) (head.horizon + slack)
    have firstRun : (Source.loadElem (E := E) (Γ := Γ) frame (head.horizon + tail.horizon + slack)
        element (path.go (.index start))).run input = (.ok value,middle) := by
      simpa only [Nat.add_assoc] using first
    have restRun : (Source.loadElems (E := E) (Γ := Γ) frame (head.horizon + tail.horizon + slack)
        element path (start + 1) count).run middle = (.ok values,after) := by
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using rest
    refine ⟨Source.finCons (.val value) values,after,?_,firstFrame.trans restFrame,?_⟩
    · have budget : head.horizon + tail.horizon + 1 + slack = (head.horizon + tail.horizon + slack) + 1 := by omega
      rw [budget]
      change (do
        let value ← Source.loadElem (E := E) (Γ := Γ) frame (head.horizon + tail.horizon + slack)
          element (path.go (.index start))
        let rest ← Source.loadElems frame (head.horizon + tail.horizon + slack) element path (start + 1) count
        pure (Source.finCons (Source.Data.val value) rest)).run input = _
      rw [Source.Hoare.run_bind,firstRun]
      dsimp only
      rw [Source.Hoare.run_bind,restRun]
      rfl
    · rw [restCount,firstCount]
      omega

theorem SourceStoredElements.dynamicCopy {E : Source.Env} {Γ : Source.RCtx} {frame : Source.Fr}
    {path : Source.SPath} {before : Source.EMState E Γ} {element : Source.STy} {count : Nat}
    (elements : SourceStoredElements frame path before 0 element count)
    (range : Source.IntTy.u256.lo ≤ (count : Int) ∧ (count : Int) ≤ Source.IntTy.u256.hi)
    (length : PersistentSourceCell frame path before (Source.Val.int count range))
    (input : Source.EMState E Γ) (extension : AllocationExtension before input) (slack : Nat) :
    ∃ (data : Source.Data E.layout (.array .memory element none)) (loaded : Source.EMState E Γ),
      SourceStorageCopyCertificate frame (elements.horizon + 1 + slack) (.array .memory element none) rfl path
        input loaded (allocatedState data loaded) loaded.2.heap.next data ∧
      loaded.2.heap.next = input.2.heap.next + elements.objects := by
  obtain ⟨values,loaded,execution,_,frontier⟩ := elements.execution input extension slack
  let data : Source.Data E.layout (.array .memory element none) := .array count (fun _ impossible => nomatch impossible) values
  have sizeRead : (Source.readLen (E := E) (Γ := Γ) frame path).run input = (.ok count,input) := by
    rw [Source.readLen,Source.Hoare.run_bind,(length.transport extension).read]
    rfl
  have load : (Source.loadMem (E := E) (Γ := Γ) frame (elements.horizon + 1 + slack)
      (.array .memory element none) path).run input = (.ok data,loaded) := by
    have budget : elements.horizon + 1 + slack = (elements.horizon + slack) + 1 := by omega
    rw [budget,Source.loadMem,Source.Hoare.run_bind,sizeRead]
    dsimp only
    rw [Source.Hoare.run_bind,execution]
    rfl
  exact ⟨data,loaded,storageCopyCertificate frame _ _ rfl path input loaded data load,frontier⟩

theorem SourceStoredElements.fixedCopy {E : Source.Env} {Γ : Source.RCtx} {frame : Source.Fr}
    {path : Source.SPath} {before : Source.EMState E Γ} {element : Source.STy} {count : Nat}
    (elements : SourceStoredElements frame path before 0 element count)
    (input : Source.EMState E Γ) (extension : AllocationExtension before input) (slack : Nat) :
    ∃ (data : Source.Data E.layout (.array .memory element (some count))) (loaded : Source.EMState E Γ),
      SourceStorageCopyCertificate frame (elements.horizon + 1 + slack) (.array .memory element (some count)) rfl path
        input loaded (allocatedState data loaded) loaded.2.heap.next data ∧
      loaded.2.heap.next = input.2.heap.next + elements.objects := by
  obtain ⟨values,loaded,execution,_,frontier⟩ := elements.execution input extension slack
  let data : Source.Data E.layout (.array .memory element (some count)) := .array count (fun _ h => by cases h; rfl) values
  have load : (Source.loadMem (E := E) (Γ := Γ) frame (elements.horizon + 1 + slack)
      (.array .memory element (some count)) path).run input = (.ok data,loaded) := by
    have budget : elements.horizon + 1 + slack = (elements.horizon + slack) + 1 := by omega
    rw [budget,Source.loadMem,Source.Hoare.run_bind,execution]
    rfl
  exact ⟨data,loaded,storageCopyCertificate frame _ _ rfl path input loaded data load,frontier⟩

def SourceStoredValue.dynamicArray {E : Source.Env} {Γ : Source.RCtx} {frame : Source.Fr}
    {path : Source.SPath} {before : Source.EMState E Γ} {element : Source.STy} {count : Nat}
    (elements : SourceStoredElements frame path before 0 element count)
    (range : Source.IntTy.u256.lo ≤ (count : Int) ∧ (count : Int) ≤ Source.IntTy.u256.hi)
    (length : PersistentSourceCell frame path before (Source.Val.int count range)) :
    SourceStoredValue frame path before (.array .memory element none) where
  horizon := elements.horizon + 2
  objects := elements.objects + 1
  horizon_positive := by omega
  execution := by
    intro input extension slack
    obtain ⟨data,loaded,copy,frontier⟩ := elements.dynamicCopy range length input extension slack
    refine ⟨.memRef rfl loaded.2.heap.next,allocatedState data loaded,?_,copy.allocates,?_⟩
    · have budget : elements.horizon + 1 + slack + 1 = elements.horizon + 2 + slack := by omega
      simpa only [budget] using copy.execution
    · change loaded.2.heap.next + 1 = input.2.heap.next + (elements.objects + 1)
      rw [frontier]
      omega

def SourceStoredValue.fixedArray {E : Source.Env} {Γ : Source.RCtx} {frame : Source.Fr}
    {path : Source.SPath} {before : Source.EMState E Γ} {element : Source.STy} {count : Nat}
    (elements : SourceStoredElements frame path before 0 element count) :
    SourceStoredValue frame path before (.array .memory element (some count)) where
  horizon := elements.horizon + 2
  objects := elements.objects + 1
  horizon_positive := by omega
  execution := by
    intro input extension slack
    obtain ⟨data,loaded,copy,frontier⟩ := elements.fixedCopy input extension slack
    refine ⟨.memRef rfl loaded.2.heap.next,allocatedState data loaded,?_,copy.allocates,?_⟩
    · have budget : elements.horizon + 1 + slack + 1 = elements.horizon + 2 + slack := by omega
      simpa only [budget] using copy.execution
    · change loaded.2.heap.next + 1 = input.2.heap.next + (elements.objects + 1)
      rw [frontier]
      omega

theorem storedDynamicArray {E : Source.Env} {Γ : Source.RCtx} {frame : Source.Fr}
    {path : Source.SPath} {before : Source.EMState E Γ} {element : Source.STy} {count : Nat}
    (elements : SourceStoredElements frame path before 0 element count)
    (range : Source.IntTy.u256.lo ≤ (count : Int) ∧ (count : Int) ≤ Source.IntTy.u256.hi)
    (length : PersistentSourceCell frame path before (Source.Val.int count range)) :
    SourceStoredDynamicArray elements := ⟨.dynamicArray elements range length,rfl,rfl⟩

theorem storedFixedArray {E : Source.Env} {Γ : Source.RCtx} {frame : Source.Fr}
    {path : Source.SPath} {before : Source.EMState E Γ} {element : Source.STy} {count : Nat}
    (elements : SourceStoredElements frame path before 0 element count) :
    SourceStoredFixedArray elements := ⟨.fixedArray elements,rfl,rfl⟩

#print axioms SourceStoredElements.nil
#print axioms SourceStoredElements.cons
#print axioms SourceStoredElements.dynamicCopy
#print axioms SourceStoredElements.fixedCopy
#print axioms SourceStoredValue.dynamicArray
#print axioms SourceStoredValue.fixedArray
#print axioms storedDynamicArray
#print axioms storedFixedArray
end Solidity.Backend.MemoryCopies
