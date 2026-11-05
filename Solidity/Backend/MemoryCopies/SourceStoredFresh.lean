import Solidity.Backend.MemoryCopies.SourceStoredFreshInterface
import Solidity.Backend.MemoryCopies.SourceCopyHorizon

/-! Derive fresh parent-last copies from actual loadElem success, then compose
repeated copies over unchanged persistent storage. No evaluator is added. -/
namespace Solidity.Backend.MemoryCopies
variable {E : Source.Env} {Γ : Source.RCtx}

theorem sourceReferenceCopy_of_success (frame : Source.Fr) (fuel : Nat) (type : Source.STy)
    (memory : type.loc? = some .memory) (path : Source.SPath) (before after : Source.EMState E Γ)
    (value : Source.Val E.layout type)
    (execution : (Source.loadElem (E := E) (Γ := Γ) frame fuel type path).run before = (.ok value,after)) :
    ∃ (data : Source.Data E.layout type) (loaded : Source.EMState E Γ) (root : Nat),
      SourceStorageCopyCertificate frame (fuel - 1) type memory path before loaded after root data ∧
      value = .memRef memory root ∧ root + 1 = after.2.heap.next := by
  cases fuel with
  | zero =>
    change ((.error .timeout : Source.R (Source.Val E.layout type)),before) = (.ok value,after) at execution
    cases execution
  | succ fuel =>
    simp only [Source.loadElem,Source.STy.byRef,memory,Option.isSome_some,if_true] at execution
    rw [Source.Hoare.run_bind] at execution
    rcases load : (Source.loadMem (E := E) (Γ := Γ) frame fuel type path).run before with ⟨result,loaded⟩
    rw [load] at execution
    cases result with
    | error halt => cases execution
    | ok data =>
      dsimp only at execution
      rw [allocRef_run data memory loaded] at execution
      have reached : allocatedState data loaded = after := congrArg Prod.snd execution
      have returned : Source.Val.memRef memory loaded.2.heap.next = value :=
        Except.ok.inj (congrArg Prod.fst execution)
      subst after
      refine ⟨data,loaded,loaded.2.heap.next,?_,returned.symm,rfl⟩
      have budget : fuel + 1 - 1 = fuel := by omega
      simpa only [budget] using storageCopyCertificate frame fuel type memory path before loaded data load

theorem SourceStoredValue.copy_result {frame : Source.Fr} {path : Source.SPath}
    {before : Source.EMState E Γ} {type : Source.STy} (stored : SourceStoredValue frame path before type)
    (memory : type.loc? = some .memory) (input : Source.EMState E Γ) (extension : AllocationExtension before input)
    (slack : Nat) :
    ∃ (data : Source.Data E.layout type) (loaded after : Source.EMState E Γ) (root : Nat),
      SourceStorageCopyCertificate frame (stored.horizon + slack - 1) type memory path input loaded after root data ∧
      after.2.heap.next = input.2.heap.next + stored.objects ∧ root + 1 = after.2.heap.next := by
  obtain ⟨value,after,execution,_,count⟩ := stored.execution input extension slack
  obtain ⟨data,loaded,root,copy,_,last⟩ := sourceReferenceCopy_of_success frame _ type memory path input after value execution
  exact ⟨data,loaded,after,root,copy,count,last⟩

def SourceStoredValue.fresh {frame : Source.Fr} {path : Source.SPath} {before : Source.EMState E Γ}
    {type : Source.STy} (stored : SourceStoredValue frame path before type) (memory : type.loc? = some .memory) :
    SourceStoredReferenceCertificate stored memory where
  positive := by
    obtain ⟨data,loaded,after,root,copy,count,last⟩ := stored.copy_result memory before (AllocationExtension.refl before) 0
    have new : before.2.heap.next ≤ root := copy.fresh
    omega
  copy := stored.copy_result memory

theorem SourceStoredValue.copy_twice {frame : Source.Fr} {path : Source.SPath} {before : Source.EMState E Γ}
    {type : Source.STy} (stored : SourceStoredValue frame path before type) (memory : type.loc? = some .memory)
    (input : Source.EMState E Γ) (extension : AllocationExtension before input) (slack : Nat) :
    SourceStoredDoubleCopy stored memory input slack := by
  obtain ⟨firstData,firstLoaded,firstAfter,firstRoot,firstCopy,firstCount,firstLast⟩ :=
    (stored.fresh memory).copy input extension slack
  obtain ⟨secondData,secondLoaded,secondAfter,secondRoot,secondCopy,secondCount,secondLast⟩ :=
    (stored.fresh memory).copy firstAfter (extension.trans firstCopy.allocates) slack
  have budget : stored.horizon + slack - 1 + 1 = stored.horizon + slack := by
    have positive : 0 < stored.horizon := stored.horizon_positive
    omega
  have firstRun : (Source.loadElem (E := E) (Γ := Γ) frame (stored.horizon + slack) type path).run input =
      (.ok (.memRef memory firstRoot),firstAfter) := by simpa only [budget] using firstCopy.execution
  have secondRun : (Source.loadElem (E := E) (Γ := Γ) frame (stored.horizon + slack) type path).run firstAfter =
      (.ok (.memRef memory secondRoot),secondAfter) := by simpa only [budget] using secondCopy.execution
  refine ⟨firstData,secondData,firstLoaded,firstAfter,secondLoaded,secondAfter,firstRoot,secondRoot,
    firstCopy,secondCopy,?_,firstCount,?_,firstLast,secondLast,?_,?_⟩
  · rw [Source.Hoare.run_bind,firstRun]
    dsimp only
    rw [Source.Hoare.run_bind,secondRun]
    rfl
  · rw [secondCount,firstCount]
    omega
  · have later : firstAfter.2.heap.next ≤ secondRoot := secondCopy.fresh
    omega
  · exact (secondCopy.old firstRoot (by omega)).trans firstCopy.object

theorem SourceStoredValue.second_timeout {frame : Source.Fr} {path : Source.SPath} {before : Source.EMState E Γ}
    {type : Source.STy} (stored : SourceStoredValue frame path before type) (memory : type.loc? = some .memory)
    (input : Source.EMState E Γ) (extension : AllocationExtension before input) (slack : Nat) :
    ∃ (data : Source.Data E.layout type) (loaded after : Source.EMState E Γ) (root : Nat),
      SourceStorageCopyCertificate frame (stored.horizon + slack - 1) type memory path input loaded after root data ∧
      after.2.heap.next = input.2.heap.next + stored.objects ∧
      (do
        let _ ← Source.loadElem (E := E) (Γ := Γ) frame (stored.horizon + slack) type path
        Source.loadElem frame 0 type path).run input = (.error .timeout,after) := by
  obtain ⟨data,loaded,after,root,copy,count,last⟩ := stored.copy_result memory input extension slack
  have budget : stored.horizon + slack - 1 + 1 = stored.horizon + slack := by
    have positive : 0 < stored.horizon := stored.horizon_positive
    omega
  have firstRun : (Source.loadElem (E := E) (Γ := Γ) frame (stored.horizon + slack) type path).run input =
      (.ok (.memRef memory root),after) := by simpa only [budget] using copy.execution
  refine ⟨data,loaded,after,root,copy,count,?_⟩
  rw [Source.Hoare.run_bind,firstRun]
  rfl

theorem SourceStoredValue.horizon_exact {frame : Source.Fr} {path : Source.SPath} {before : Source.EMState E Γ}
    {type : Source.STy} (stored : SourceStoredValue frame path before type)
    (input : Source.EMState E Γ) (extension : AllocationExtension before input) (slack : Nat) :
    (Source.loadElem (E := E) (Γ := Γ) frame (stored.horizon + slack) type path).run input =
      (Source.loadElem frame stored.horizon type path).run input := by
  obtain ⟨value,after,run,_,_⟩ := stored.execution input extension 0
  have execution : (Source.loadElem (E := E) (Γ := Γ) frame stored.horizon type path).run input = (.ok value,after) := by
    simpa only [Nat.add_zero] using run
  exact ((loadElem_horizon frame stored.horizon slack type path).success input after value execution).trans execution.symm

theorem SourceStoredFields.horizon_exact {frame : Source.Fr} {path : Source.SPath} {before : Source.EMState E Γ}
    {start : Nat} {types : List Source.STy} (stored : SourceStoredFields frame path before start types)
    (input : Source.EMState E Γ) (extension : AllocationExtension before input) (slack : Nat) :
    (Source.loadFields (E := E) (Γ := Γ) frame (stored.horizon + slack) types path start).run input =
      (Source.loadFields frame stored.horizon types path start).run input := by
  obtain ⟨values,after,run,_,_⟩ := stored.execution input extension 0
  have execution : (Source.loadFields (E := E) (Γ := Γ) frame stored.horizon types path start).run input = (.ok values,after) := by
    simpa only [Nat.add_zero] using run
  exact ((loadFields_horizon frame stored.horizon slack types path start).success input after values execution).trans execution.symm

theorem SourceStoredElements.horizon_exact {frame : Source.Fr} {path : Source.SPath} {before : Source.EMState E Γ}
    {start count : Nat} {type : Source.STy} (stored : SourceStoredElements frame path before start type count)
    (input : Source.EMState E Γ) (extension : AllocationExtension before input) (slack : Nat) :
    (Source.loadElems (E := E) (Γ := Γ) frame (stored.horizon + slack) type path start count).run input =
      (Source.loadElems frame stored.horizon type path start count).run input := by
  obtain ⟨values,after,run,_,_⟩ := stored.execution input extension 0
  have execution : (Source.loadElems (E := E) (Γ := Γ) frame stored.horizon type path start count).run input = (.ok values,after) := by
    simpa only [Nat.add_zero] using run
  exact ((loadElems_horizon frame stored.horizon slack type path start count).success input after values execution).trans execution.symm

#print axioms sourceReferenceCopy_of_success
#print axioms SourceStoredValue.copy_result
#print axioms SourceStoredValue.fresh
#print axioms SourceStoredValue.copy_twice
#print axioms SourceStoredValue.second_timeout
#print axioms SourceStoredValue.horizon_exact
#print axioms SourceStoredFields.horizon_exact
#print axioms SourceStoredElements.horizon_exact
end Solidity.Backend.MemoryCopies
