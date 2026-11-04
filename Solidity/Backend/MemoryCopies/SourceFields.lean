import Solidity.Backend.MemoryCopies.SourceFieldsInterface
import Solidity.Backend.MemoryCopies.SourceConstruction

/-! Existing Source field traversal and struct parent construction composed. -/
namespace Solidity.Backend.MemoryCopies

def SourceValueConstruction.pureDefault {E : Source.Env} {τ : Source.STy}
    (value : Source.Val E.layout τ) (default : Source.Val.default E.layout τ = some value) :
    SourceValueConstruction E τ where
  horizon := 1
  objects := 0
  horizon_positive := by decide
  execution := by
    intro Γ before slack
    refine ⟨value,before,?_,AllocationExtension.refl before,rfl⟩
    have budget : 1 + slack = slack + 1 := by omega
    rw [budget,Source.zeroVal,default]
    rfl

def SourceConstructionCertificate.value {E : Source.Env} {τ : Source.STy}
    {memory : τ.loc? = some .memory} (child : SourceConstructionCertificate E τ memory) :
    SourceValueConstruction E τ where
  horizon := child.horizon
  objects := child.objects
  horizon_positive := child.horizon_positive
  execution := by
    intro Γ before slack
    obtain ⟨after,root,data,certificate,count,_⟩ := child.execution before slack
    exact ⟨.memRef memory root,after,certificate.execution,
      ⟨certificate.frame,certificate.growth,certificate.old⟩,count⟩

def SourceFieldsConstruction.nil (E : Source.Env) : SourceFieldsConstruction E [] where
  horizon := 1
  objects := 0
  horizon_positive := by decide
  execution := by
    intro Γ before slack
    refine ⟨.nil,before,?_,AllocationExtension.refl before,rfl⟩
    have budget : 1 + slack = slack + 1 := by omega
    rw [budget,Source.zeroFields]
    · rfl
    · omega

def SourceFieldsConstruction.cons {E : Source.Env} {τ : Source.STy} {types : List Source.STy}
    (head : SourceValueConstruction E τ) (tail : SourceFieldsConstruction E types) :
    SourceFieldsConstruction E (τ :: types) where
  horizon := head.horizon + tail.horizon + 1
  objects := head.objects + tail.objects
  horizon_positive := by omega
  execution := by
    intro Γ before slack
    obtain ⟨value,middle,first,firstFrame,firstCount⟩ := head.execution before (tail.horizon + slack)
    obtain ⟨data,after,rest,restFrame,restCount⟩ := tail.execution middle (head.horizon + slack)
    have firstRun :
        (Source.zeroVal (E := E) (Γ := Γ) (head.horizon + tail.horizon + slack) τ).run before =
          (.ok value,middle) := by
      simpa only [Nat.add_assoc] using first
    have restRun :
        (Source.zeroFields (E := E) (Γ := Γ) (head.horizon + tail.horizon + slack) types).run middle =
          (.ok data,after) := by
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using rest
    refine ⟨.cons (.val value) data,after,?_,firstFrame.trans restFrame,?_⟩
    · have budget : head.horizon + tail.horizon + 1 + slack = (head.horizon + tail.horizon + slack) + 1 := by omega
      rw [budget,Source.zeroFields,Source.Hoare.run_bind,firstRun]
      dsimp only
      rw [Source.Hoare.run_bind,restRun]
      rfl
    · rw [restCount,firstCount]
      omega

/-- The field certificate is indexed by the actual existing environment
layout, so no separate desired field list or final Source run is assumed. -/
def SourceFieldsConstruction.structDefault {E : Source.Env} (name : Source.DeclName)
    (fields : SourceFieldsConstruction E (E.layout.fields name)) :
    SourceConstructionCertificate E (.struct .memory name) rfl where
  horizon := fields.horizon + 2
  objects := fields.objects + 1
  horizon_positive := by omega
  objects_positive := by omega
  execution := by
    intro Γ before slack
    obtain ⟨values,middle,fieldRun,preserved,counted⟩ := fields.execution before slack
    let data : Source.Data E.layout (.struct .memory name) := .struct values
    have execution :
        (Source.zeroVal (E := E) (Γ := Γ) (fields.horizon + 2 + slack) (.struct .memory name)).run before =
          (.ok (.memRef rfl middle.2.heap.next),allocatedState data middle) := by
      have budget : fields.horizon + 2 + slack = (fields.horizon + slack) + 1 + 1 := by omega
      rw [budget,Source.zeroVal]
      simp only [Source.Val.default,Source.Val.defaultElem,Source.STy.loc?,if_true]
      rw [Source.Hoare.run_bind,Source.zeroData,Source.Hoare.run_bind,fieldRun]
      dsimp only
      exact allocRef_run data rfl middle
    have frame : AllocationExtension before (allocatedState data middle) := by
      have derived : AllocationExtension before
          ((Source.zeroVal (E := E) (Γ := Γ) (fields.horizon + 2 + slack) (.struct .memory name)).run before).2 :=
        zeroVal_allocates _ _ before
      rw [execution] at derived
      exact derived
    refine ⟨allocatedState data middle,middle.2.heap.next,data,
      ⟨execution,frame.frame,frame.growth,preserved.growth,Source.Heap.alloc_get _ _,frame.old⟩,?_,rfl⟩
    change middle.2.heap.next + 1 = before.2.heap.next + (fields.objects + 1)
    rw [counted]
    omega

#print axioms SourceValueConstruction.pureDefault
#print axioms SourceConstructionCertificate.value
#print axioms SourceFieldsConstruction.nil
#print axioms SourceFieldsConstruction.cons
#print axioms SourceFieldsConstruction.structDefault
end Solidity.Backend.MemoryCopies
