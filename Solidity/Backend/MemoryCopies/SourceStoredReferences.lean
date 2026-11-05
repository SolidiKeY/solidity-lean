import Solidity.Backend.MemoryCopies.SourceStoredReferencesInterface

/-! Reference closure over the existing Source copy and field certificates. -/
namespace Solidity.Backend.MemoryCopies

theorem SourceStorageCopyCertificate.allocates {E : Source.Env} {Γ : Source.RCtx}
    {frame : Source.Fr} {fuel : Nat} {τ : Source.STy} {memory : τ.loc? = some .memory}
    {path : Source.SPath} {before loaded after : Source.EMState E Γ} {root : Nat} {data : Source.Data E.layout τ}
    (copy : SourceStorageCopyCertificate frame fuel τ memory path before loaded after root data) :
    AllocationExtension before after := by
  have first : AllocationExtension before loaded := ⟨copy.load.nonheap,copy.load.growth,copy.load.old⟩
  have last : AllocationExtension loaded ((Source.allocRef (E := E) (Γ := Γ) data).run loaded).2 :=
    AllocatesOnly.allocRef data loaded
  rw [copy.allocation] at last
  exact first.trans last

def SourceStoredValue.structValue {E : Source.Env} {Γ : Source.RCtx} {frame : Source.Fr}
    {path : Source.SPath} {before : Source.EMState E Γ} (name : Source.DeclName)
    (fields : SourceStoredFields frame path before 0 (E.layout.fields name)) :
    SourceStoredValue frame path before (.struct .memory name) where
  horizon := fields.horizon + 2
  objects := fields.objects + 1
  horizon_positive := by omega
  execution := by
    intro input extension slack
    obtain ⟨data,loaded,copy,count⟩ := fields.structCopy name input extension slack
    refine ⟨.memRef rfl loaded.2.heap.next,allocatedState data loaded,?_,copy.allocates,?_⟩
    · have budget : fields.horizon + 1 + slack + 1 = fields.horizon + 2 + slack := by omega
      simpa only [budget] using copy.execution
    · change loaded.2.heap.next + 1 = input.2.heap.next + (fields.objects + 1)
      rw [count]
      omega

theorem sourceEmptyArrayLoad_run {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
    (path : Source.SPath) (input : Source.EMState E Γ) (element : Source.STy) (slack : Nat)
    (length : PersistentSourceCell frame path input (Source.Val.int 0 Source.IntTy.u256.zero_mem)) :
    (Source.loadMem (E := E) (Γ := Γ) frame (2 + slack) (.array .memory element none) path).run input =
      (.ok (.array 0 (fun _ impossible => nomatch impossible) Fin.elim0),input) := by
  have sizeRead : (Source.readLen (E := E) (Γ := Γ) frame path).run input = (.ok 0,input) := by
    rw [Source.readLen,Source.Hoare.run_bind,length.read]
    rfl
  have budget : 2 + slack = (slack + 1) + 1 := by omega
  rw [budget,Source.loadMem,Source.Hoare.run_bind,sizeRead]
  rfl

def SourceStoredValue.emptyArray {E : Source.Env} {Γ : Source.RCtx} {frame : Source.Fr}
    {path : Source.SPath} {before : Source.EMState E Γ} (element : Source.STy)
    (length : PersistentSourceCell frame path before (Source.Val.int 0 Source.IntTy.u256.zero_mem)) :
    SourceStoredValue frame path before (.array .memory element none) where
  horizon := 3
  objects := 1
  horizon_positive := by decide
  execution := by
    intro input extension slack
    let data : Source.Data E.layout (.array .memory element none) :=
      .array 0 (fun _ impossible => nomatch impossible) Fin.elim0
    have load : (Source.loadMem (E := E) (Γ := Γ) frame (2 + slack) (.array .memory element none) path).run input =
        (.ok data,input) := sourceEmptyArrayLoad_run frame path input element slack (length.transport extension)
    have copy : SourceStorageCopyCertificate frame (2 + slack) (.array .memory element none) rfl path
        input input (allocatedState data input) input.2.heap.next data :=
      storageCopyCertificate frame _ _ rfl path input input data load
    refine ⟨.memRef rfl input.2.heap.next,allocatedState data input,?_,copy.allocates,rfl⟩
    have budget : 2 + slack + 1 = 3 + slack := by omega
    simpa only [budget] using copy.execution

theorem SourceByteChildren.transport {E : Source.Env} {Γ : Source.RCtx} {frame : Source.Fr}
    {path : Source.SPath} {before after : Source.EMState E Γ} {start : Nat} {children : List (List UInt8)}
    (inputs : SourceByteChildren frame path before start children) (extension : AllocationExtension before after) :
    SourceByteChildren frame path after start children := fun index => (inputs index).transport extension

def SourceStoredValue.byteArray {E : Source.Env} {Γ : Source.RCtx} {frame : Source.Fr}
    {path : Source.SPath} {before : Source.EMState E Γ} (children : List (List UInt8))
    (range : Source.IntTy.u256.lo ≤ (children.length : Int) ∧ (children.length : Int) ≤ Source.IntTy.u256.hi)
    (length : PersistentSourceCell frame path before (Source.Val.int children.length range))
    (inputs : SourceByteChildren frame path before 0 children) :
    SourceStoredValue frame path before (.array .memory (.bytes .memory) none) where
  horizon := byteChildrenHorizon children + 2
  objects := children.length + 1
  horizon_positive := by omega
  execution := by
    intro input extension slack
    obtain ⟨values,loaded,copy,count,_,_⟩ := sourceNestedBytes_copy frame path input children slack range
      (length.transport extension) (inputs.transport extension)
    refine ⟨.memRef rfl loaded.2.heap.next,_,?_,copy.allocates,?_⟩
    · have budget : byteChildrenHorizon children + 1 + slack + 1 = byteChildrenHorizon children + 2 + slack := by omega
      simpa only [budget] using copy.execution
    · change loaded.2.heap.next + 1 = input.2.heap.next + (children.length + 1)
      rw [count]
      omega

theorem storedStructValue {E : Source.Env} {Γ : Source.RCtx} {frame : Source.Fr}
    {path : Source.SPath} {before : Source.EMState E Γ} (name : Source.DeclName)
    (fields : SourceStoredFields frame path before 0 (E.layout.fields name)) : SourceStoredStructValue name fields :=
  ⟨SourceStoredValue.structValue name fields,rfl,rfl⟩

theorem storedEmptyArrayValue {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
    (path : Source.SPath) (before : Source.EMState E Γ) (element : Source.STy)
    (length : PersistentSourceCell frame path before (Source.Val.int 0 Source.IntTy.u256.zero_mem)) :
    SourceStoredEmptyArrayValue frame path before element := ⟨SourceStoredValue.emptyArray element length,rfl,rfl⟩

theorem storedByteArrayValue {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
    (path : Source.SPath) (before : Source.EMState E Γ) (children : List (List UInt8))
    (range : Source.IntTy.u256.lo ≤ (children.length : Int) ∧ (children.length : Int) ≤ Source.IntTy.u256.hi)
    (length : PersistentSourceCell frame path before (Source.Val.int children.length range))
    (inputs : SourceByteChildren frame path before 0 children) : SourceStoredByteArrayValue frame path before children :=
  ⟨SourceStoredValue.byteArray children range length inputs,rfl,rfl⟩

#print axioms SourceStorageCopyCertificate.allocates
#print axioms SourceStoredValue.structValue
#print axioms sourceEmptyArrayLoad_run
#print axioms SourceStoredValue.emptyArray
#print axioms SourceByteChildren.transport
#print axioms SourceStoredValue.byteArray
#print axioms storedStructValue
#print axioms storedEmptyArrayValue
#print axioms storedByteArrayValue
end Solidity.Backend.MemoryCopies
