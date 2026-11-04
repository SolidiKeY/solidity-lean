import Solidity.Backend.MemoryCopies.SourceStoredFresh
import Solidity.Backend.MemoryCopies.SourceStoredElements

/-! Repeated deep storage copies retain first payloads and allocate distinct roots. -/
namespace Solidity.Backend.MemoryCopies.SourceStoredFreshControls
private inductive Mode where | empty | populated | long
private def declaration : Source.Decl :=
  ⟨.struct,"Envelope",none,true,.struct "Envelope"
    (.structMember (.array (.elem .bytes) .none) "chunks")
    (.cons (.structMember (.elem .bytes) "tail") .nil)⟩
private def rootDecl : Source.Decl :=
  ⟨.stateVar,"root",none,true,.stateVar (.userType ⟨"Envelope",[]⟩) none none none false "root" .none⟩
private def E : Source.Env := ⟨[declaration,rootDecl]⟩
private def name : Source.DeclName := ⟨none,"Envelope"⟩
private def path : Source.SPath := ⟨⟨none,"root"⟩,[]⟩
private def chunksPath : Source.SPath := path.go (.field 0)
private abbrev T : Source.STy := .struct .memory name
private def children : Mode → List (List UInt8)
  | .empty => []
  | .populated => [[17,23],[]]
  | .long => List.replicate 64 []
private theorem range (mode : Mode) : Source.IntTy.u256.lo ≤ ((children mode).length : Int) ∧
    ((children mode).length : Int) ≤ Source.IntTy.u256.hi := by cases mode <;> decide
private def frame : Source.Fr :=
  {this := ⟨1,by decide⟩,sender := ⟨2,by decide⟩,value := ⟨0,by decide⟩,static := false,contract := "C"}
private def storage (mode : Mode) : Source.Storage E.layout E.cellTy :=
  let initial := Source.Storage.empty.write chunksPath (.int (children mode).length (range mode))
  match mode with
  | .populated =>
    ((initial.write (chunksPath.go (.index 0)) (.int 2 (by decide))).write
      ((chunksPath.go (.index 0)).go (.index 0)) (.fixedBytes [17] rfl)).write
      ((chunksPath.go (.index 0)).go (.index 1)) (.fixedBytes [23] rfl)
  | _ => initial
private def before (mode : Mode) : Source.EMState E [.bool] :=
  (.cons (.bool true) .nil,
    {ex := ⟨⟨fun _ => ⟨⟨17,by decide⟩,3,some 9,storage mode⟩⟩,Source.Transient.empty,[]⟩,
     heap := (Source.Heap.empty.alloc ⟨.bool,.val (.bool true)⟩).1,events := [],
     logs := [(⟨13,by decide⟩,[1,2])],fnLocals := ⟨[.bool],.cons (.bool false) .nil⟩})
private def inputs (mode : Mode) : SourceByteChildren frame chunksPath (before mode) 0 (children mode) := by
  cases mode with
  | empty => intro index; exact Fin.elim0 index
  | populated =>
    intro index
    rcases index with ⟨index,bound⟩
    cases index with
    | zero =>
      change StoredSourceBytes frame (chunksPath.go (.index 0)) (before .populated) [17,23]
      refine ⟨by decide,⟨rfl,rfl,rfl⟩,?_⟩
      intro byte
      rcases byte with ⟨byte,bound⟩
      cases byte with
      | zero => exact ⟨rfl,rfl,rfl⟩
      | succ byte => cases byte with
        | zero => exact ⟨rfl,rfl,rfl⟩
        | succ byte => change byte + 2 < 2 at bound; omega
    | succ index => cases index with
      | zero =>
        change StoredSourceBytes frame (chunksPath.go (.index 1)) (before .populated) []
        exact ⟨by decide,⟨rfl,rfl,rfl⟩,(fun byte => Fin.elim0 byte)⟩
      | succ index => change index + 2 < 2 at bound; omega
  | long =>
    intro index
    have empty : (children .long)[index] = [] := by
      change (List.replicate 64 ([] : List UInt8))[index.val]'(by exact index.isLt) = []
      exact List.getElem_replicate _
    rw [empty]
    exact ⟨by decide,⟨rfl,rfl,rfl⟩,(fun byte => Fin.elim0 byte)⟩
private def lengthInput (mode : Mode) : PersistentSourceCell frame chunksPath (before mode)
    (Source.Val.int (children mode).length (range mode)) := by
  cases mode <;> exact ⟨rfl,rfl,rfl⟩
private def tailInput (mode : Mode) : StoredSourceBytes frame (path.go (.field 1)) (before mode) [] := by
  cases mode <;> exact ⟨by decide,⟨rfl,rfl,rfl⟩,(fun byte => Fin.elim0 byte)⟩
private def fields (mode : Mode) : SourceStoredFields frame path (before mode) 0 (E.layout.fields name) :=
  .cons (.byteArray (children mode) (range mode) (lengthInput mode) (inputs mode))
    (.cons (.bytes (tailInput mode)) (.nil frame path (before mode) 2))
private def copied (mode : Mode) : SourceStoredValue frame path (before mode) T := .structValue name (fields mode)
private def elements : SourceStoredElements frame chunksPath (before .populated) 0 (.bytes .memory) 2 :=
  .cons (.bytes (inputs .populated ⟨0,by decide⟩))
    (.cons (.bytes (inputs .populated ⟨1,by decide⟩)) (.nil frame chunksPath (before .populated) 2 (.bytes .memory)))
private def twice (mode : Mode) : Source.EM E [.bool] (Source.Val E.layout T × Source.Val E.layout T) := do
  let first ← Source.loadElem frame (copied mode).horizon T path
  let second ← Source.loadElem frame (copied mode).horizon T path
  pure (first,second)
private def observe
    (result : Source.R (Source.Val E.layout T × Source.Val E.layout T) × Source.EMState E [.bool]) : Option (Nat × Nat × Nat) :=
  match result.1 with
  | .ok (.memRef _ first,.memRef _ second) => some (first,second,result.2.2.heap.next)
  | _ => none
private def byteContent (heap : Source.Heap E.layout) (root : Nat) : Option (List UInt8) :=
  match heap.get root with
  | some ⟨.bytes .memory,.bytes bytes⟩ => some bytes
  | _ => none
private def dataRoot {type : Source.STy} (result : Source.R (Source.Data E.layout type)) : Option Nat :=
  match result with
  | .ok (.val (.memRef _ root)) => some root
  | _ => none
private def arrayRefs (heap : Source.Heap E.layout) (root : Nat) : Option (List (Option Nat)) :=
  match heap.get root with
  | some ⟨.array .memory (.bytes .memory) none,.array count _ values⟩ =>
      some ((List.finRange count).map (fun index => match values index with | .val (.memRef _ child) => some child | _ => none))
  | _ => none
private def structRefs (heap : Source.Heap E.layout) (root : Nat) : Option (Option Nat × Option Nat) :=
  match heap.get root with
  | some ⟨.struct .memory decl,.struct values⟩ =>
      if decl = name then some (dataRoot (values.nth 0 (.array .memory (.bytes .memory) none)),dataRoot (values.nth 1 (.bytes .memory))) else none
  | _ => none
private def arrayLength (heap : Source.Heap E.layout) (root : Nat) : Option Nat :=
  match heap.get root with
  | some ⟨.array .memory (.bytes .memory) none,.array count _ _⟩ => some count
  | _ => none

theorem declared : E.pathTy path = some (.struct .storage name) ∧ E.layout.fields name =
    [.array .memory (.bytes .memory) none,.bytes .memory] := ⟨rfl,rfl⟩

theorem reference_inhabited (mode : Mode) : SourceStoredReferenceCertificate (copied mode) rfl := (copied mode).fresh rfl

theorem actual_twice (mode : Mode) : SourceStoredDoubleCopy (copied mode) rfl (before mode) 0 :=
  (copied mode).copy_twice rfl (before mode) (AllocationExtension.refl (before mode)) 0

theorem pair_observation (mode : Mode) : observe ((twice mode).run (before mode)) =
    some ((copied mode).objects,2 * (copied mode).objects,1 + 2 * (copied mode).objects) := by
  obtain ⟨firstData,secondData,firstLoaded,firstAfter,secondLoaded,secondAfter,firstRoot,secondRoot,
    firstCopy,secondCopy,execution,firstCount,secondCount,firstLast,secondLast,_,_⟩ := actual_twice mode
  have run : (twice mode).run (before mode) = (.ok (.memRef rfl firstRoot,.memRef rfl secondRoot),secondAfter) := by
    simpa only [Nat.add_zero] using execution
  rw [run]
  change some (firstRoot,secondRoot,secondAfter.2.heap.next) = _
  change firstAfter.2.heap.next = 1 + (copied mode).objects at firstCount
  change secondAfter.2.heap.next = 1 + 2 * (copied mode).objects at secondCount
  have first : firstRoot = (copied mode).objects := by omega
  have second : secondRoot = 2 * (copied mode).objects := by omega
  rw [first,second,secondCount]

theorem populated_pair : observe ((twice .populated).run (before .populated)) = some (5,10,11) := by
  have count : (copied .populated).objects = 5 := by decide +kernel
  simpa only [count] using pair_observation .populated

theorem empty_pair : observe ((twice .empty).run (before .empty)) = some (3,6,7) := by
  have count : (copied .empty).objects = 3 := by decide +kernel
  simpa only [count] using pair_observation .empty

theorem long_pair : observe ((twice .long).run (before .long)) = some (67,134,135) := by
  have count : (copied .long).objects = 67 := by decide +kernel
  simpa only [count] using pair_observation .long

theorem retained_payloads :
    let heap := ((twice .populated).run (before .populated)).2.2.heap
    byteContent heap 1 = some [17,23] ∧ byteContent heap 2 = some [] ∧
      byteContent heap 6 = some [17,23] ∧ byteContent heap 7 = some [] ∧
      arrayRefs heap 3 = some [some 1,some 2] ∧ arrayRefs heap 8 = some [some 6,some 7] ∧
      structRefs heap 5 = some (some 3,some 4) ∧ structRefs heap 10 = some (some 8,some 9) := by decide +kernel

theorem long_lengths :
    let heap := ((twice .long).run (before .long)).2.2.heap
    arrayLength heap 65 = some 64 ∧ arrayLength heap 132 = some 64 := by decide +kernel

theorem value_horizon (mode : Mode) (slack : Nat) :
    (Source.loadElem (E := E) (Γ := [.bool]) frame ((copied mode).horizon + slack) T path).run (before mode) =
      (Source.loadElem frame (copied mode).horizon T path).run (before mode) :=
  (copied mode).horizon_exact (before mode) (AllocationExtension.refl (before mode)) slack

theorem fields_horizon (mode : Mode) (slack : Nat) :
    (Source.loadFields (E := E) (Γ := [.bool]) frame ((fields mode).horizon + slack) (E.layout.fields name) path 0).run (before mode) =
      (Source.loadFields frame (fields mode).horizon (E.layout.fields name) path 0).run (before mode) :=
  (fields mode).horizon_exact (before mode) (AllocationExtension.refl (before mode)) slack

theorem elements_horizon (slack : Nat) :
    (Source.loadElems (E := E) (Γ := [.bool]) frame (elements.horizon + slack) (.bytes .memory) chunksPath 0 2).run (before .populated) =
      (Source.loadElems frame elements.horizon (.bytes .memory) chunksPath 0 2).run (before .populated) :=
  elements.horizon_exact (before .populated) (AllocationExtension.refl (before .populated)) slack

theorem second_timeout_keeps_first (mode : Mode) :
    ∃ (data : Source.Data E.layout T) (loaded after : Source.EMState E [.bool]) (root : Nat),
      SourceStorageCopyCertificate frame ((copied mode).horizon + 0 - 1) T rfl path (before mode) loaded after root data ∧
      after.2.heap.next = 1 + (copied mode).objects ∧
      (do
        let _ ← Source.loadElem (E := E) (Γ := [.bool]) frame ((copied mode).horizon + 0) T path
        Source.loadElem frame 0 T path).run (before mode) = (.error .timeout,after) ∧
      after.2.heap.get root = some ⟨T,data⟩ := by
  obtain ⟨data,loaded,after,root,copy,count,run⟩ :=
    (copied mode).second_timeout rfl (before mode) (AllocationExtension.refl (before mode)) 0
  exact ⟨data,loaded,after,root,copy,count,run,copy.object⟩

theorem wrong_shared_root_rejected : observe ((twice .populated).run (before .populated)) ≠ some (5,5,11) := by
  rw [populated_pair]
  decide

theorem old_and_nonheap :
    let first := (Source.loadElem (E := E) (Γ := [.bool]) frame (copied .populated).horizon T path).run (before .populated)
    let second := (Source.loadElem (E := E) (Γ := [.bool]) frame (copied .populated).horizon T path).run first.2
    second.2.2.heap.get 0 = (before .populated).2.heap.get 0 ∧
      second.2 = ((before .populated).1,{(before .populated).2 with heap := second.2.2.heap}) := by
  have firstFrame : AllocationExtension (before .populated)
      ((Source.loadElem (E := E) (Γ := [.bool]) frame (copied .populated).horizon T path).run (before .populated)).2 :=
    loadElem_allocates frame _ T path (before .populated)
  have secondFrame : AllocationExtension
      ((Source.loadElem (E := E) (Γ := [.bool]) frame (copied .populated).horizon T path).run (before .populated)).2
      ((Source.loadElem (E := E) (Γ := [.bool]) frame (copied .populated).horizon T path).run
        ((Source.loadElem (E := E) (Γ := [.bool]) frame (copied .populated).horizon T path).run (before .populated)).2).2 :=
    loadElem_allocates frame _ T path _
  exact ⟨(firstFrame.trans secondFrame).old 0 (by change 0 < 1; decide),(firstFrame.trans secondFrame).frame⟩

#print axioms declared
#print axioms reference_inhabited
#print axioms actual_twice
#print axioms pair_observation
#print axioms populated_pair
#print axioms empty_pair
#print axioms long_pair
#print axioms retained_payloads
#print axioms long_lengths
#print axioms value_horizon
#print axioms fields_horizon
#print axioms elements_horizon
#print axioms second_timeout_keeps_first
#print axioms wrong_shared_root_rejected
#print axioms old_and_nonheap
end Solidity.Backend.MemoryCopies.SourceStoredFreshControls
