import Solidity.Backend.MemoryCopies.CopyPathInterface
import Solidity.Backend.MemoryCopies.HeapContents

/-! A read-only fold of existing typed Path through Heap.field/index. This is
an intrinsic copy observer, not a Source path resolver or emitted-code selector. -/
namespace Solidity.Backend.MemoryCopies

noncomputable def copyPathObserver : CopyPathObserver := fun {H} heap {T U} path =>
  @Path.rec (fun T U _ => MVal H T → Option (MVal H U))
    (fun {_T} value => some value)
    (fun {_s _f _T _U} proof _path previous reference => previous (heap.field reference proof))
    (fun {_E _U} index _path previous reference => (heap.index reference .dyn index).bind previous)
    (fun {_E _U _n} index _path previous reference => (heap.index reference .fixed index).bind previous)
    (fun {_K _V _U} _key _path _previous reference => (heap.get reference : Empty).elim)
    T U path

def CopyPathMirrors {H : HTy} {T : Ty} (heap : Heap H) (frontier : Nat)
    (stored : Option (SVal T)) (observed : Option (MVal H T)) : Prop :=
  match stored,observed with
  | none,none => True
  | some value,some memory => value.Mirrors heap frontier memory
  | _,_ => False

theorem mirror_path {H : HTy} (heap : Heap H) (frontier : Nat) :
    {T U : Ty} → (path : Path T U) → (value : SVal T) → (reference : MVal H T) →
    value.Mirrors heap frontier reference →
    CopyPathMirrors heap frontier (value.findLiveM path) (copyPathObserver heap path reference)
  | _, _, .nil, value, reference, mirrored => by cases value <;> exact mirrored
  | _, _, .field proof path, .struct fields, reference, mirrored => by
    change CopyPathMirrors heap frontier ((fields.get proof).findLiveM path)
      (copyPathObserver heap path (heap.field reference proof))
    exact mirror_path heap frontier path (fields.get proof) _
      (SFields.Mirrors.get fields (heap.get reference) mirrored.2 proof)
  | _, _, .at index path, .array values shadow bound, reference, mirrored => by
    change CopyPathMirrors heap frontier
      (match values.toList[index.1.toNat]? with | some value => value.findLiveM path | none => none)
      ((heap.index reference .dyn index).bind (copyPathObserver heap path))
    unfold Heap.index
    rcases SVec.Mirrors.getElem values _ mirrored.2 index.1.toNat with absent | present
    · rw [absent.1,absent.2]
      trivial
    · obtain ⟨value,memory,stored,observed,child⟩ := present
      rw [stored,observed]
      exact mirror_path heap frontier path value memory child
  | _, _, .atF index path, .fixed values, reference, mirrored => by
    change CopyPathMirrors heap frontier
      (match values.toList[index.1.toNat]? with | some value => value.findLiveM path | none => none)
      ((heap.index reference .fixed index).bind (copyPathObserver heap path))
    unfold Heap.index
    rcases SVec.Mirrors.getElem values _ mirrored.2 index.1.toNat with absent | present
    · rw [absent.1,absent.2]
      trivial
    · obtain ⟨value,memory,stored,observed,child⟩ := present
      rw [stored,observed]
      exact mirror_path heap frontier path value memory child
  | _, _, .key key path, .map entries default, reference, mirrored => False.elim mirrored

theorem CopyPathMirrors.contents {H : HTy} {T : Ty} {heap : Heap H} {frontier : Nat}
    {stored : Option (SVal T)} {observed : Option (MVal H T)}
    (mirrored : CopyPathMirrors heap frontier stored observed) :
    observed.map (MVal.copyMToSt heap) = stored.map SVal.strip := by
  cases stored with
  | none => cases observed with
    | none => rfl
    | some memory => cases mirrored
  | some value => cases observed with
    | none => cases mirrored
    | some memory => exact congrArg some (mirror_contents heap value memory frontier mirrored)

theorem copy_path_contents {H : HTy} {T U : Ty} (heap : Heap H) (value : SVal T)
    (memory : T.mapFree = true) (path : Path T U) :
    let grown := value.copyStToM heap memory
    (copyPathObserver grown.heap path grown.val).map (MVal.copyMToSt grown.heap) =
      (value.findLiveM path).map SVal.strip :=
  (mirror_path _ H.length path value _ (SVal.mirrors_copyStToM heap value memory)).contents

theorem copy_path_bounds {H : HTy} {T : Ty} {R : RefTy} (heap : Heap H) (value : SVal T)
    (memory : T.mapFree = true) (path : Path T (.ref R))
    (reference : HRef (value.copyStToM heap memory).H' R)
    (observed : copyPathObserver (value.copyStToM heap memory).heap path (value.copyStToM heap memory).val = some reference) :
    H.length ≤ reference.id ∧ reference.id < H.length + liveObjectCount value := by
  let grown := value.copyStToM heap memory
  have mirrored : CopyPathMirrors grown.heap H.length (value.findLiveM path) (copyPathObserver grown.heap path grown.val) :=
    mirror_path _ H.length path value _ (SVal.mirrors_copyStToM heap value memory)
  rw [observed] at mirrored
  cases found : value.findLiveM path with
  | none => rw [found] at mirrored; cases mirrored
  | some child =>
    have childMirror : child.Mirrors grown.heap H.length reference := by simpa only [found,CopyPathMirrors] using mirrored
    have fresh : H.length ≤ reference.id := SVal.Mirrors.id_ge child reference childMirror
    have bound : reference.id < grown.H'.length := reference.id_lt
    have count : grown.H'.length = H.length + liveObjectCount value := valueCopy_count value memory heap
    exact ⟨fresh,by omega⟩

def copiedPaths : CopiedPathCertificate copyPathObserver := ⟨copy_path_contents,copy_path_bounds⟩

theorem copy_path_absent_iff {H : HTy} {T U : Ty} (heap : Heap H) (value : SVal T)
    (memory : T.mapFree = true) (path : Path T U) :
    copyPathObserver (value.copyStToM heap memory).heap path (value.copyStToM heap memory).val = none ↔
      value.findLiveM path = none := by
  have contents :
      (copyPathObserver (value.copyStToM heap memory).heap path (value.copyStToM heap memory).val).map
        (MVal.copyMToSt (value.copyStToM heap memory).heap) = (value.findLiveM path).map SVal.strip :=
    copy_path_contents heap value memory path
  constructor
  · intro absent
    rw [absent,Option.map_none] at contents
    cases found : value.findLiveM path with
    | none => rfl
    | some child => rw [found] at contents; cases contents
  · intro absent
    rw [absent,Option.map_none] at contents
    cases found : copyPathObserver (value.copyStToM heap memory).heap path (value.copyStToM heap memory).val with
    | none => rfl
    | some child => rw [found] at contents; cases contents

theorem copyPathObserver_keeps {H H' : HTy} (extension : H <+: H') (heap : Heap H) (after : Heap H')
    (kept : Heap.Keeps extension heap after) :
    {T U : Ty} → (path : Path T U) → (reference : MVal H T) →
    copyPathObserver after path (MVal.wk extension T reference) =
      (copyPathObserver heap path reference).map (MVal.wk extension U)
  | _, _, .nil, reference => rfl
  | _, _, .field proof path, reference => by
    change copyPathObserver after path (after.field (HRef.wk extension reference) proof) =
      (copyPathObserver heap path (heap.field reference proof)).map _
    rw [kept.field reference proof]
    exact copyPathObserver_keeps extension heap after kept path _
  | _, _, @Path.at E U index path, reference => by
    change ((after.index (HRef.wk extension reference) .dyn index).bind (copyPathObserver after path)) =
      ((heap.index reference .dyn index).bind (copyPathObserver heap path)).map _
    have read : after.index (HRef.wk extension reference) .dyn index =
        (heap.index reference .dyn index).map (MVal.wk extension E) := by
      simpa only [Heap.readAddr,MAddr.wk] using kept.readAddr (.index reference .dyn index)
    rw [read]
    cases old : heap.index reference .dyn index with
    | none => rfl
    | some value => exact copyPathObserver_keeps extension heap after kept path value
  | _, _, @Path.atF E U count index path, reference => by
    change ((after.index (HRef.wk extension reference) .fixed index).bind (copyPathObserver after path)) =
      ((heap.index reference .fixed index).bind (copyPathObserver heap path)).map _
    have read : after.index (HRef.wk extension reference) .fixed index =
        (heap.index reference .fixed index).map (MVal.wk extension E) := by
      simpa only [Heap.readAddr,MAddr.wk] using kept.readAddr (.index reference .fixed index)
    rw [read]
    cases old : heap.index reference .fixed index with
    | none => rfl
    | some value => exact copyPathObserver_keeps extension heap after kept path value
  | _, _, .key key path, reference => by cases (heap.get reference : Empty)

theorem copy_path_contents_keeps {H H' : HTy} {T U : Ty} (heap : Heap H) (value : SVal T)
    (memory : T.mapFree = true) (extension : (value.copyStToM heap memory).H' <+: H')
    (after : Heap H') (kept : Heap.Keeps extension (value.copyStToM heap memory).heap after) (path : Path T U) :
    (copyPathObserver after path (MVal.wk extension T (value.copyStToM heap memory).val)).map
      (MVal.copyMToSt after) = (value.findLiveM path).map SVal.strip := by
  have mirrored : value.Mirrors after H.length (MVal.wk extension T (value.copyStToM heap memory).val) :=
    SVal.Mirrors.wk kept value _ (SVal.mirrors_copyStToM heap value memory)
  exact (mirror_path after H.length path value _ mirrored).contents

theorem copy_paths_separated {H : HTy} {T U : Ty} {R Q : RefTy} (heap : Heap H)
    (firstValue : SVal T) (secondValue : SVal U) (firstMemory : T.mapFree = true) (secondMemory : U.mapFree = true)
    (firstPath : Path T (.ref R)) (secondPath : Path U (.ref Q)) :
    let first := firstValue.copyStToM heap firstMemory
    let second := secondValue.copyStToM first.heap secondMemory
    ∀ (left : HRef second.H' R) (right : HRef second.H' Q),
      copyPathObserver second.heap firstPath (MVal.wk second.ext T first.val) = some left →
      copyPathObserver second.heap secondPath second.val = some right → left.id < right.id := by
  dsimp only
  intro left right observedLeft observedRight
  let first := firstValue.copyStToM heap firstMemory
  let second := secondValue.copyStToM first.heap secondMemory
  have kept : Heap.Keeps second.ext first.heap second.heap := SVal.keeps_copyStToM secondValue secondMemory first.heap
  have transported : copyPathObserver second.heap firstPath (MVal.wk second.ext T first.val) =
      (copyPathObserver first.heap firstPath first.val).map (MVal.wk second.ext (.ref R)) :=
    copyPathObserver_keeps second.ext first.heap second.heap kept firstPath first.val
  rw [transported] at observedLeft
  cases old : copyPathObserver first.heap firstPath first.val with
  | none => rw [old] at observedLeft; cases observedLeft
  | some original =>
    rw [old] at observedLeft
    have identity : original.id = left.id := congrArg HRef.id (Option.some.inj observedLeft)
    have earlier : original.id < first.H'.length := original.id_lt
    have later : first.H'.length ≤ right.id := (copy_path_bounds first.heap secondValue secondMemory secondPath right observedRight).1
    omega

#print axioms mirror_path
#print axioms CopyPathMirrors.contents
#print axioms copy_path_contents
#print axioms copy_path_bounds
#print axioms copiedPaths
#print axioms copy_path_absent_iff
#print axioms copyPathObserver_keeps
#print axioms copy_path_contents_keeps
#print axioms copy_paths_separated
end Solidity.Backend.MemoryCopies
