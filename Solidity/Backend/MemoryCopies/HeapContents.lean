import Solidity.Backend.MemoryCopies.HeapContentsInterface

/-! Reading live contents from the existing heap mirror. These proofs reuse
published copy functions and type-rank fuel independence; no evaluator is added. -/
namespace Solidity.Backend.MemoryCopies
open Semantics (tyRank fieldsRank)

private theorem copyAt_eq {H : HTy} (hp : Heap H) (k : Nat) (T : Ty)
    (bound : tyRank T < k + 1) (memory : MVal H T) :
    MVal.copyAt hp k (MVal.copyBelow hp k) T bound memory = MVal.copyMToSt hp memory :=
  MVal.copyBelow_eq hp (k + 1) T bound memory

private theorem map_copyAt_eq {H : HTy} (hp : Heap H) (k : Nat) (T : Ty)
    (bound : tyRank T < k + 1) (values : List (MVal H T)) :
    values.map (MVal.copyAt hp k (MVal.copyBelow hp k) T bound) =
      values.map (MVal.copyMToSt hp) :=
  congrArg (fun f => values.map f) (funext (copyAt_eq hp k T bound))

private theorem array_eq_of_contents {E : Ty} {n m : Nat}
    (left : SVec E n) (right : SVec E m) (ln : n < 2 ^ 256) (rm : m < 2 ^ 256)
    (contents : left.toList = right.toList) :
    SVal.array left .nil ln = SVal.array right .nil rm := by
  have lengths : n = m := by
    simpa only [SVec.length_toList] using congrArg List.length contents
  cases lengths
  have values : left = right := SVec.eq_of_toList_eq left right contents
  cases values
  rfl

mutual
/-- A full mirrored value reads back as its live contents. -/
theorem mirror_contents {H : HTy} (hp : Heap H) :
    {T : Ty} → (value : SVal T) → (memory : MVal H T) → (frontier : Nat) →
    value.Mirrors hp frontier memory → MVal.copyMToSt hp memory = value.strip
  | _, .prim value, memory, _, mirrored => by
    rw [MVal.copyMToSt_prim, SVal.strip_prim]
    exact congrArg SVal.prim mirrored
  | _, .struct fields, memory, frontier, mirrored => by
    rw [SVal.strip_struct]
    unfold MVal.copyMToSt
    rw [MVal.copyBelow, MVal.copyAt, MVal.copyRefAt]
    exact congrArg SVal.struct (mirror_fields hp _ fields _ _ frontier mirrored.2)
  | _, .array values _ _, memory, frontier, mirrored => by
    rw [SVal.strip_array]
    unfold MVal.copyMToSt
    rw [MVal.copyBelow, MVal.copyAt, MVal.copyRefAt]
    apply array_eq_of_contents
    rw [SVec.toList_ofList, map_copyAt_eq]
    simpa only [MObj.elems_dyn] using mirror_elements hp values _ frontier mirrored.2
  | _, .fixed values, memory, frontier, mirrored => by
    rw [SVal.strip_fixed]
    unfold MVal.copyMToSt
    rw [MVal.copyBelow, MVal.copyAt, MVal.copyRefAt]
    apply congrArg SVal.fixed
    apply SVec.eq_of_toList_eq
    rw [SVec.toList_ofLen, map_copyAt_eq]
    simpa only [MObj.elems_fixed] using mirror_elements hp values _ frontier mirrored.2
  | _, .map _ _, _, _, mirrored => False.elim mirrored

/-- Struct fields read from the existing rank-bounded copy operation. -/
theorem mirror_fields {H : HTy} (hp : Heap H) (k : Nat) :
    {fs : List (Name × Ty)} → (values : SFields fs) → (bound : fieldsRank fs < k) →
    (memory : MFields H fs) → (frontier : Nat) → values.Mirrors hp frontier memory →
    MFields.copyBelow k (MVal.copyBelow hp k) fs bound memory = values.strip
  | _, .nil, _, _, _, _ => by simp only [MFields.copyBelow, SFields.strip_nil]
  | _, .cons value rest, _, memory, frontier, mirrored => by
    simp only [MFields.copyBelow, SFields.strip_cons]
    rw [MVal.copyBelow_eq]
    exact congr (congrArg SFields.cons (mirror_contents hp value memory.1 frontier mirrored.1))
      (mirror_fields hp k rest _ memory.2 frontier mirrored.2)

/-- Live array elements, including nested references, read in order. -/
theorem mirror_elements {H : HTy} (hp : Heap H) :
    {E : Ty} → {n : Nat} → (values : SVec E n) → (memory : List (MVal H E)) →
    (frontier : Nat) → values.Mirrors hp frontier memory →
    memory.map (MVal.copyMToSt hp) = values.strip.toList
  | _, _, .nil, memory, _, mirrored => by
    change memory = [] at mirrored
    rw [mirrored]
    simp only [List.map_nil, SVec.strip_nil, SVec.toList_nil]
  | _, _, .cons value rest, _, frontier, mirrored => by
    obtain ⟨memory, tail, rfl, headMirror, tailMirror⟩ := mirrored
    simp only [List.map_cons, SVec.strip_cons, SVec.toList_cons]
    exact congr (congrArg List.cons (mirror_contents hp value memory frontier headMirror))
      (mirror_elements hp rest tail frontier tailMirror)
end

/-- The signature-only mirror obligation is inhabited for every existing mirror. -/
def mirrorContents : MirrorContentsCertificate := ⟨mirror_contents⟩

/-- Generic V2 contents certificate. Freshness, framing and dynamic lengths
remain the existing master theorems; they are not assumed as new premises. -/
def storageHeapContents {R : RefTy} (value : SVal (.ref R))
    (memory : (Ty.ref R).mapFree = true) : V2.StorageHeapCertificate value memory where
  contents := by
    intro H hp
    exact mirror_contents (value.copyStToM hp memory).heap value _ H.length
      (SVal.mirrors_copyStToM hp value memory)

/-- info: 'Solidity.Backend.MemoryCopies.mirror_contents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mirror_contents
/-- info: 'Solidity.Backend.MemoryCopies.mirror_fields' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mirror_fields
/-- info: 'Solidity.Backend.MemoryCopies.mirror_elements' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mirror_elements
/-- info: 'Solidity.Backend.MemoryCopies.mirrorContents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mirrorContents
/-- info: 'Solidity.Backend.MemoryCopies.storageHeapContents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms storageHeapContents
end Solidity.Backend.MemoryCopies
