import Solidity.Theory.Typed.MemMirror

/-!
Joint inputs for all thirteen explicit memory-mirror interface theorems.
A populated heap, singleton fields and singleton vectors avoid relying on
empty catalogs or empty data containers. Prefix/keeps premises and mirrors
are proved together. This is model-input feasibility, not physical EVM gas.
-/
namespace H62.AuditTheories
open Solidity
private abbrev MB : Ty := .prim .bool
private abbrev MH : HTy := [.array MB]

/-- A heap with a real live array object containing false. -/
def mirrorHeap : Heap MH := (⟨[false], by decide⟩, ())
/-- Its in-bounds typed reference. -/
def mirrorRoot : HRef MH (.array MB) := ⟨0, rfl⟩

/-- The bound and primitive mirror premises coexist on a populated heap. -/
theorem mirror_val_mono_joint_witness :
    ∃ (H : HTy) (hp : Heap H) (n n' : Nat) (T : Ty) (v : SVal T) (w : MVal H T),
      n' ≤ n ∧ v.Mirrors hp n w :=
  ⟨MH, mirrorHeap, 1, 0, MB, .prim false, false, by decide, rfl⟩

/-- Singleton fields and the order bound coexist with their mirror. -/
theorem mirror_fields_mono_joint_witness :
    ∃ (H : HTy) (hp : Heap H) (n n' : Nat) (fs : List (Name × Ty))
      (x : SFields fs) (o : MFields H fs), n' ≤ n ∧ x.Mirrors hp n o :=
  ⟨MH, mirrorHeap, 1, 0, [("flag", MB)], .cons (.prim false) .nil,
    (false, ()), by decide, rfl, True.intro⟩

/-- A singleton vector's mirror and the order bound hold simultaneously. -/
theorem mirror_vec_mono_joint_witness :
    ∃ (H : HTy) (hp : Heap H) (n n' : Nat) (E : Ty) (k : Nat)
      (x : SVec E k) (l : List (MVal H E)), n' ≤ n ∧ x.Mirrors hp n l :=
  ⟨MH, mirrorHeap, 1, 0, MB, 1, .cons (.prim false) .nil, [false],
    by decide, false, [], rfl, rfl, rfl⟩

/-- The prefix, quantified heap preservation and value mirror are joint. -/
theorem mirror_val_wk_joint_witness :
    ∃ (H H' : HTy) (e : H <+: H') (hp : Heap H) (hp' : Heap H')
      (n : Nat) (T : Ty) (v : SVal T) (w : MVal H T),
      Heap.Keeps e hp hp' ∧ v.Mirrors hp n w :=
  ⟨MH, MH, List.prefix_refl _, mirrorHeap, mirrorHeap, 0, MB, .prim false,
    false, Heap.Keeps.refl _, rfl⟩

/-- Heap preservation and a nonempty fields mirror coexist. -/
theorem mirror_fields_wk_joint_witness :
    ∃ (H H' : HTy) (e : H <+: H') (hp : Heap H) (hp' : Heap H')
      (n : Nat) (fs : List (Name × Ty)) (x : SFields fs) (o : MFields H fs),
      Heap.Keeps e hp hp' ∧ x.Mirrors hp n o :=
  ⟨MH, MH, List.prefix_refl _, mirrorHeap, mirrorHeap, 0,
    [("flag", MB)], .cons (.prim false) .nil, (false, ()),
    Heap.Keeps.refl _, rfl, True.intro⟩

/-- Heap preservation and a nonempty vector mirror coexist. -/
theorem mirror_vec_wk_joint_witness :
    ∃ (H H' : HTy) (e : H <+: H') (hp : Heap H) (hp' : Heap H')
      (n : Nat) (E : Ty) (k : Nat) (x : SVec E k) (l : List (MVal H E)),
      Heap.Keeps e hp hp' ∧ x.Mirrors hp n l :=
  ⟨MH, MH, List.prefix_refl _, mirrorHeap, mirrorHeap, 0, MB, 1,
    .cons (.prim false) .nil, [false], Heap.Keeps.refl _, false, [], rfl, rfl, rfl⟩

/-- A genuine array can be copied from storage into a populated heap. -/
theorem mirror_val_copy_joint_witness :
    ∃ (H : HTy) (hp : Heap H) (T : Ty) (v : SVal T) (h : T.mapFree = true),
      v.Mirrors (v.copyStToM hp h).heap H.length (v.copyStToM hp h).val :=
  ⟨MH, mirrorHeap, .ref (.array MB),
    .array (.cons (.prim true) .nil) .nil (by decide), rfl,
    SVal.mirrors_copyStToM _ _ _⟩

/-- The entire quantified map-free fields premise is inhabited jointly. -/
theorem mirror_fields_copy_joint_witness :
    ∃ (H : HTy) (hp : Heap H) (fs : List (Name × Ty)) (x : SFields fs)
      (h : ∀ fT ∈ fs, fT.2.mapFree = true),
      x.Mirrors (x.copyStToM hp h).heap H.length (x.copyStToM hp h).val := by
  refine ⟨MH, mirrorHeap, [("flag", MB)], .cons (.prim false) .nil, ?_, ?_⟩
  · intro fT hf
    have he : fT = ("flag", MB) := List.mem_singleton.mp hf
    subst fT
    rfl
  · exact SFields.mirrors_copyStToM _ _ _

/-- A nonempty map-free vector has all copy inputs. -/
theorem mirror_vec_copy_joint_witness :
    ∃ (H : HTy) (hp : Heap H) (E : Ty) (k : Nat) (x : SVec E k)
      (h : E.mapFree = true),
      x.Mirrors (x.copyStToM hp h).heap H.length (x.copyStToM hp h).val.1 :=
  ⟨MH, mirrorHeap, MB, 1, .cons (.prim false) .nil, rfl,
    SVec.mirrors_copyStToM _ _ _⟩

/-- The primitive read inputs include its successful mirror premise. -/
theorem mirror_prim_joint_witness :
    ∃ (H : HTy) (hp : Heap H) (n : Nat) (p : PrimTy)
      (v : SVal (.prim p)) (w : MVal H (.prim p)), v.Mirrors hp n w :=
  ⟨MH, mirrorHeap, 0, .bool, .prim false, false, rfl⟩

/-- A real object reference satisfies the mirror's identity lower bound. -/
theorem mirror_id_ge_joint_witness :
    ∃ (H : HTy) (hp : Heap H) (n : Nat) (R : RefTy)
      (v : SVal (.ref R)) (r : MVal H (.ref R)), v.Mirrors hp n r := by
  refine ⟨MH, mirrorHeap, 0, .array MB,
    .array (.cons (.prim false) .nil) .nil (by decide), mirrorRoot, ?_⟩
  simp only [SVal.Mirrors, MObj.elems_dyn]
  change (0 : Nat) ≤ 0 ∧
    SVec.Mirrors (E := MB) mirrorHeap 0 (.cons (.prim false) .nil) [false]
  exact ⟨by decide, false, [], rfl, rfl, rfl⟩

/-- The fields mirror and named member lookup hold together. -/
theorem mirror_fields_get_joint_witness :
    ∃ (H : HTy) (hp : Heap H) (n : Nat) (f : Name)
      (fs : List (Name × Ty)) (x : SFields fs) (o : MFields H fs) (T : Ty),
      x.Mirrors hp n o ∧ Semantics.lookupBy f fs = some T :=
  ⟨MH, mirrorHeap, 0, "flag", [("flag", MB)], .cons (.prim false) .nil,
    (false, ()), MB, ⟨rfl, True.intro⟩, rfl⟩

/-- The post-premise index is an in-bounds read of the nonempty mirror. -/
theorem mirror_vec_getElem_joint_witness :
    ∃ (H : HTy) (hp : Heap H) (n : Nat) (E : Ty) (k : Nat)
      (x : SVec E k) (l : List (MVal H E)) (i : Nat),
      x.Mirrors hp n l ∧ i < k :=
  ⟨MH, mirrorHeap, 0, MB, 1, .cons (.prim false) .nil, [false], 0,
    ⟨false, [], rfl, rfl, rfl⟩, by decide⟩

#print axioms mirror_val_mono_joint_witness
#print axioms mirror_fields_mono_joint_witness
#print axioms mirror_vec_mono_joint_witness
#print axioms mirror_val_wk_joint_witness
#print axioms mirror_fields_wk_joint_witness
#print axioms mirror_vec_wk_joint_witness
#print axioms mirror_val_copy_joint_witness
#print axioms mirror_fields_copy_joint_witness
#print axioms mirror_vec_copy_joint_witness
#print axioms mirror_prim_joint_witness
#print axioms mirror_id_ge_joint_witness
#print axioms mirror_fields_get_joint_witness
#print axioms mirror_vec_getElem_joint_witness
end H62.AuditTheories
