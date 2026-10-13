import Solidity.Typing.Constructibility

/-!
# What the tests of `wt(storage)` decide

`SVal.Canon`, `SVal.Tight` (`Typing/Reachability.lean`, `Typing/Tight.lean`)
and the keys in range are propositions; `wt(storage)` (`Calculus/Problem.lean`)
asks them as tests the kernel evaluates (`Semantics/StorageWt.lean`:
`SVal.allB B`, a fold of node tests `B : HeredB`).  Here each test decides
its `Hered`'s node conditions clause for clause (`SVal.allB_iff`):
`Storage.shapeB` is canonical and tight, `Storage.keysB` the keys in range.
-/

namespace Solidity

open Semantics (structDef lookupBy setBy nodupKeysB)

variable {C : Contract}

/-- Node tests that decide a predicate's node conditions. -/
structure HeredB.Decides (B : HeredB) (P : Hered) : Prop where
  arr : ∀ {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E), B.arr e sh = true ↔ P.arr e sh
  fix : ∀ E n, B.fix E n = true ↔ P.fix E n
  map : ∀ (K : PrimTy) {V : Ty} (m : SMap K V) (d : SVal V), B.map K m d = true ↔ P.map K m d

section Iff

variable {P : Hered} {B : HeredB}

mutual
/-- **The test decides the predicate**, its node tests deciding the node
conditions. -/
theorem SVal.allB_iff (hB : B.Decides P) : {T : Ty} → (v : SVal T) → v.allB B = true ↔ v.All P
  | _, .prim _ => by simp only [SVal.allB, SVal.All]
  | _, .struct fs => by simp only [SVal.allB, SVal.All]; exact SFields.allB_iff hB fs
  | _, .array e sh _ => by
    simp only [SVal.allB, SVal.All, Bool.and_eq_true]
    rw [hB.arr, SVec.allB_iff hB e, SList.allB_iff hB sh, and_assoc]
  | _, .fixed e => by
    simp only [SVal.allB, SVal.All, Bool.and_eq_true]
    rw [hB.fix, SVec.allB_iff hB e]
  | _, .map m d => by
    simp only [SVal.allB, SVal.All, Bool.and_eq_true]
    rw [hB.map, SMap.allB_iff hB m, SVal.allB_iff hB d, and_assoc]

theorem SFields.allB_iff (hB : B.Decides P) : {fs : List (Name × Ty)} → (x : SFields fs) →
    x.allB B = true ↔ x.All P
  | _, .nil => by simp only [SFields.allB, SFields.All]
  | _, .cons v rest => by
    simp only [SFields.allB, SFields.All, Bool.and_eq_true]
    rw [SVal.allB_iff hB v, SFields.allB_iff hB rest]

theorem SList.allB_iff (hB : B.Decides P) : {E : Ty} → (l : SList E) → l.allB B = true ↔ l.All P
  | _, .nil => by simp only [SList.allB, SList.All]
  | _, .cons v rest => by
    simp only [SList.allB, SList.All, Bool.and_eq_true]
    rw [SVal.allB_iff hB v, SList.allB_iff hB rest]

theorem SVec.allB_iff (hB : B.Decides P) : {E : Ty} → {n : Nat} → (l : SVec E n) →
    l.allB B = true ↔ l.All P
  | _, _, .nil => by simp only [SVec.allB, SVec.All]
  | _, _, .cons v rest => by
    simp only [SVec.allB, SVec.All, Bool.and_eq_true]
    rw [SVal.allB_iff hB v, SVec.allB_iff hB rest]

theorem SMap.allB_iff (hB : B.Decides P) : {K : PrimTy} → {V : Ty} → (m : SMap K V) → m.allB B = true ↔ m.All P
  | _, _, .nil => by simp only [SMap.allB, SMap.All]
  | _, _, .cons _ v rest => by
    simp only [SMap.allB, SMap.All, Bool.and_eq_true]
    rw [SVal.allB_iff hB v, SMap.allB_iff hB rest]
end

end Iff

/-! ## The three tests -/

/-- Every mapping's keys in range. -/
def keysH : Hered where
  arr _ _ := True
  fix _ _ := True
  map K := fun m _ => ∀ e ∈ m.toList, K.keyOk (PrimTy.key e.1)

theorem canonHB_decides : canonHB.Decides canonH :=
  ⟨fun _ _ => by simp only [canonHB, canonH],
    fun _ _ => by simp only [canonHB, canonH],
    fun _ _ m d => by simp only [canonHB, canonH, Bool.and_eq_true, SVal.beq_iff]⟩

theorem SVal.canonB_iff {T : Ty} (v : SVal T) : v.allB canonHB = true ↔ v.Canon :=
  SVal.allB_iff canonHB_decides v

theorem SList.toList_isEmpty {E : Ty} (sh : SList E) : sh.toList.isEmpty = true ↔ sh = .nil := by
  cases sh with
  | nil => simp only [SList.toList_nil, List.isEmpty_nil]
  | cons v rest => simp only [SList.toList_cons, List.isEmpty_cons, Bool.false_eq_true,
      reduceCtorEq]

theorem SMap.toList_isEmpty {K : PrimTy} {V : Ty} (m : SMap K V) : m.toList.isEmpty = true ↔ m = .nil := by
  cases m with
  | nil => simp only [SMap.toList_nil, List.isEmpty_nil]
  | cons k v rest => simp only [SMap.toList_cons, List.isEmpty_cons, Bool.false_eq_true,
      reduceCtorEq]

theorem tightHB_arr {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E) :
    tightHB.arr e sh = true ↔ tightH.arr e sh := by
  show ((E.defaultOkS || (n == 0 && sh.toList.isEmpty)) &&
    (!E.isPrimitive || sh.toList.all fun w => w.beq (SVal.dflt E))) = true ↔
    ((E.defaultOkS = false → n = 0 ∧ sh = .nil) ∧
      (E.isPrimitive = true → ∀ w ∈ sh.toList, w = SVal.dflt E))
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, SList.toList_isEmpty,
    Bool.not_eq_true', List.all_eq_true, SVal.beq_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun hd => ?_, fun hp => ?_⟩
    · rcases h1 with h | h
      · rw [hd] at h; exact nomatch h
      · exact h
    · rcases h2 with h | h
      · rw [hp] at h; exact nomatch h
      · exact h
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · cases hd : E.defaultOkS
      · exact Or.inr (h1 hd)
      · exact Or.inl rfl
    · cases hp : E.isPrimitive
      · exact Or.inl rfl
      · exact Or.inr (h2 hp)

theorem tightHB_decides : tightHB.Decides tightH :=
  ⟨tightHB_arr, fun _ _ => by simp only [tightHB, tightH],
    fun _ _ _ _ => by simp only [tightHB, tightH]⟩

theorem SVal.tightB_iff {T : Ty} (v : SVal T) : v.allB tightHB = true ↔ v.Tight :=
  SVal.allB_iff tightHB_decides v

theorem keysHB_decides : keysHB.Decides keysH :=
  ⟨fun _ _ => by simp only [keysHB, keysH],
    fun _ _ => by simp only [keysHB, keysH],
    fun K _ m d => by
      show (m.toList.all fun e => K.keyFits (PrimTy.key e.1)) = true ↔ ∀ e ∈ m.toList, K.keyOk (PrimTy.key e.1)
      simp only [List.all_eq_true, PrimTy.keyOk]⟩

theorem SVal.keysB_iff {T : Ty} (v : SVal T) : v.allB keysHB = true ↔ v.All keysH :=
  SVal.allB_iff keysHB_decides v

/-! ## The storage's tests -/

theorem Storage.shapeB_iff (st : Storage C) : st.shapeB = true ↔ st.Canon ∧ st.Tight := by
  simp only [Storage.shapeB, Bool.and_eq_true]
  rw [SFields.allB_iff canonHB_decides st, SFields.allB_iff tightHB_decides st]

theorem Storage.keysB_iff (st : Storage C) : st.keysB = true ↔ st.All keysH :=
  SFields.allB_iff keysHB_decides st

/-- Keys and slots in range have their keys in range. -/
theorem Storage.keysB_of_fits {st : Storage C} (h : st.Fits) : st.keysB = true :=
  (Storage.keysB_iff st).2 (SFields.all_mono (P := keysH) (Q := fitsH) (G := fun _ => True)
    ⟨fun _ _ _ _ => trivial, fun _ _ => trivial, fun _ _ _ => trivial, fun _ _ _ => trivial,
      fun _ _ _ _ _ => trivial, fun _ _ _ _ => trivial, fun _ _ _ h => h⟩ st
    (fun _ _ => trivial) h)

/-- Bounded storage has its keys in range. -/
theorem Storage.keysB_of_bnd {st : Storage C} (h : st.Bnd) : st.keysB = true :=
  (Storage.keysB_iff st).2 (SFields.all_mono (P := keysH) (Q := bndH) (G := fun _ => True)
    ⟨fun _ _ _ _ => trivial, fun _ _ => trivial, fun _ _ _ => trivial, fun _ _ _ => trivial,
      fun _ _ _ _ _ => trivial, fun _ _ _ _ => trivial, fun _ _ _ h => h⟩ st
    (fun _ _ => trivial) h)

end Solidity
