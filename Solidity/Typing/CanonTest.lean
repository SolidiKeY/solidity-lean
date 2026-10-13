import Solidity.Typing.Constructibility

/-!
# The tests `wt(storage)` makes

`SVal.Canon`, `SVal.Tight` (`Typing/Reachability.lean`, `Typing/Tight.lean`)
and the keys in range are propositions; `wt(storage)` (`Calculus/Problem.lean`)
asks them as tests the kernel evaluates (Gate G0): `SVal.allB B`, a fold
(`SVal.fold`, compiled by its `match` twin), of node tests `B : HeredB` that
decide a `Hered`'s node conditions clause for clause (`SVal.allB_iff`).
`Storage.shapeB` is canonical and tight, `Storage.keysB` the keys in range,
`Storage.wtB` both.
-/

namespace Solidity

open Semantics (structDef lookupBy setBy nodupKeysB)

variable {C : Contract}

/-- A predicate's node conditions as tests. -/
structure HeredB where
  arr : {E : Ty} → {n : Nat} → SVec E n → SList E → Bool
  fix : Ty → Nat → Bool
  map : Ty → {V : Ty} → SMap V → SVal V → Bool

/-- Every node passing `B`'s test, as a fold. -/
def allBFold (B : HeredB) : Fold where
  V _ := Bool
  F _ := Bool
  L _ := Bool
  W _ _ := Bool
  M _ := Bool
  prim := fun _ => true
  struct := fun _ ih => ih
  array := fun e sh _ ie ish => B.arr e sh && ie && ish
  fixed := fun {E} {n} _ ie => B.fix E n && ie
  map := fun {K} {_} m d im id => B.map K m d && im && id
  fnil := true
  fcons := fun _ _ iv ir => iv && ir
  lnil := true
  lcons := fun _ _ iv ir => iv && ir
  wnil := true
  wcons := fun _ _ iv ir => iv && ir
  mnil := true
  mcons := fun _ _ _ iv ir => iv && ir

/-- Every node of `v` passing `B`'s test. -/
def SVal.allB (B : HeredB) {T : Ty} (v : SVal T) : Bool := v.fold (allBFold B)
def SFields.allB (B : HeredB) {fs : List (Name × Ty)} (x : SFields fs) : Bool := x.fold (allBFold B)
def SList.allB (B : HeredB) {E : Ty} (l : SList E) : Bool := l.fold (allBFold B)
def SVec.allB (B : HeredB) {E : Ty} {n : Nat} (l : SVec E n) : Bool := l.fold (allBFold B)
def SMap.allB (B : HeredB) {V : Ty} (m : SMap V) : Bool := m.fold (allBFold B)

section AllB

variable (B : HeredB)

theorem SVal.allB_prim {p : PrimTy} (v : p.Denote) : (SVal.prim v).allB B = true := rfl
theorem SVal.allB_struct {s : Name} (fs : SFields (structDef s)) :
    (SVal.struct fs).allB B = fs.allB B := rfl
theorem SVal.allB_array {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E) (h : n < 2 ^ 256) :
    (SVal.array e sh h).allB B = (B.arr e sh && e.allB B && sh.allB B) := rfl
theorem SVal.allB_fixed {E : Ty} {n : Nat} (e : SVec E n) :
    (SVal.fixed e).allB B = (B.fix E n && e.allB B) := rfl
theorem SVal.allB_map {K V : Ty} (m : SMap V) (d : SVal V) :
    (SVal.map (K := K) m d).allB B = (B.map K m d && m.allB B && d.allB B) := rfl
theorem SFields.allB_nil : (SFields.nil).allB B = true := rfl
theorem SFields.allB_cons {f : Name} {T : Ty} {fs : List (Name × Ty)} (v : SVal T)
    (rest : SFields fs) : (SFields.cons (f := f) v rest).allB B = (v.allB B && rest.allB B) := rfl
theorem SList.allB_nil {E : Ty} : (SList.nil (E := E)).allB B = true := rfl
theorem SList.allB_cons {E : Ty} (v : SVal E) (rest : SList E) :
    (SList.cons v rest).allB B = (v.allB B && rest.allB B) := rfl
theorem SVec.allB_nil {E : Ty} : (SVec.nil (E := E)).allB B = true := rfl
theorem SVec.allB_cons {E : Ty} {n : Nat} (v : SVal E) (rest : SVec E n) :
    (SVec.cons v rest).allB B = (v.allB B && rest.allB B) := rfl
theorem SMap.allB_nil {V : Ty} : (SMap.nil (V := V)).allB B = true := rfl
theorem SMap.allB_cons {V : Ty} (k : Int) (v : SVal V) (rest : SMap V) :
    (SMap.cons k v rest).allB B = (v.allB B && rest.allB B) := rfl

end AllB

attribute [irreducible] SVal.allB SFields.allB SList.allB SVec.allB SMap.allB
attribute [eqns SVal.allB_prim SVal.allB_struct SVal.allB_array SVal.allB_fixed SVal.allB_map]
  SVal.allB
attribute [eqns SFields.allB_nil SFields.allB_cons] SFields.allB
attribute [eqns SList.allB_nil SList.allB_cons] SList.allB
attribute [eqns SVec.allB_nil SVec.allB_cons] SVec.allB
attribute [eqns SMap.allB_nil SMap.allB_cons] SMap.allB

section Iff

variable {P : Hered} {B : HeredB}
  (harr : ∀ {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E), B.arr e sh = true ↔ P.arr e sh)
  (hfix : ∀ E n, B.fix E n = true ↔ P.fix E n)
  (hmap : ∀ K {V : Ty} (m : SMap V) (d : SVal V), B.map K m d = true ↔ P.map K m d)

include harr hfix hmap

mutual
/-- **The test decides the predicate**, its node tests deciding the node
conditions. -/
theorem SVal.allB_iff : {T : Ty} → (v : SVal T) → v.allB B = true ↔ v.All P
  | _, .prim _ => by simp only [SVal.allB, SVal.All]
  | _, .struct fs => by simp only [SVal.allB, SVal.All]; exact SFields.allB_iff fs
  | _, .array e sh _ => by
    simp only [SVal.allB, SVal.All, Bool.and_eq_true]
    rw [harr, SVec.allB_iff e, SList.allB_iff sh, and_assoc]
  | _, .fixed e => by
    simp only [SVal.allB, SVal.All, Bool.and_eq_true]
    rw [hfix, SVec.allB_iff e]
  | _, .map m d => by
    simp only [SVal.allB, SVal.All, Bool.and_eq_true]
    rw [hmap, SMap.allB_iff m, SVal.allB_iff d, and_assoc]

theorem SFields.allB_iff : {fs : List (Name × Ty)} → (x : SFields fs) → x.allB B = true ↔ x.All P
  | _, .nil => by simp only [SFields.allB, SFields.All]
  | _, .cons v rest => by
    simp only [SFields.allB, SFields.All, Bool.and_eq_true]
    rw [SVal.allB_iff v, SFields.allB_iff rest]

theorem SList.allB_iff : {E : Ty} → (l : SList E) → l.allB B = true ↔ l.All P
  | _, .nil => by simp only [SList.allB, SList.All]
  | _, .cons v rest => by
    simp only [SList.allB, SList.All, Bool.and_eq_true]
    rw [SVal.allB_iff v, SList.allB_iff rest]

theorem SVec.allB_iff : {E : Ty} → {n : Nat} → (l : SVec E n) → l.allB B = true ↔ l.All P
  | _, _, .nil => by simp only [SVec.allB, SVec.All]
  | _, _, .cons v rest => by
    simp only [SVec.allB, SVec.All, Bool.and_eq_true]
    rw [SVal.allB_iff v, SVec.allB_iff rest]

theorem SMap.allB_iff : {V : Ty} → (m : SMap V) → m.allB B = true ↔ m.All P
  | _, .nil => by simp only [SMap.allB, SMap.All]
  | _, .cons _ v rest => by
    simp only [SMap.allB, SMap.All, Bool.and_eq_true]
    rw [SVal.allB_iff v, SMap.allB_iff rest]
end

end Iff

/-! ## The three tests -/

/-- `canonH`'s test: distinct keys, the default default. -/
def canonHB : HeredB where
  arr _ _ := true
  fix _ _ := true
  map _ := fun {V} m d => nodupKeysB m.toList && d.beq (SVal.dflt V)

/-- `tightH`'s test. -/
def tightHB : HeredB where
  arr := fun {E} {n} _ sh => (E.defaultOkS || (n == 0 && sh.toList.isEmpty)) &&
    (!E.isPrimitive || sh.toList.all fun w => w.beq (SVal.dflt E))
  fix _ _ := true
  map K := fun m _ => K.isKey || m.toList.isEmpty

/-- A key in its key type's range, as a test. -/
def Ty.keyOkB : Ty → Int → Bool
  | .prim p, k => p.keyFits k
  | .ref _, _ => true

/-- Every mapping's keys in range. -/
def keysH : Hered where
  arr _ _ := True
  fix _ _ := True
  map K := fun m _ => ∀ e ∈ m.toList, K.keyOk e.1

/-- `keysH`'s test. -/
def keysHB : HeredB where
  arr _ _ := true
  fix _ _ := true
  map K := fun m _ => m.toList.all fun e => K.keyOkB e.1

theorem SVal.canonB_iff {T : Ty} (v : SVal T) : v.allB canonHB = true ↔ v.Canon :=
  SVal.allB_iff (P := canonH) (fun _ _ => by simp only [canonHB, canonH])
    (fun _ _ => by simp only [canonHB, canonH])
    (fun _ _ m d => by simp only [canonHB, canonH, Bool.and_eq_true, SVal.beq_iff]) v

theorem SList.toList_isEmpty {E : Ty} (sh : SList E) : sh.toList.isEmpty = true ↔ sh = .nil := by
  cases sh with
  | nil => simp only [SList.toList_nil, List.isEmpty_nil]
  | cons v rest => simp only [SList.toList_cons, List.isEmpty_cons, Bool.false_eq_true,
      reduceCtorEq]

theorem SMap.toList_isEmpty {V : Ty} (m : SMap V) : m.toList.isEmpty = true ↔ m = .nil := by
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

theorem SVal.tightB_iff {T : Ty} (v : SVal T) : v.allB tightHB = true ↔ v.Tight :=
  SVal.allB_iff (P := tightH) tightHB_arr (fun _ _ => by simp only [tightHB, tightH])
    (fun K _ m d => by
      show (K.isKey || m.toList.isEmpty) = true ↔ (K.isKey = false → m = .nil)
      rw [Bool.or_eq_true, SMap.toList_isEmpty]
      cases K.isKey
      · simp only [Bool.false_eq_true, false_or, forall_const]
      · simp only [true_or, Bool.true_eq_false, false_implies]) v

theorem Ty.keyOkB_iff (K : Ty) (k : Int) : K.keyOkB k = true ↔ K.keyOk k := by
  cases K <;> simp only [Ty.keyOkB, Ty.keyOk]

theorem SVal.keysB_iff {T : Ty} (v : SVal T) : v.allB keysHB = true ↔ v.All keysH :=
  SVal.allB_iff (P := keysH) (fun _ _ => by simp only [keysHB, keysH])
    (fun _ _ => by simp only [keysHB, keysH])
    (fun K _ m d => by
      show (m.toList.all fun e => K.keyOkB e.1) = true ↔ ∀ e ∈ m.toList, K.keyOk e.1
      simp only [List.all_eq_true, Ty.keyOkB_iff]) v

theorem SFields.allB_iff' {P : Hered} {B : HeredB}
    (h : ∀ {T : Ty} (v : SVal T), v.allB B = true ↔ v.All P) :
    {fs : List (Name × Ty)} → (x : SFields fs) → x.allB B = true ↔ x.All P
  | _, .nil => by simp only [SFields.allB, SFields.All]
  | _, .cons v rest => by
    simp only [SFields.allB, SFields.All, Bool.and_eq_true]
    rw [h v, SFields.allB_iff' h rest]

/-! ## The storage's tests -/

/-- Every root canonical and tight. -/
def Storage.shapeB (st : Storage C) : Bool := SFields.allB canonHB st && SFields.allB tightHB st

/-- Every mapping key in range. -/
def Storage.keysB (st : Storage C) : Bool := SFields.allB keysHB st

/-- What `wt(storage)` tests: the shape and the keys. -/
def Storage.wtB (st : Storage C) : Bool := st.shapeB && st.keysB

theorem Storage.shapeB_iff (st : Storage C) : st.shapeB = true ↔ st.Canon ∧ st.Tight := by
  simp only [Storage.shapeB, Bool.and_eq_true]
  rw [SFields.allB_iff' SVal.canonB_iff st, SFields.allB_iff' SVal.tightB_iff st]

theorem Storage.keysB_iff (st : Storage C) : st.keysB = true ↔ st.All keysH :=
  SFields.allB_iff' SVal.keysB_iff st

/-- Keys and slots in range have their keys in range. -/
theorem Storage.keysB_of_fits {st : Storage C} (h : st.Fits) : st.keysB = true :=
  (Storage.keysB_iff st).2 (SFields.all_mono (P := keysH) (Q := fitsH) (fun _ => True)
    (fun _ _ _ _ => trivial) (fun _ _ => trivial) (fun _ _ _ => trivial) (fun _ _ _ => trivial)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ _ h => h) st
    (fun _ _ => trivial) h)

/-- Bounded storage has its keys in range. -/
theorem Storage.keysB_of_bnd {st : Storage C} (h : st.Bnd) : st.keysB = true :=
  (Storage.keysB_iff st).2 (SFields.all_mono (P := keysH) (Q := bndH) (fun _ => True)
    (fun _ _ _ _ => trivial) (fun _ _ => trivial) (fun _ _ _ => trivial) (fun _ _ _ => trivial)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ _ h => h) st
    (fun _ _ => trivial) h)

end Solidity
