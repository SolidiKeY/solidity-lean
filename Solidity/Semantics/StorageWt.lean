import Solidity.Semantics.Storage

/-!
# The test `wt(storage)` runs

`wt(storage)` (`Op1.wt`, `Signature.lean`) is a test the kernel evaluates
in certificates (Gate G0): `SVal.allB B`, a fold (`SVal.fold`, compiled by
its `match` twin), of node tests `B : HeredB`.  `Storage.shapeB` asks every
root canonical and tight, which is all `Storage.wtB` asks: a mapping's keys
are values of its key type, so no key is out of range.  What they decide is
`Typing/CanonTest.lean`'s (`SVal.allB_iff`, `Storage.shapeB_iff`): the
reachable storages (`wt_iff_reachable`, `Calculus/Problem.lean`).
-/

namespace Solidity

open Semantics (structDef nodupKeysB)

variable {C : Contract}

/-- A predicate's node conditions as tests. -/
structure HeredB where
  arr : {E : Ty} → {n : Nat} → SVec E n → SList E → Bool
  fix : Ty → Nat → Bool
  map : (K : PrimTy) → {V : Ty} → SMap K V → SVal V → Bool

/-- Every node passing `B`'s test, as a fold. -/
def allBFold (B : HeredB) : Fold where
  V _ := Bool
  F _ := Bool
  L _ := Bool
  W _ _ := Bool
  M _ _ := Bool
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
def SMap.allB (B : HeredB) {K : PrimTy} {V : Ty} (m : SMap K V) : Bool := m.fold (allBFold B)

section AllB

variable (B : HeredB)

theorem SVal.allB_prim {p : PrimTy} (v : p.Denote) : (SVal.prim v).allB B = true := rfl
theorem SVal.allB_struct {s : Name} (fs : SFields (structDef s)) :
    (SVal.struct fs).allB B = fs.allB B := rfl
theorem SVal.allB_array {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E) (h : n < 2 ^ 256) :
    (SVal.array e sh h).allB B = (B.arr e sh && e.allB B && sh.allB B) := rfl
theorem SVal.allB_fixed {E : Ty} {n : Nat} (e : SVec E n) :
    (SVal.fixed e).allB B = (B.fix E n && e.allB B) := rfl
theorem SVal.allB_map {K : PrimTy} {V : Ty} (m : SMap K V) (d : SVal V) :
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
theorem SMap.allB_nil {K : PrimTy} {V : Ty} : (SMap.nil (K := K) (V := V)).allB B = true := rfl
theorem SMap.allB_cons {K : PrimTy} {V : Ty} (k : K.Denote) (v : SVal V) (rest : SMap K V) :
    (SMap.cons k v rest).allB B = (v.allB B && rest.allB B) := rfl

end AllB

attribute [irreducible] SVal.allB SFields.allB SList.allB SVec.allB SMap.allB
attribute [eqns SVal.allB_prim SVal.allB_struct SVal.allB_array SVal.allB_fixed SVal.allB_map]
  SVal.allB
attribute [eqns SFields.allB_nil SFields.allB_cons] SFields.allB
attribute [eqns SList.allB_nil SList.allB_cons] SList.allB
attribute [eqns SVec.allB_nil SVec.allB_cons] SVec.allB
attribute [eqns SMap.allB_nil SMap.allB_cons] SMap.allB

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
  map _ := fun _ _ => true


/-! ## The storage's tests -/

/-- Every root canonical and tight. -/
def Storage.shapeB (st : Storage C) : Bool := SFields.allB canonHB st && SFields.allB tightHB st

/-- What `wt(storage)` tests: the shape. -/
def Storage.wtB (st : Storage C) : Bool := st.shapeB

end Solidity
