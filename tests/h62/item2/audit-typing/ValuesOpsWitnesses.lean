import tests.h62.item2.«audit-typing».ValuesDefaultsWitnesses

namespace H62.AuditTyping.ValuesOpsWitnesses
open Solidity
open H62.AuditTyping.ValuesDefaultsWitnesses (truthH)

def stripTruth : truthH.StripOK := by
  intro _E _n _e _sh _hp _he
  exact True.intro

def deleteTruth : truthH.DelOK := by
  intro _E _n _e _sh _hp _he
  exact True.intro

def overlayTruth : truthH.OvOK := by
  intro _E _m _n _oe _os _ne _ns _ho _hn _he _hs _hne
  exact True.intro

abbrev arrayTy : Ty := .ref (.array (.prim .bool))
def arrayValue (live shadow : Bool) : SVal arrayTy :=
  .array (.cons (.prim live) .nil) (.cons (.prim shadow) .nil) (by decide)

theorem array_all (live shadow : Bool) : (arrayValue live shadow).All truthH := by
  simp only [arrayValue, SVal.All_array, SVec.All_cons, SVec.All_nil,
    SList.All_cons, SList.All_nil, SVal.All_prim, truthH, true_and]

def row (live shadow : Bool) : SFields [("a", arrayTy)] :=
  .cons (arrayValue live shadow) .nil

theorem row_all (live shadow : Bool) : (row live shadow).All truthH := by
  simp only [row, SFields.All_cons, SFields.All_nil, array_all, true_and]

def vector (live shadow : Bool) : SVec arrayTy 1 := .cons (arrayValue live shadow) .nil

theorem vector_all (live shadow : Bool) : (vector live shadow).All truthH := by
  simp only [vector, SVec.All_cons, SVec.All_nil, array_all, true_and]

theorem val_strip : ∃ (P : Hered), ∃ (_hs : P.StripOK),
    ∃ (T : Ty) (v : SVal T), ∃ (_hv : v.All P), True :=
  ⟨truthH, stripTruth, arrayTy, arrayValue false true, array_all false true, True.intro⟩

theorem fields_strip : ∃ (P : Hered), ∃ (_hs : P.StripOK),
    ∃ (fs : List (Solidity.Name × Ty)) (x : SFields fs), ∃ (_hx : x.All P), True :=
  ⟨truthH, stripTruth, [("a", arrayTy)], row false true, row_all false true, True.intro⟩

theorem vec_strip : ∃ (P : Hered), ∃ (_hs : P.StripOK),
    ∃ (E : Ty) (n : Nat) (e : SVec E n), ∃ (_he : e.All P), True :=
  ⟨truthH, stripTruth, arrayTy, 1, vector false true, vector_all false true, True.intro⟩

theorem val_delete : ∃ (P : Hered), ∃ (_hd : P.DelOK),
    ∃ (T : Ty) (v : SVal T), ∃ (_hv : v.All P), True :=
  ⟨truthH, deleteTruth, arrayTy, arrayValue false true, array_all false true, True.intro⟩

theorem fields_delete : ∃ (P : Hered), ∃ (_hd : P.DelOK),
    ∃ (fs : List (Solidity.Name × Ty)) (x : SFields fs), ∃ (_hx : x.All P), True :=
  ⟨truthH, deleteTruth, [("a", arrayTy)], row false true, row_all false true, True.intro⟩

theorem vec_delete : ∃ (P : Hered), ∃ (_hd : P.DelOK),
    ∃ (E : Ty) (n : Nat) (e : SVec E n), ∃ (_he : e.All P), True :=
  ⟨truthH, deleteTruth, arrayTy, 1, vector false true, vector_all false true, True.intro⟩

theorem val_overlay : ∃ (P : Hered), ∃ (_hs : P.StripOK) (_hd : P.DelOK) (_hov : P.OvOK),
    ∃ (T : Ty) (o v : SVal T), ∃ (_ho : o.All P) (_hv : v.All P), True :=
  ⟨truthH, stripTruth, deleteTruth, overlayTruth, arrayTy, arrayValue false true,
    arrayValue true false, array_all false true, array_all true false, True.intro⟩

theorem fields_overlay : ∃ (P : Hered), ∃ (_hs : P.StripOK) (_hd : P.DelOK) (_hov : P.OvOK),
    ∃ (fs : List (Solidity.Name × Ty)) (os ns : SFields fs),
    ∃ (_ho : os.All P) (_hn : ns.All P), True :=
  ⟨truthH, stripTruth, deleteTruth, overlayTruth, [("a", arrayTy)], row false true,
    row true false, row_all false true, row_all true false, True.intro⟩

theorem vec_overlay : ∃ (P : Hered), ∃ (_hs : P.StripOK) (_hd : P.DelOK) (_hov : P.OvOK),
    ∃ (E : Ty) (n : Nat) (L : List (SVal E)), ∃ (_hL : ∀ w ∈ L, w.All P),
    ∃ (e : SVec E n), ∃ (_he : e.All P), True := by
  refine ⟨truthH, stripTruth, deleteTruth, overlayTruth, arrayTy, 1,
    [arrayValue false true], ?_, vector true false, vector_all true false, True.intro⟩
  intro w hw
  have e : w = arrayValue false true := List.mem_singleton.mp hw
  subst w
  exact array_all false true

def rejectArrayH : Hered where
  arr := fun _ _ => False
  fix := fun _ _ => True
  map := fun _ {_} _ _ => True

-- A globally inhabited predicate record does not make this input feasible.
theorem reject_array_not_all : ¬ (arrayValue false true).All rejectArrayH := by
  intro h
  have hc := Eq.mp (SVal.All_array (P := rejectArrayH) (E := .prim .bool)
    (SVec.cons (SVal.prim (p := .bool) false) SVec.nil)
    (SList.cons (SVal.prim (p := .bool) true) SList.nil) (by decide)) h
  exact hc.1

end H62.AuditTyping.ValuesOpsWitnesses
