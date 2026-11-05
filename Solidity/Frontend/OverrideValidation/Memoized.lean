import Solidity.Frontend.OverrideValidation.Validator

/-! Materialized typed relation tables, proved equivalent to the original
candidate. Neither the independent judgment nor validateB is replaced. -/
namespace Solidity.Frontend.OverrideValidation
open Solidity.Source

def tableGet {α : Type} {n : Nat} (values : Vector α n) (i : Fin n) : α := values[i.val]

def bitTable {n : Nat} (f : Fin n → Bool) : Vector Bool n := Vector.ofFn f

def edgeTable {n : Nat} (f : Fin n → Fin n → Bool) : Vector (Vector Bool n) n :=
  Vector.ofFn fun i => Vector.ofFn (f i)

theorem bitTable_get {n : Nat} (f : Fin n → Bool) (i : Fin n) : tableGet (bitTable f) i = f i := by
  simp only [bitTable, tableGet, Vector.getElem_ofFn]

theorem edgeTable_get {n : Nat} (f : Fin n → Fin n → Bool) (i j : Fin n) :
    tableGet (tableGet (edgeTable f) i) j = f i j := by
  simp only [edgeTable, tableGet, Vector.getElem_ofFn]

theorem bitTable_get_fun {n : Nat} (f : Fin n → Bool) : tableGet (bitTable f) = f := by
  funext i
  exact bitTable_get f i

def tableAdjacentB (E : Env) (initial active : Node E → Bool)
    (edges : Node E → Node E → Bool) (a b : GraphVertex E) : Bool :=
  match realNode E a, realNode E b with
  | some d, some f => active d && active f && (edges d f || edges f d)
  | none, some f => (a == rootVertex E && initial f) ||
      (a == topVertex E && active f && !((nodes E).any fun g => edges f g))
  | some d, none => (b == rootVertex E && initial d) ||
      (b == topVertex E && active d && !((nodes E).any fun g => edges d g))
  | none, none => false

/-- A slot's tables are concrete vectors, not partially applied closures. -/
def memoRetainedTable (E : Env) (c key : Node E) : Vector Bool E.decls.length :=
  let initial := bitTable (overrideFrontierB E c key)
  let edges := edgeTable (overrideEdgeB E)
  let edge := fun a b => tableGet (tableGet edges a) b
  let active := bitTable fun (d : Node E) =>
    (nodes E).any fun root => tableGet initial root && routeB edge (nodes E) root d
  let adjacent := edgeTable (tableAdjacentB E (tableGet initial) (tableGet active) edge)
  let adj := fun a b => tableGet (tableGet adjacent a) b
  let cut := bitTable fun (v : Node E) => tableGet active v &&
    (vertices E).any fun a => a != realVertex v && (vertices E).any fun b =>
      b != realVertex v && routeB adj (vertices E) a b &&
      !routeB (fun x y => adj x y && x != realVertex v && y != realVertex v) (vertices E) a b
  bitTable fun (f : Node E) => tableGet initial f && (nodes E).all fun v => !tableGet cut v ||
    ((v == f || !routeB edge (nodes E) v f) && (v != f || implemented f.decl))

theorem memoRetainedTable_get (E : Env) (c key f : Node E) :
    tableGet (memoRetainedTable E c key) f = retainedB E c key f := by
  simp only [memoRetainedTable, bitTable_get, bitTable_get_fun, edgeTable_get]
  rfl

def fastAmbiguityB (E : Env) (c key : Node E) : Bool :=
  if hasOwnB E c key then true
  else if multipleB E c key then
    let kept := memoRetainedTable E c key
    !((nodes E).any fun f => tableGet kept f && (nodes E).any fun g => tableGet kept g && f != g)
  else true

theorem fastAmbiguityB_eq (E : Env) (c key : Node E) : fastAmbiguityB E c key = ambiguityB E c key := by
  cases ho : hasOwnB E c key with
  | true => simp only [fastAmbiguityB, ho, if_true, ambiguityB, Bool.true_or]
  | false =>
    cases hm : multipleB E c key with
    | true =>
      simp only [fastAmbiguityB, ho, Bool.false_eq_true, if_false, hm,
        if_true, memoRetainedTable_get, ambiguityB, Bool.false_or]
    | false =>
      simp only [fastAmbiguityB, ho, hm, Bool.false_eq_true, if_false]
      symm
      apply ambiguityB_iff.mpr
      right
      rintro ⟨f, g, hf, hg, hne⟩
      have ht : multipleB E c key = true := multipleB_iff.mpr ⟨f, g, hf.1, hg.1, hne⟩
      rw [hm] at ht
      cases ht

/-- Explicit optimized entry point, with an unconditional equality theorem. -/
def fastValidateB (E : Env) : Bool :=
  extractionB E && graphValidB E && (nodes E).all fun c => !contractB c.decl ||
    (memberNamesB E c && inheritedFamiliesB E c) && (nodes E).all fun key => !(family key.decl).isSome ||
      ((!ownB E c key || declarationOverridesB E c key) && fastAmbiguityB E c key && implementationB E c key)

theorem fastValidateB_eq (E : Env) : fastValidateB E = validateB E := by
  simp only [fastValidateB, fastAmbiguityB_eq]
  rfl

theorem fastValidateB_iff {E : Env} : fastValidateB E = true ↔ OverrideGraphOK E := by
  rw [fastValidateB_eq]
  exact validateB_iff

end Solidity.Frontend.OverrideValidation
