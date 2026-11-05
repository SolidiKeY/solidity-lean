import Solidity.Frontend.QualifiedUnits.Inheritance

/-! Qualified type-name paths used while normalizing signatures. Namespace
lookup reuses the existing finite name graph, independently of function
signature comparison, so type resolution cannot recurse through itself. -/
namespace Solidity.Frontend.QualifiedUnits.TypePaths
open Solidity.Source Solidity.Frontend.Static

def step (P : UnitSet) (R : List Remapping) (a : Sym) (x : String) : List Sym :=
  match a with
  | .unit u => P.globals R u x
  | .decl i => (inheritedMembers P R i x).map Sym.decl

def head (P : UnitSet) (R : List Remapping) (u : String) (scope : Option DeclId)
    (x : String) : List Sym :=
  match scope with
  | none => P.globals R u x
  | some i =>
    let localNames := inheritedMembers P R i x
    if localNames = [] then P.globals R u x else localNames.map Sym.decl

/-- Every prefix and the terminal identify one original symbol. -/
inductive Route (P : UnitSet) (R : List Remapping) : List Sym → List String → Sym → Prop where
  | done {L : List Sym} {a : Sym} : a ∈ L → (∀ b, b ∈ L → b = a) → Route P R L [] a
  | next {L : List Sym} {a b : Sym} {x : String} {xs : List String} :
      a ∈ L → (∀ c, c ∈ L → c = a) → Route P R (step P R a x) xs b →
      Route P R L (x :: xs) b

def tail (P : UnitSet) (R : List Remapping) : List Sym → List String → Option Sym
  | L, [] => uniqueSymbol L
  | L, x :: xs => (uniqueSymbol L).bind fun a => tail P R (step P R a x) xs

theorem tail_iff {P : UnitSet} {R : List Remapping} {L : List Sym} {xs : List String} {a : Sym} :
    tail P R L xs = some a ↔ Route P R L xs a := by
  induction xs generalizing L with
  | nil =>
    rw [tail, uniqueSymbol_iff]
    exact ⟨fun h => .done h.1 h.2, fun h => by cases h with | done h u => exact ⟨h,u⟩⟩
  | cons x xs ih =>
    simp only [tail, Option.bind_eq_some_iff]
    constructor
    · rintro ⟨b,hb,ht⟩
      obtain ⟨hm,hu⟩ := uniqueSymbol_iff.mp hb
      exact .next hm hu (ih.mp ht)
    · intro h
      cases h with
      | next hm hu ht => exact ⟨_,uniqueSymbol_iff.mpr ⟨hm,hu⟩,ih.mpr ht⟩

def lookup (P : UnitSet) (R : List Remapping) (u : String) (scope : Option DeclId)
    (path : IdPath) : Option DeclId :=
  match tail P R (head P R u scope path.head) path.tail with
  | some (.decl i) => some i
  | _ => none

theorem lookup_iff {P : UnitSet} {R : List Remapping} {u : String} {scope : Option DeclId}
    {path : IdPath} {i : DeclId} :
    lookup P R u scope path = some i ↔ Route P R (head P R u scope path.head) path.tail (.decl i) := by
  unfold lookup
  cases ht : tail P R (head P R u scope path.head) path.tail with
  | none => simp only [reduceCtorEq, false_iff]; intro h; rw [tail_iff.mpr h] at ht; cases ht
  | some a =>
    cases a with
    | unit v => simp only [reduceCtorEq, false_iff]; intro h; rw [tail_iff.mpr h] at ht; cases ht
    | decl j =>
      constructor
      · intro h; cases Option.some.inj h; exact tail_iff.mp ht
      · intro h; have same := ht.symm.trans (tail_iff.mpr h); cases Option.some.inj same; rfl

end Solidity.Frontend.QualifiedUnits.TypePaths
