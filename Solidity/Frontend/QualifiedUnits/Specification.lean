import Solidity.Frontend.QualifiedUnits.Inheritance

/-! Independent lexical-head and accepted qualified-path judgments. The
relations below do not call the qualified checker. G13 retains expression
typing/access control and overload selection; G14 retains inheritance
validity and C3/override checks. -/
namespace Solidity.Frontend.QualifiedUnits
open Solidity.Source

/-- Namespace step including inherited declaration names. -/
inductive NamespaceStep (P : UnitSet) (R : List Remapping) : Sym → String → Sym → Prop where
  | unit {u x : String} {s : Sym} : Sees P R u x s → NamespaceStep P R (.unit u) x s
  | decl {i j : DeclId} {x : String} : InheritedMember P R i x j → NamespaceStep P R (.decl i) x (.decl j)

/-- Lexical declaration head: contract members precede the importing unit's
globals. Locals are tested by `Resolved` before this relation is used. -/
inductive Head (P : UnitSet) (R : List Remapping) (u : String) (scope : Option DeclId)
    (x : String) : Sym → Prop where
  | member {i j : DeclId} : scope = some i → InheritedMember P R i x j → Head P R u scope x (.decl j)
  | global {s : Sym} : (∀ i, scope = some i → ¬ ∃ j, InheritedMember P R i x j) →
      Sees P R u x s → Head P R u scope x s

/-- Two distinct declarations may share a terminal name only as an overload
set of functions or events of the same kind. This is a proposition over
original declaration data, not a call to the no-clash checker. -/
def Overloadable (P : UnitSet) (a b : Sym) : Prop :=
  match a, b with
  | .decl i, .decl j =>
    match P.decl? i, P.decl? j with
    | some d, some e => d.kind = e.kind ∧ d.kind.overloads = true
    | _, _ => False
  | _, _ => False

/-- Identity duplicates are harmless, even along separate import routes. -/
def Compatible (P : UnitSet) (a b : Sym) : Prop := a = b ∨ Overloadable P a b

def Coherent (P : UnitSet) (S : Sym → Prop) : Prop :=
  ∀ a b, S a → S b → Compatible P a b

/-- A terminal can be an overload set; every proper namespace prefix has
one identity. Missing or ambiguous prefixes have no derivation, even when
several conflicting routes would later converge to the same declaration. -/
inductive Admits (P : UnitSet) (R : List Remapping) : (Sym → Prop) → List String → Sym → Prop where
  | terminal {S : Sym → Prop} {s : Sym} : S s → Coherent P S → Admits P R S [] s
  | next {S : Sym → Prop} {a s : Sym} {x : String} {xs : List String} :
      S a → (∀ b, S b → b = a) → Admits P R (NamespaceStep P R a x) xs s →
      Admits P R S (x :: xs) s

/-- Lexical scope belongs to the queried unit and identifies a container. -/
def ValidScope (P : UnitSet) (u : String) : Option DeclId → Prop
  | none => True
  | some i => i.unit = u ∧ match P.decl? i with
      | none => False
      | some d => Container d.kind

instance instDecidableValidScope (P : UnitSet) (u : String) (scope : Option DeclId) :
    Decidable (ValidScope P u scope) := by
  cases scope with
  | none => exact isTrue True.intro
  | some i =>
    unfold ValidScope
    simp only
    cases P.decl? i <;> simp only <;> infer_instance

/-- Independent accepted declaration resolution, including local shadowing.
A local head is deliberately left to G13's expression typing; it cannot be
reinterpreted as an imported namespace by declaration resolution. -/
def Resolved (P : UnitSet) (R : List Remapping) (u : String) (scope : Option DeclId)
    (locals : List String) (p : IdPath) (s : Sym) : Prop :=
  ValidScope P u scope ∧ locals.idxOf? p.head = none ∧ Admits P R (Head P R u scope p.head) p.tail s

/-- An accepted namespace prefix cannot contain a second identity. -/
theorem Admits.prefix_unique {P : UnitSet} {R : List Remapping} {S : Sym → Prop}
    {x : String} {xs : List String} {s : Sym} (h : Admits P R S (x :: xs) s) :
    ∃ a, S a ∧ ∀ b, S b → b = a := by
  cases h with
  | next ha hu _ => exact ⟨_, ha, hu⟩

/-- Accepted terminal answers preserve no-clash, including duplicate and
converging identity routes. -/
theorem Admits.coherent {P : UnitSet} {R : List Remapping} {S : Sym → Prop}
    {xs : List String} {s t : Sym} (h : Admits P R S xs s) (k : Admits P R S xs t) :
    Compatible P s t := by
  induction xs generalizing S with
  | nil =>
    cases h with
    | terminal hs hc => cases k with
      | terminal ht _ => exact hc s t hs ht
  | cons x xs ih =>
    cases h with
    | next ha hu hs => cases k with
      | next hb _ ht =>
        have e := hu _ hb
        subst e
        exact ih hs ht

/-- Local shadowing blocks every declaration-namespace interpretation. -/
theorem local_shadows {P : UnitSet} {R : List Remapping} {u : String} {scope : Option DeclId}
    {locals : List String} {p : IdPath} {i : Nat} {s : Sym}
    (h : locals.idxOf? p.head = some i) : ¬ Resolved P R u scope locals p s := by
  intro ⟨_, hn, _⟩
  rw [h] at hn
  cases hn

end Solidity.Frontend.QualifiedUnits
