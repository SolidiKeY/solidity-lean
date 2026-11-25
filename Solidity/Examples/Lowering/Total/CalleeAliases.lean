import Solidity.Correctness.Lowering.Total.CalleeAliases

/-! Model callee aliases against assembled Source declarations: model aliases
different from retained source names, duplicate aliases resolved by first
match, missing metadata failing assembly, and one source name retained by two
entries, where assembly succeeds but `DeclaredUniquely` does not hold. Execution
is not checked. -/
namespace Solidity.Examples.Lowering.Total.CalleeAliases

open Solidity.Correctness.Lowering.Total Solidity.Correctness.Lowering.Total.Decode
open Solidity.Correctness.Lowering.Total.CalleeAliases
open Semantics (lookupBy)

/-- `function NAME() internal {}` with retained source identity. -/
def fn (name : String) : FunDecl :=
  { sourceDecl := some { name, callable := .local .internalFn }, params := [], body := [] }
/-- The same entry with no retained source metadata. -/
def bare : FunDecl := { params := [], body := [] }

/-- Model aliases `get_0`/`set_1` differ from source names `get`/`set`. -/
def renamed : List (Name × FunDecl) := [("get_0", fn "get"), ("set_1", fn "set")]
/-- Alias `f` twice: the first entry is `first`, the shadowed one `second`. -/
def dup : List (Name × FunDecl) := [("g", fn "other"), ("f", fn "first"), ("f", fn "second")]
/-- Overloads: two aliases, one retained source name `h`. -/
def overload : List (Name × FunDecl) := [("h_0", fn "h"), ("h_1", fn "h")]

def unitOf (fs : List (Name × FunDecl)) : Option (Source.Syn .unit) :=
  Callee.withFunctions tablesS [] "C" .nil fs
/-- The table entry the alias lookup lands on: name and scope at `entryPosition`. -/
def landing (fs : List (Name × FunDecl)) (a : Name) : Option (String × Option String) := do
  let u ← unitOf fs
  let i ← firstIndex a fs
  let d ← u.decls[entryPosition "C" .nil i]?
  pure (d.name, d.scope)
def declaredCount (fs : List (Name × FunDecl)) (x : String) : Option Nat :=
  (unitOf fs).map fun u => (u.env.declared (some "C") x).length

/-! Distinct model and source names: the alias selects the entry, the
declaration carries the source name; the alias itself declares nothing. -/
#guard landing renamed "get_0" == some ("get", some "C")
#guard landing renamed "set_1" == some ("set", some "C")
#guard declaredCount renamed "get_0" == some 0
#guard declaredCount renamed "get" == some 1
/-! Duplicate aliases: first match at position 1, the later entry shadowed. -/
#guard firstIndex "f" dup == some 1
#guard landing dup "f" == some ("first", some "C")
#guard declaredCount dup "second" == some 1
/-! Absent alias and absent metadata. -/
#guard firstIndex "missing" dup == none
#guard landing dup "missing" == none
#guard (unitOf [("get", fn "get"), ("bare", bare)]).isNone
/-! Overloads: assembly succeeds yet the source name has two candidates. -/
#guard (unitOf overload).isSome
#guard declaredCount overload "h" == some 2

example : lookupBy "f" dup = some (fn "first") := rfl
example : lookupBy "missing" dup = none :=
  Iff.mpr alias_none (by simp [dup])
example : firstIndex "f" dup = some 1 := rfl
/-- Any first-match position of `f` lies strictly before the shadowed `second`. -/
example {i} (hf : firstIndex "f" dup = some i) : i < 2 := by
  have h1 : firstIndex "f" dup = some 1 := rfl
  exact alias_shadowed (j := 2) (d' := fn "second") hf rfl (by rw [h1] at hf; cases hf; decide)
/-- Missing metadata fails assembly whatever the alias. -/
example : unitOf [("get", fn "get"), ("bare", bare)] = none :=
  withFunctions_absent (e := ("bare", bare)) (by simp) rfl
/-- Renaming every alias leaves the unit unchanged. -/
example : unitOf (renamed.map fun e => (e.1 ++ "'", e.2)) = unitOf renamed :=
  withFunctions_relabel _

/-- From any successful assembly of `dup`, the lookup of `f` lands on the
declaration named `first` in scope `C`, not the alias and not `second`. -/
example {u} (hu : unitOf dup = some u) :
    ∃ out, u.decls[entryPosition "C" .nil 1]? = some out ∧
      out.name = "first" ∧ out.scope = some "C" := by
  obtain ⟨i, out, source, hi, _, hp, _, hs, hn, hsc, _⟩ := alias_entry hu (a := "f") rfl
  cases hi; cases hs
  exact ⟨out, hp, hn, hsc⟩

/-- Overloads: the declaration `h_0` lands on is named `h`, yet it fails the
name-resolution obligation, though assembly succeeded. -/
example {u} (hu : unitOf overload = some u) :
    ∃ out, u.decls[entryPosition "C" .nil 0]? = some out ∧ out.name = "h" ∧
      ¬ DeclaredUniquely u "C" out := by
  obtain ⟨i, out, source, hi, _, hp, _, hs, hn, hsc, _⟩ := alias_entry hu (a := "h_0") rfl
  cases hi; cases hs
  obtain ⟨out', source', hp', _, hs', hn', hsc', _⟩ :=
    withFunctions_identity hu (index := 1) (e := ("h_1", fn "h")) rfl
  cases hs'
  refine ⟨out, hp, hn, fun h => ?_⟩
  have := h.position_unique (by simp [hn]) hp rfl (by simpa using hsc) hp' (hn'.trans hn.symm)
    (by simpa using hsc')
  simp [entryPosition, Source.Syn.collect] at this

/-- First-match shadowing as a list fact: `first` is preceded only by `g`. -/
example : lookupBy "f" dup = some (fn "first") :=
  lookupBy_shadow [("g", fn "other")] [("f", fn "second")] (by simp)

/-- Without the obligation, `get_0`'s declaration is a Source candidate under
the source name `get`, never under the alias. -/
example {u} (hu : unitOf renamed = some u) :
    ∃ out, out.name = "get" ∧ out ∈ u.env.declared (some "C") "get" := by
  obtain ⟨out, source, _, hs, hn, hd⟩ := alias_declared hu (a := "get_0") rfl
  cases hs
  exact ⟨out, hn, hd (by decide)⟩

/-- Under the obligation, every candidate is the landing declaration. -/
example {u : Source.Syn .unit} {out d' : Source.Decl} (h : DeclaredUniquely u "C" out)
    (hd : d' ∈ u.env.declared (some "C") out.name) : d' = out :=
  DeclaredUniquely.unique h hd

/-- Binding at the first-match position of `f` selects `first`, not `second`. -/
example {settings s}
    (h : Version.CalleeBinding.fromFunctions tablesS [] settings "C" .nil dup 1 = some s) :
    s.declaration.name = "first" ∧ s.declaration.scope = some "C" := by
  obtain ⟨d, source, _, _, hi, hs, hn, hsc, _⟩ := fromFunctions_alias (a := "f") rfl h
  cases hi; cases hs
  exact ⟨hn, hsc⟩

end Solidity.Examples.Lowering.Total.CalleeAliases
