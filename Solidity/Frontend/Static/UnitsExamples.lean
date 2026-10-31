import Solidity.Frontend.Static.Units
import Solidity.Frontend.Static.Overloads

/-!
# G12 controls: imports, identities, shadowing and overloads

Hand-written S00 trees, each control computed by the kernel (`decide`):

| Theorem | Statement |
|---|---|
| `cycle_resolves`, `cycle_ok` | `a.sol` and `b.sol` import each other: each sees the other's contract; the check terminates and accepts |
| `diamond_one_identity`, `diamond_ok` | `D` reached through `b.sol` and `c.sol` is one identity, no clash |
| `clash_refused` | two different `T` imported into one unit: refused |
| `alias_renames`, `alias_hides_original` | `import {T as U}` binds `U`, not `T` |
| `missing_refused` | an import of an absent unit: refused |
| `remapped`, `relative_parent` | remapping and `..` resolution |
| `missingSym_refused`, `aliasCycle_empty`, `aliasCycle_refused` | an imported symbol that does not exist, and a cycle of aliases: refused |
| `freeOverloads_ok`, `freeOverloads_both`, `fnEvent_refused` | free functions from two units overload; a function and an event of one name clash |
| `namespace_binds` | `import "x.sol" as N` binds `N` to the unit (re-exported), not `x.sol`'s names |
| `shadowed_member`, `shadowed_global`, `shadow_ok` | in contract `C` the member `T` shadows the file-level contract `T` (S01's lookup); at file level `T` is the contract |
| `ambiguous_refused`, `exact_selected` | `f(uint8)`/`f(uint16)` called with `1`: two fit, refused; with a `uint16` exactly `f(uint16)` is selected |
| `crossBase_merged`, `crossBase_s01`, `override_hides` | overloads split between `B` and its base `A` form one set (S01's lookup sees only `B`'s); an override hides the base function |
-/

namespace Solidity.Frontend.Static.UnitsExamples

open Solidity.Source
open Solidity.Frontend.Static

/-- `contract N {}` -/
def emptyContract (n : String) : Syn .top := .contract false n .none .nil .nil

/-- A unit from its top-level elements. -/
def mkUnit : List (Syn .top) → Syn .unit
  | xs => .unit (xs.foldr (fun x acc => .cons x acc) .nil)

/-! ## An import cycle -/

def cycle : UnitSet := ⟨[
  ("a.sol", mkUnit [.importPath "./b.sol" Option.none, emptyContract "A"]),
  ("b.sol", mkUnit [.importPath "./a.sol" Option.none, emptyContract "B"])]⟩

/-- Each unit of the cycle sees the other's contract, and its own. -/
theorem cycle_resolves :
    cycle.globals [] "a.sol" "B" = [.decl ⟨"b.sol", 0⟩] ∧
    cycle.globals [] "b.sol" "A" = [.decl ⟨"a.sol", 0⟩] ∧
    cycle.globals [] "a.sol" "A" = [.decl ⟨"a.sol", 0⟩] := by decide

theorem cycle_ok : UnitsOK cycle [] := unitsOK_iff.mp (by decide)

/-! ## A diamond: one identity along two routes -/

def diamond : UnitSet := ⟨[
  ("d.sol", mkUnit [emptyContract "D"]),
  ("b.sol", mkUnit [.importPath "d.sol" Option.none]),
  ("c.sol", mkUnit [.importPath "d.sol" Option.none]),
  ("a.sol", mkUnit [.importPath "b.sol" Option.none, .importPath "c.sol" Option.none])]⟩

theorem diamond_one_identity : diamond.globals [] "a.sol" "D" = [.decl ⟨"d.sol", 0⟩] := by decide

theorem diamond_ok : UnitsOK diamond [] := unitsOK_iff.mp (by decide)

/-! ## A clash, an alias, a missing unit -/

def clash : UnitSet := ⟨[
  ("x.sol", mkUnit [emptyContract "T"]),
  ("y.sol", mkUnit [emptyContract "T"]),
  ("a.sol", mkUnit [.importPath "x.sol" Option.none, .importPath "y.sol" Option.none])]⟩

/-- **Negative control**: two different declarations named `T` in one
file-level scope. -/
theorem clash_refused : ¬ UnitsOK clash [] := fun h => by
  have e := unitsOK_iff.mpr h
  revert e
  decide

def aliased : UnitSet := ⟨[
  ("x.sol", mkUnit [emptyContract "T"]),
  ("a.sol", mkUnit [.importSymbols (.importAlias "T" (Option.some "U")) .nil "x.sol"])]⟩

theorem alias_renames : aliased.globals [] "a.sol" "U" = [.decl ⟨"x.sol", 0⟩] := by decide

theorem alias_hides_original : aliased.globals [] "a.sol" "T" = [] := by decide

def missing : UnitSet := ⟨[("a.sol", mkUnit [.importPath "nowhere.sol" Option.none])]⟩

/-- **Negative control**: an import of an absent unit. -/
theorem missing_refused : ¬ UnitsOK missing [] := fun h => by
  have e := unitsOK_iff.mpr h
  revert e
  decide

/-- **Negative control**: `import {Nope} from "x.sol"` names no declaration
of `x.sol` (solc error 2904). -/
def missingSym : UnitSet := ⟨[
  ("x.sol", mkUnit [emptyContract "T"]),
  ("a.sol", mkUnit [.importSymbols (.importAlias "Nope" Option.none) .nil "x.sol"])]⟩

theorem missingSym_refused : ¬ UnitsOK missingSym [] := fun h => by
  have e := unitsOK_iff.mpr h
  revert e
  decide

/-- **Negative control**: `a.sol` takes `y` from `b.sol` as `x`, `b.sol`
takes `x` from `a.sol` as `y`: the aliases denote nothing. -/
def aliasCycle : UnitSet := ⟨[
  ("a.sol", mkUnit [.importSymbols (.importAlias "y" (Option.some "x")) .nil "b.sol"]),
  ("b.sol", mkUnit [.importSymbols (.importAlias "x" (Option.some "y")) .nil "a.sol"])]⟩

theorem aliasCycle_empty : aliasCycle.globals [] "a.sol" "x" = [] := by decide

theorem aliasCycle_refused : ¬ UnitsOK aliasCycle [] := fun h => by
  have e := unitsOK_iff.mpr h
  revert e
  decide

/-- `function f(p) {}` at file level. -/
def freeFn (p : Syn .param) : Syn .top :=
  .topPart (.function (t := true) (.ident "f") (.cons p .nil) Option.none Option.none .nil false
    Option.none .nil (.some (.block .nil)))

/-- `event f();` at file level. -/
def freeEvent : Syn .top := .topPart (.event (t := true) "f" .nil false)

def boolP : Syn .param := .param (.elem .bool) Option.none (Option.some "b")
def u8P : Syn .param := .param (.elem (.int false 8 (by decide))) Option.none (Option.some "v")

/-- Free functions `f(bool)` and `f(uint8)` from two units overload in a
third. -/
def freeOverloads : UnitSet := ⟨[
  ("x.sol", mkUnit [freeFn boolP]),
  ("y.sol", mkUnit [freeFn u8P]),
  ("a.sol", mkUnit [.importPath "x.sol" Option.none, .importPath "y.sol" Option.none])]⟩

theorem freeOverloads_ok : UnitsOK freeOverloads [] := unitsOK_iff.mp (by decide)

theorem freeOverloads_both :
    freeOverloads.globals [] "a.sol" "f" = [.decl ⟨"x.sol", 0⟩, .decl ⟨"y.sol", 0⟩] := by decide

/-- **Negative control**: a free function and an event named `f` in one scope. -/
def fnEvent : UnitSet := ⟨[
  ("x.sol", mkUnit [freeFn boolP]),
  ("y.sol", mkUnit [freeEvent]),
  ("a.sol", mkUnit [.importPath "x.sol" Option.none, .importPath "y.sol" Option.none])]⟩

theorem fnEvent_refused : ¬ UnitsOK fnEvent [] := fun h => by
  have e := unitsOK_iff.mpr h
  revert e
  decide

/-- `import "x.sol" as N;` binds `N` to the unit, re-exported by `import "a.sol"`. -/
def namespaced : UnitSet := ⟨[
  ("x.sol", mkUnit [emptyContract "T"]),
  ("a.sol", mkUnit [.importPath "x.sol" (Option.some "N")]),
  ("b.sol", mkUnit [.importPath "a.sol" Option.none])]⟩

theorem namespace_binds :
    namespaced.globals [] "b.sol" "N" = [.unit "x.sol"] ∧ namespaced.globals [] "a.sol" "T" = [] := by
  decide

/-! ## Paths -/

theorem remapped :
    UnitSet.target [{ pre := "lib/", target := "vendor/lib/" }] "src/a.sol" "lib/x.sol" =
      "vendor/lib/x.sol" := by decide

theorem relative_parent : UnitSet.target [] "src/a/b.sol" "../x.sol" = "src/x.sol" := by decide

/-- The longer context wins over the longer prefix. -/
theorem remap_context :
    UnitSet.target [{ context := "src/", pre := "lib/", target := "ctx/" },
      { pre := "lib/x", target := "long/" }] "src/a.sol" "lib/x.sol" = "ctx/x.sol" := by decide

/-! ## Shadowing -/

/-- `uint256 x;` as a state variable. -/
def uintVar (x : String) : Syn (.part false) :=
  .stateVar (.elem (.int false 256 (by decide))) Option.none Option.none Option.none false x .none

/-- A file-level contract `T` and a member `T` of contract `C`, one unit. -/
def shadowUnit : Syn .unit := mkUnit [emptyContract "T",
  .contract false "C" .none .nil (.cons (uintVar "T") .nil)]

def shadow : UnitSet := ⟨[("a.sol", shadowUnit)]⟩

/-- Inside `C`, `T` is the member: it shadows the file-level contract (solc
warns, 2519, and resolves to the member). -/
theorem shadowed_member :
    ((Syn.env shadowUnit).lookup (Option.some "C") "T").map (fun d => (d.kind, d.scope)) =
      [(.stateVar, Option.some "C")] := by decide

/-- At file level `T` is the contract, and the member is no file-level name. -/
theorem shadowed_global : shadow.globals [] "a.sol" "T" = [.decl ⟨"a.sol", 0⟩] := by decide

theorem shadow_ok : UnitsOK shadow [] := unitsOK_iff.mp (by decide)

/-! ## Overloads -/

/-- A parameter of an integer type. -/
def intParam (bits : Nat) (h : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) : Syn .param :=
  .param (.elem (.int false bits h)) Option.none (Option.some "v")

/-- `function f(p) internal {}` -/
def fn (name : String) (p : Syn .param) (override : Bool := false) : Syn (.part false) :=
  .function (.ident name) (.cons p .nil) (Option.some .internal) Option.none .nil (!override)
    (if override then Option.some [] else Option.none) .nil (.some (.block .nil))

def overloadUnit : Syn .unit := mkUnit [.contract false "C" .none .nil
  (.cons (fn "f" (intParam 8 (by decide))) (.cons (fn "f" (intParam 16 (by decide))) .nil))]

def u16 : STy := .int ⟨false, 16, by decide⟩

/-- **Negative control**: `f(1)` fits both `f(uint8)` and `f(uint16)`, so the
call is refused. -/
theorem ambiguous_refused :
    (((Syn.env overloadUnit).inheritedFns "C" "f").filter
        (accepts (Syn.env overloadUnit) (Syn.env overloadUnit).isBase [.rational (Q.ofInt 1)])).length = 2 ∧
    (selectOverload (Syn.env overloadUnit) (Syn.env overloadUnit).isBase
      ((Syn.env overloadUnit).inheritedFns "C" "f") [.rational (Q.ofInt 1)]).isNone = true := by
  decide

/-- With a `uint16` argument exactly `f(uint16)` is selected. -/
theorem exact_selected :
    ((selectOverload (Syn.env overloadUnit) (Syn.env overloadUnit).isBase
      ((Syn.env overloadUnit).inheritedFns "C" "f") [u16]).bind
        (fun d => paramsOf (Syn.env overloadUnit) d)).map (STy.sameList [u16]) = Option.some true := by
  decide

/-- `bool b` -/
def boolParam : Syn .param := .param (.elem .bool) Option.none (Option.some "b")

def crossBase : Syn .unit := mkUnit [
  .contract false "A" .none .nil (.cons (fn "f" (intParam 256 (by decide))) .nil),
  .contract false "B" .none (.cons (.inherit ⟨"A", []⟩ .none) .nil) (.cons (fn "f" boolParam) .nil)]

/-- Both overloads of `f` are callable in `B`. -/
theorem crossBase_merged :
    ((Syn.env crossBase).inheritedFns "B" "f").map Decl.scope = [Option.some "B", Option.some "A"] := by
  decide

/-- S01's lookup sees only `B`'s (the gap this closes). -/
theorem crossBase_s01 :
    ((Syn.env crossBase).lookup (Option.some "B") "f").map Decl.scope = [Option.some "B"] := by decide

def overriding : Syn .unit := mkUnit [
  .contract false "A" .none .nil (.cons (fn "f" (intParam 256 (by decide))) .nil),
  .contract false "B" .none (.cons (.inherit ⟨"A", []⟩ .none) .nil)
    (.cons (fn "f" (intParam 256 (by decide)) true) .nil)]

/-- An override hides the base function with its parameter types. -/
theorem override_hides :
    ((Syn.env overriding).inheritedFns "B" "f").map Decl.scope = [Option.some "B"] := by decide

end Solidity.Frontend.Static.UnitsExamples

/-- info: 'Solidity.Frontend.Static.iter_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.iter_complete
/-- info: 'Solidity.Frontend.Static.globals_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.globals_sound
/-- info: 'Solidity.Frontend.Static.globals_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.globals_complete
/-- info: 'Solidity.Frontend.Static.unitsOK_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.unitsOK_iff
/-- info: 'Solidity.Frontend.Static.globals_lookup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.globals_lookup
/-- info: 'Solidity.Frontend.Static.mem_inheritedFns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.mem_inheritedFns
/-- info: 'Solidity.Frontend.Static.UnitsExamples.cycle_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.UnitsExamples.cycle_ok
/-- info: 'Solidity.Frontend.Static.UnitsExamples.clash_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.UnitsExamples.clash_refused
/-- info: 'Solidity.Frontend.Static.UnitsExamples.ambiguous_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.UnitsExamples.ambiguous_refused
/-- info: 'Solidity.Frontend.Static.UnitsExamples.crossBase_merged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.UnitsExamples.crossBase_merged
/-- info: 'Solidity.Frontend.Static.lookup_sub_globals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.lookup_sub_globals
/-- info: 'Solidity.Frontend.Static.lookup_sub_inheritedFns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.lookup_sub_inheritedFns
/-- info: 'Solidity.Frontend.Static.UnitsExamples.missingSym_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.UnitsExamples.missingSym_refused
/-- info: 'Solidity.Frontend.Static.UnitsExamples.fnEvent_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.UnitsExamples.fnEvent_refused
