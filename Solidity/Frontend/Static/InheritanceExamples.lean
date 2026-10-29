import Solidity.Frontend.Static.Inheritance
import Solidity.Frontend.Static.C3
import Solidity.Source.TypingExamples

/-!
# G14 controls, cross-checked with solc's syntax tests

Each control transcribes a test of the pinned solc 0.8.38 test tree
(`tests/upstream/solidity-0.8.38.tar.gz`,
`test/libsolidity/syntaxTests/{inheritance,nameAndTypeResolution}/`) as S00
syntax and computes the checker's verdict in the kernel (`decide`); the
expected verdict is the test's own expectation block.  Function bodies are
empty (they do not bear on these checks).

| Theorem | Upstream test | solc's verdict |
|---|---|---|
| `missingVirtual_refused` | `inheritance/override/override_missing_virtual.sol` | 9456 (`test`), 4334 (`test2`) |
| `override_ok` | `inheritance/override/override.sol` | accepted |
| `lessStrict_refused` | `inheritance/override/override_less_strict_mutability.sol` (contracts `A`, `C`) | 6959 |
| `stricter_ok` | `inheritance/override/override_stricter_mutability.sol` (contracts `A`, `B`) | accepted |
| `noCommonBase_refused` | `inheritance/override/no_common_base_and_unique_implementation.sol` | 6480 (`f`, `g`) |
| `sharedBase_ok` | `inheritance/override/override_shared_base_simple.sol` | accepted |
| `sharedBase_override_ok`, `sharedBase_unlisted_refused` | `inheritance/override/override_shared_base.sol`; the same with `override` but no list | accepted; 4327 |
| `externalPublic_ok` | `inheritance/override/external_turns_public_no_params.sol` | accepted |
| `unimplementedNonVirtual_refused` | `inheritance/unimplemented_without_virtual.sol` | 5424 |
| `abstractNeeded_refused` | `nameAndTypeResolution/029_create_abstract_contract.sol` (contract `base`) | 3656 |
| `argsTwice_refused` | `inheritance/duplicatedConstructorCall/` (`B is A(2) { constructor() A(3) }`) | 3364 |
| `argsMissing_refused` | `nameAndTypeResolution/061_missing_base_constructor_arguments.sol` | 3415 |
| `argsCount_refused` | `inheritance/too_few_base_arguments.sol` (contract `Derived`) | 7927 |
| `nonBaseCtor_refused` | `inheritance/reference_non_base_ctor.sol` | 4659 |
| `ctorModifiers_ok` | `inheritance/modifiers_in_constructor_context.sol` | accepted |
| `usingNotLibrary_refused` | `nameAndTypeResolution/252_using_for_not_library.sol` | 4357 |
| `diamond_c3`, `diamond_ctorOrder` | S01's diamond `D is B, C` | linearization `D, C, B, A`, C3-consistent; constructors `A, B, C, D` |
-/

namespace Solidity.Frontend.Static.InheritanceExamples

open Solidity.Source Solidity.Frontend.Static

def u256T : Syn .typeName := .elem (.int false 256 (by decide))
def u8T : Syn .typeName := .elem (.int false 8 (by decide))
def p (t : Syn .typeName) : Syn .param := .param t Option.none Option.none
def rU : Syn (.list .param) := .cons (p u256T) .nil
def body : Syn (.opt (.block .body)) := .some (.block .nil)

/-- `function n() vis mut virtual? override? returns (…) { }` (or without
body). -/
def fn (n : String) (vis : Visibility) (mu : Option Mutability) (virt : Bool)
    (ov : Option (List IdPath)) (rets : Syn (.list .param)) (b : Bool) : Syn (.part false) :=
  .function (.ident n) .nil (Option.some vis) mu .nil virt ov rets (if b then body else .none)

def is_ (bs : List String) : Syn (.list .inherit) :=
  bs.foldr (fun b acc => .cons (.inherit ⟨b, []⟩ .none) acc) .nil

def con (abs : Bool) (n : String) (bs : List String) (parts : List (Syn (.part false))) : Syn .top :=
  .contract abs n .none (is_ bs) (parts.foldr (fun x acc => .cons x acc) .nil)

def mkUnit (tops : List (Syn .top)) : Syn .unit := .unit (tops.foldr (fun x acc => .cons x acc) .nil)

def res (u : Syn .unit) : Resolution := resolveUnit ⟨.legacy, []⟩ u

def A : IdPath := ⟨"A", []⟩
def B : IdPath := ⟨"B", []⟩

/-! ## Overrides -/

/-- `override_missing_virtual.sol`. -/
def missingVirtual : Syn .unit := mkUnit [
  con true "A" [] [fn "test" .external Option.none true Option.none rU false,
                  fn "test2" .external Option.none false Option.none rU true],
  con true "X" ["A"] [fn "test" .external Option.none false Option.none rU true,
                      fn "test2" .external Option.none false (Option.some [A]) rU true]]

/-- 9456 on `test` (no `override`), 4334 on `test2` (base not `virtual`). -/
theorem missingVirtual_refused :
    ((res missingVirtual).env.ownFns "X").map (fnOverrideB (res missingVirtual).env "X") = [false, false] ∧
    ¬ OverridesOK (res missingVirtual).env := by
  refine ⟨by decide, fun h => ?_⟩
  have e := overridesB_iff.mpr h
  revert e
  decide

/-- `override.sol`. -/
def overrideOk : Syn .unit := mkUnit [
  con true "A" [] [fn "test" .internal Option.none true Option.none rU false,
                  fn "test2" .internal Option.none true Option.none rU false],
  con false "X" ["A"] [fn "test" .internal Option.none false (Option.some []) rU true,
                       fn "test2" .internal Option.none false (Option.some [A]) rU true]]

theorem override_ok : InheritanceOK (res overrideOk) := inheritance_iff.mp (by decide)

/-- `override_less_strict_mutability.sol`, contracts `A` and `C`. -/
def lessStrict : Syn .unit := mkUnit [
  con false "A" [] [fn "foo" .external (Option.some .pure) true Option.none rU true],
  con false "C" ["A"] [fn "foo" .external (Option.some .view) true (Option.some []) rU true]]

theorem lessStrict_refused : ¬ OverridesOK (res lessStrict).env := fun h => by
  have e := overridesB_iff.mpr h
  revert e
  decide

/-- `override_stricter_mutability.sol`, contracts `A` and `B`. -/
def stricter : Syn .unit := mkUnit [
  con false "A" [] [fn "foo" .internal (Option.some .view) true Option.none rU true],
  con false "B" ["A"] [fn "foo" .internal (Option.some .pure) true (Option.some []) rU true]]

theorem stricter_ok : InheritanceOK (res stricter) := inheritance_iff.mp (by decide)

/-- `no_common_base_and_unique_implementation.sol`. -/
def noCommonBase : Syn .unit := mkUnit [
  con true "A" [] [fn "f" .external Option.none false Option.none .nil true,
                  fn "g" .external Option.none true Option.none .nil false],
  con true "B" [] [fn "g" .external Option.none false Option.none .nil true,
                  fn "f" .external Option.none true Option.none .nil false],
  con false "C" ["A", "B"] []]

theorem noCommonBase_refused : ¬ MustOverride (res noCommonBase).env := fun h => by
  have e := mustOverrideB_iff.mpr h
  revert e
  decide

/-- `override_shared_base_simple.sol`. -/
def sharedBase : Syn .unit := mkUnit [
  con false "I" [] [fn "f" .external Option.none false Option.none .nil true],
  con false "A" ["I"] [], con false "B" ["I"] [], con false "C" ["A", "B"] []]

theorem sharedBase_ok : InheritanceOK (res sharedBase) := inheritance_iff.mp (by decide)

/-- `override_shared_base.sol` (bodies dropped), with `override(A, B)` in
`X`, or with `override` and no list. -/
def sharedOverride (ov : List IdPath) : Syn .unit := mkUnit [
  con false "I" [] [fn "set" .pub Option.none true Option.none .nil true],
  con false "A" ["I"] [fn "set" .pub Option.none true (Option.some []) .nil true],
  con false "B" ["I"] [fn "set" .pub Option.none true (Option.some []) .nil true],
  con false "X" ["A", "B"] [fn "set" .pub Option.none false (Option.some ov) .nil true]]

theorem sharedBase_override_ok : InheritanceOK (res (sharedOverride [A, B])) := inheritance_iff.mp (by decide)

/-- **4327**: two base contracts, and the `override` list does not name them. -/
theorem sharedBase_unlisted_refused : ¬ OverridesOK (res (sharedOverride [])).env := fun h => by
  have e := overridesB_iff.mpr h
  revert e
  decide

/-- `external_turns_public_no_params.sol`. -/
def externalPublic : Syn .unit := mkUnit [
  con false "A" [] [fn "f" .external (Option.some .pure) true Option.none .nil true],
  con false "B" ["A"] [fn "f" .pub (Option.some .pure) false (Option.some []) .nil true]]

theorem externalPublic_ok : InheritanceOK (res externalPublic) := inheritance_iff.mp (by decide)

/-! ## Implementations -/

/-- `unimplemented_without_virtual.sol`. -/
def unimplNonVirtual : Syn .unit := mkUnit [con true "C" [] [fn "f" .external Option.none false Option.none .nil false]]

theorem unimplementedNonVirtual_refused : ¬ ImplOK (res unimplNonVirtual).env := fun h => by
  have e := implB_iff.mpr h
  revert e
  decide

/-- `029_create_abstract_contract.sol`, contract `base`. -/
def abstractNeeded : Syn .unit := mkUnit [con false "base" [] [fn "foo" .pub Option.none true Option.none .nil false]]

theorem abstractNeeded_refused : ¬ ImplOK (res abstractNeeded).env := fun h => by
  have e := implB_iff.mpr h
  revert e
  decide

/-! ## Base constructors and modifiers -/

/-- `constructor(uint) { }` -/
def ctor1 : Syn (.part false) := .constructor (.cons (p u256T) .nil) .nil false Option.none (.block .nil)
def ctor2 : Syn (.part false) := .constructor (.cons (p u256T) (.cons (p u256T) .nil)) .nil false Option.none (.block .nil)

/-- A constructor with modifier invocations. -/
def ctorWith (invs : List (Syn .modInv)) : Syn (.part false) :=
  .constructor .nil (invs.foldr (fun x acc => .cons x acc) .nil) false Option.none (.block .nil)

def num (n : Nat) : Syn .expr := .lit (.num (.dec n 0 0))
def args (es : List (Syn .expr)) : Syn (.opt .callArgs) := .some (.positional (es.foldr (fun x acc => .cons x acc) .nil))

/-- `contract A { constructor(uint) { } } contract B is A(2) { constructor() A(3) { } }` -/
def argsTwice : Syn .unit := .unit (.cons (con false "A" [] [ctor1])
  (.cons (.contract false "B" .none (.cons (.inherit A (args [num 2])) .nil)
    (.cons (ctorWith [.modInv A (args [num 3])]) .nil)) .nil))

theorem argsTwice_refused : ¬ CtorArgsOK (res argsTwice).env "B" := fun h => by
  have e := ctorArgsB_iff.mpr h
  revert e
  decide

/-- `061_missing_base_constructor_arguments.sol`. -/
def argsMissing : Syn .unit := mkUnit [con false "A" [] [ctor1], con false "B" ["A"] []]

theorem argsMissing_refused : ¬ CtorArgsOK (res argsMissing).env "B" := fun h => by
  have e := ctorArgsB_iff.mpr h
  revert e
  decide

/-- `too_few_base_arguments.sol`, contract `Derived`: `is Base(2)` for
`constructor(uint, uint)`. -/
def argsCount : Syn .unit := .unit (.cons (con false "Base" [] [ctor2])
  (.cons (.contract false "Derived" .none (.cons (.inherit ⟨"Base", []⟩ (args [num 2])) .nil) .nil) .nil))

theorem argsCount_refused : ¬ CtorArgsOK (res argsCount).env "Derived" := fun h => by
  have e := ctorArgsB_iff.mpr h
  revert e
  decide

/-- `reference_non_base_ctor.sol`: `contract X {} contract D { constructor() X(5) {} }` -/
def nonBaseCtor : Syn .unit := mkUnit [con false "X" [] [], con false "D" [] [ctorWith [.modInv ⟨"X", []⟩ (args [num 5])]]]

theorem nonBaseCtor_refused : ¬ ModInvOK (res nonBaseCtor).env := fun h => by
  have e := modInvsB_iff.mpr h
  revert e
  decide

/-- `modifier m { _; }` -/
def modDecl (n : String) : Syn (.part false) :=
  .modifier n .none false Option.none (.some (.block (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "_")))) .nil)))

/-- `modifiers_in_constructor_context.sol`. -/
def ctorModifiers : Syn .unit := mkUnit [
  con false "A" [] [ctorWith [.modInv ⟨"m1", []⟩ .none], modDecl "m1"],
  con false "B" ["A"] [modDecl "m2", ctorWith [.modInv A (args []), .modInv ⟨"m1", []⟩ .none, .modInv ⟨"m2", []⟩ .none]]]

theorem ctorModifiers_ok : InheritanceOK (res ctorModifiers) := inheritance_iff.mp (by decide)

/-! ## `using for` -/

/-- `252_using_for_not_library.sol`. -/
def usingNotLibrary : Syn .unit := mkUnit [con false "D" [] [],
  con false "C" [] [.usingPart (.usingPath ⟨"D", []⟩ (.some u256T) false)]]

theorem usingNotLibrary_refused : ¬ UsingLibOK (res usingNotLibrary).env usingNotLibrary := fun h => by
  have e := usingLibB_iff.mpr h
  revert e
  decide

/-! ## Linearization and constructor order -/

/-- S01's diamond: `A`; `B is A`; `C is A`; `D is B, C`. -/
theorem diamond_c3 : C3Lin (Syn.env TypingExamples.diamond) "D" ["D", "C", "B", "A"] :=
  linearize_sound TypingExamples.diamond_linearize

theorem diamond_ctorOrder : (Syn.env TypingExamples.diamond).ctorOrder "D" = ["A", "B", "C", "D"] :=
  (ctorOrder_spec TypingExamples.diamond_linearize).1

end Solidity.Frontend.Static.InheritanceExamples
/-- info: 'Solidity.Frontend.Static.fnOverrideB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.fnOverrideB_iff
/-- info: 'Solidity.Frontend.Static.overridesB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.overridesB_iff
/-- info: 'Solidity.Frontend.Static.mustOverrideB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.mustOverrideB_iff
/-- info: 'Solidity.Frontend.Static.implB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.implB_iff
/-- info: 'Solidity.Frontend.Static.ctorArgsB_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.ctorArgsB_iff
/-- info: 'Solidity.Frontend.Static.modInvsB_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.modInvsB_iff
/-- info: 'Solidity.Frontend.Static.usingLibB_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.usingLibB_iff
/-- info: 'Solidity.Frontend.Static.inheritance_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.inheritance_iff
/-- info: 'Solidity.Frontend.Static.callable_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.callable_unique
/-- info: 'Solidity.Frontend.Static.merge_sublist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.merge_sublist
/-- info: 'Solidity.Frontend.Static.merge_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.merge_nodup
/-- info: 'Solidity.Frontend.Static.merge_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.merge_sub
/-- info: 'Solidity.Frontend.Static.linearize_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.linearize_sound
/-- info: 'Solidity.Frontend.Static.ctorOrder_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.ctorOrder_spec
/-- info: 'Solidity.Frontend.Static.InheritanceExamples.missingVirtual_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InheritanceExamples.missingVirtual_refused
/-- info: 'Solidity.Frontend.Static.InheritanceExamples.override_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InheritanceExamples.override_ok
/-- info: 'Solidity.Frontend.Static.InheritanceExamples.lessStrict_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InheritanceExamples.lessStrict_refused
/-- info: 'Solidity.Frontend.Static.InheritanceExamples.noCommonBase_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InheritanceExamples.noCommonBase_refused
/-- info: 'Solidity.Frontend.Static.InheritanceExamples.sharedBase_unlisted_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InheritanceExamples.sharedBase_unlisted_refused
/-- info: 'Solidity.Frontend.Static.InheritanceExamples.abstractNeeded_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InheritanceExamples.abstractNeeded_refused
/-- info: 'Solidity.Frontend.Static.InheritanceExamples.argsTwice_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InheritanceExamples.argsTwice_refused
/-- info: 'Solidity.Frontend.Static.InheritanceExamples.argsMissing_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InheritanceExamples.argsMissing_refused
/-- info: 'Solidity.Frontend.Static.InheritanceExamples.argsCount_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InheritanceExamples.argsCount_refused
/-- info: 'Solidity.Frontend.Static.InheritanceExamples.nonBaseCtor_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InheritanceExamples.nonBaseCtor_refused
/-- info: 'Solidity.Frontend.Static.InheritanceExamples.usingNotLibrary_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InheritanceExamples.usingNotLibrary_refused
/-- info: 'Solidity.Frontend.Static.InheritanceExamples.diamond_c3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InheritanceExamples.diamond_c3
