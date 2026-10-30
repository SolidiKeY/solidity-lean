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

/-- `override_less_strict_mutability.sol`. -/
def lessStrict : Syn .unit := mkUnit [
  con false "A" [] [fn "foo" .external (Option.some .pure) true Option.none rU true],
  con false "B" ["A"] [fn "foo" .external (Option.some .pure) true (Option.some []) rU true],
  con false "C" ["A"] [fn "foo" .external (Option.some .view) true (Option.some []) rU true],
  con false "D" ["B", "C"] [fn "foo" .external Option.none true (Option.some [B, ⟨"C", []⟩]) rU true],
  con false "E" ["C", "B"] [fn "foo" .external (Option.some .pure) true (Option.some [B, ⟨"C", []⟩]) rU true],
  con false "F" ["C", "B"] [fn "foo" .external (Option.some .payable) true (Option.some [B, ⟨"C", []⟩]) rU true]]

/-- 6959 on `C`, `D` and `F`; `B` and `E` (`pure` over `view` and `pure`)
pass, as in solc. -/
theorem lessStrict_refused :
    (["B", "C", "D", "E", "F"].map fun c =>
      ((res lessStrict).env.ownFns c).all (fnOverrideB (res lessStrict).env c)) =
      [true, false, false, true, false] ∧
    ¬ OverridesOK (res lessStrict).env := by
  refine ⟨by decide, fun h => ?_⟩
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

/-- `function n(ps) internal virtual? override(…)? returns (uint256);` -/
def fnP (n : String) (ps : Syn (.list .param)) (virt : Bool) (ov : Option (List IdPath)) : Syn (.part false) :=
  .function (.ident n) ps (Option.some .internal) Option.none .nil virt ov rU .none

/-- `override_multiple_duplicated.sol`. -/
def dupList : Syn .unit := mkUnit [
  con true "A" [] [fnP "foo" .nil true Option.none, fnP "test" (.cons (p u8T) .nil) true Option.none],
  con true "B" [] [fnP "foo" .nil true Option.none, fnP "test" .nil true Option.none],
  con true "C" [] [fnP "foo" .nil true Option.none],
  con true "D" [] [fnP "foo" .nil true Option.none, fnP "test" .nil true Option.none],
  con true "X" ["A", "B", "C", "D"] [
    fnP "test" .nil true (Option.some [B, ⟨"D", []⟩, ⟨"D", []⟩]),
    fnP "foo" .nil true (Option.some [A, ⟨"C", []⟩, B, B, B, ⟨"D", []⟩, ⟨"D", []⟩])]]

/-- **4520** on both functions of `X`; without the duplicates both pass. -/
theorem dupList_refused :
    ((res dupList).env.ownFns "X").map (fnOverrideB (res dupList).env "X") = [false, false] ∧
    ¬ OverridesOK (res dupList).env := by
  refine ⟨by decide, fun h => ?_⟩
  have e := overridesB_iff.mpr h
  revert e
  decide

/-- The same unit with each list deduplicated. -/
def dupListFixed : Syn .unit := mkUnit [
  con true "A" [] [fnP "foo" .nil true Option.none, fnP "test" (.cons (p u8T) .nil) true Option.none],
  con true "B" [] [fnP "foo" .nil true Option.none, fnP "test" .nil true Option.none],
  con true "C" [] [fnP "foo" .nil true Option.none],
  con true "D" [] [fnP "foo" .nil true Option.none, fnP "test" .nil true Option.none],
  con true "X" ["A", "B", "C", "D"] [
    fnP "test" .nil true (Option.some [B, ⟨"D", []⟩]),
    fnP "foo" .nil true (Option.some [A, ⟨"C", []⟩, B, ⟨"D", []⟩])]]

theorem dupListFixed_ok : InheritanceOK (res dupListFixed) := inheritance_iff.mp (by decide)

/-- `uint[] loc` (or `uint8[] loc`) as a parameter list. -/
def arrP (t : Syn .typeName) (loc : DataLoc) : Syn (.list .param) :=
  .cons (.param (.array t .none) (Option.some loc) Option.none) .nil

/-- `override/calldata_memory.sol` (bodies dropped); with `elem` `u8T` in
`B`, the parameter types differ. -/
def calldataMemory (t : Syn .typeName) : Syn .unit := mkUnit [
  con false "A" [] (([("f", Option.some Mutability.pure), ("g", Option.some .view), ("h", Option.none),
    ("i", Option.some .payable)]).map fun (n, mu) =>
      .function (.ident n) (arrP u256T .calldata) (Option.some .external) mu .nil true Option.none .nil body),
  con false "B" ["A"] (([("f", Option.some Mutability.pure), ("g", Option.some .view), ("h", Option.none),
    ("i", Option.some .payable)]).map fun (n, mu) =>
      .function (.ident n) (arrP t .memory) (Option.some .pub) mu .nil false (Option.some []) .nil body)]

/-- A `memory` parameter overrides a `calldata` one (solc accepts); with
`uint8[]` for `uint[]` nothing is overridden (7792). -/
theorem calldataMemory_ok : InheritanceOK (res (calldataMemory u256T)) ∧
    ¬ OverridesOK (res (calldataMemory u8T)).env := by
  refine ⟨inheritance_iff.mp (by decide), fun h => ?_⟩
  have e := overridesB_iff.mpr h
  revert e
  decide

/-- `interface/overrides_single.sol`. -/
def overridesSingle : Syn .unit := mkUnit [
  .interface "Super" .nil (["test1", "test2", "test3"].foldr
    (fun n acc => .cons (fn n .external Option.none false Option.none rU false) acc) .nil),
  .interface "Sub" (is_ ["Super"]) (.cons (fn "test1" .external Option.none false Option.none rU false)
    (.cons (fn "test2" .external Option.none false (Option.some []) rU false)
    (.cons (fn "test3" .external Option.none false (Option.some [⟨"Super", []⟩]) rU false) .nil)))]

/-- Overriding a single interface function needs no `override` (solc 0.8.8);
over a `virtual` contract function it does (9456). -/
theorem overridesSingle_ok : InheritanceOK (res overridesSingle) ∧
    ¬ OverridesOK (res (mkUnit [con true "Super" [] [fn "test1" .external Option.none true Option.none rU false],
      con true "Sub" ["Super"] [fn "test1" .external Option.none true Option.none rU false]])).env := by
  refine ⟨inheritance_iff.mp (by decide), fun h => ?_⟩
  have e := overridesB_iff.mpr h
  revert e
  decide

/-- `override/override_implemented_with_unimplemented_then_implemented.sol`. -/
def implThenUnimpl : Syn .unit := mkUnit [
  con false "A" [] [fn "f" .pub Option.none true Option.none .nil true],
  con true "B" ["A"] [fn "f" .pub Option.none true (Option.some []) .nil false],
  con false "C" ["B"] [fn "f" .pub Option.none true (Option.some []) .nil true]]

/-- **4593** on `B` only. -/
theorem implThenUnimpl_refused :
    (["B", "C"].map fun c => ((res implThenUnimpl).env.ownFns c).all (fnOverrideB (res implThenUnimpl).env c)) =
      [false, true] ∧ ¬ OverridesOK (res implThenUnimpl).env := by
  refine ⟨by decide, fun h => ?_⟩
  have e := overridesB_iff.mpr h
  revert e
  decide

/-- `override/virtual_private.sol`. -/
def virtualPrivate : Syn .unit := mkUnit [
  con true "A" [] [fn "test" .priv Option.none true Option.none rU false],
  con true "X" ["A"] [fn "test" .priv Option.none false (Option.some []) rU true]]

/-- `virtual/library_err.sol`, or without `virtual`. -/
def libVirtual (v : Bool) : Syn .unit := mkUnit [
  .library "L" (.cons (fn "f" .internal (Option.some .pure) v Option.none rU true) .nil)]

/-- **3942** and **7801**; the library function without `virtual` passes. -/
theorem virtualDecl_refused : ¬ VirtualDeclOK (res virtualPrivate).env ∧
    ¬ VirtualDeclOK (res (libVirtual true)).env ∧ VirtualDeclOK (res (libVirtual false)).env := by
  refine ⟨fun h => ?_, fun h => ?_, virtualDeclB_iff.mp (by decide)⟩ <;>
  · have e := virtualDeclB_iff.mpr h
    revert e
    decide

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

/-- `too_few_base_arguments.sol`: `Derived is Base(2)` and `Derived2 is
Base { constructor() Base(2) { } }` for `constructor(uint, uint)`. -/
def argsCount : Syn .unit := .unit (.cons (con false "Base" [] [ctor2])
  (.cons (.contract false "Derived" .none (.cons (.inherit ⟨"Base", []⟩ (args [num 2])) .nil) .nil)
  (.cons (.contract false "Derived2" .none (.cons (.inherit ⟨"Base", []⟩ .none) .nil)
    (.cons (ctorWith [.modInv ⟨"Base", []⟩ (args [num 2])]) .nil)) .nil)))

/-- 7927 on `Derived`, 2973 on `Derived2`. -/
theorem argsCount_refused : ¬ CtorArgsOK (res argsCount).env "Derived" ∧
    ¬ CtorArgsOK (res argsCount).env "Derived2" := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have e := ctorArgsB_iff.mpr h
    revert e
    decide
  · have e := ctorArgsB_iff.mpr h
    revert e
    decide

def C : IdPath := ⟨"C", []⟩

/-- `duplicatedConstructorCall/ancestor.sol`. -/
def argsAncestor : Syn .unit := .unit (.cons (con false "A" [] [ctor1])
  (.cons (.contract false "B" .none (.cons (.inherit A (args [num 2])) .nil) (.cons (ctorWith []) .nil))
  (.cons (.contract false "C" .none (.cons (.inherit B .none) .nil)
    (.cons (ctorWith [.modInv A (args [num 3])]) .nil)) .nil)))

/-- `duplicatedConstructorCall/base_multi.sol` (`ctor` true) and
`base_multi_no_constructor.sol` (false). -/
def argsMulti (ctor : Bool) : Syn .unit := .unit (.cons (con false "C" [] [ctor1])
  (.cons (.contract false "A" .none (.cons (.inherit C (args [num 2])) .nil) .nil)
  (.cons (.contract false "B" .none (.cons (.inherit C (args [num 2])) .nil) .nil)
  (.cons (.contract false "D" .none (.cons (.inherit A .none) (.cons (.inherit B .none) .nil))
    (if ctor then .cons (ctorWith [.modInv C (args [num 3])]) .nil else .nil)) .nil))))

/-- `duplicatedConstructorCall/base_multi_no_constructor_modifier_style.sol`. -/
def argsMultiMod : Syn .unit := .unit (.cons (con false "C" [] [ctor1])
  (.cons (.contract false "A" .none (.cons (.inherit C .none) .nil) (.cons (ctorWith [.modInv C (args [num 2])]) .nil))
  (.cons (.contract false "B" .none (.cons (.inherit C .none) .nil) (.cons (ctorWith [.modInv C (args [num 2])]) .nil))
  (.cons (con false "D" ["A", "B"] []) .nil))))

/-- **3364** on the remaining `duplicatedConstructorCall/` tests: arguments
given twice along the linearization, through an ancestor, two bases, or
constructor modifier invocations of two bases. -/
theorem argsTwice_paths_refused :
    ¬ CtorArgsOK (res argsAncestor).env "C" ∧ ¬ CtorArgsOK (res (argsMulti true)).env "D" ∧
    ¬ CtorArgsOK (res (argsMulti false)).env "D" ∧ ¬ CtorArgsOK (res argsMultiMod).env "D" := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
  · have e := ctorArgsB_iff.mpr h
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

/-- `disallow_modifier_style_without_parentheses.sol`:
`contract A { constructor() { } } contract B is A { constructor() A { } }` -/
def modStyleBare : Syn .unit := mkUnit [con false "A" [] [ctorWith []],
  con false "B" ["A"] [ctorWith [.modInv A .none]]]

/-- **1563**: a base constructor invoked modifier-style needs parentheses;
with them (`A()`) the unit passes. -/
theorem modStyleBare_refused : ¬ ModInvOK (res modStyleBare).env ∧
    ModInvOK (res (mkUnit [con false "A" [] [ctorWith []],
      con false "B" ["A"] [ctorWith [.modInv A (args [])]]])).env := by
  refine ⟨fun h => ?_, modInvsB_iff.mp (by decide)⟩
  have e := modInvsB_iff.mpr h
  revert e
  decide

/-- `modifier m(uint) { _; }` -/
def modDeclP (n : String) : Syn (.part false) :=
  .modifier n (.some (.cons (p u256T) .nil)) false Option.none
    (.some (.block (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "_")))) .nil)))

/-- `function f() public m { }` (or `m(1)`), `m` taking one parameter. -/
def modArgs (a : Option (List (Syn .expr))) : Syn .unit := mkUnit [con false "X" [] [modDeclP "m",
  .function (.ident "f") .nil (Option.some .pub) Option.none
    (.cons (.modInv ⟨"m", []⟩ (match a with | Option.some es => args es | Option.none => .none)) .nil)
    false Option.none .nil body]]

/-- **2973**: a modifier of one parameter invoked without parentheses (zero
arguments) or with two is refused; with one it passes. -/
theorem modArgs_count :
    ¬ ModInvOK (res (modArgs Option.none)).env ∧ ¬ ModInvOK (res (modArgs (Option.some [num 1, num 2]))).env ∧
    ModInvOK (res (modArgs (Option.some [num 1]))).env := by
  refine ⟨fun h => ?_, fun h => ?_, modInvsB_iff.mp (by decide)⟩ <;>
  · have e := modInvsB_iff.mpr h
    revert e
    decide

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
/-- info: 'Solidity.Frontend.Static.virtualDeclB_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.virtualDeclB_iff
/-- info: 'Solidity.Frontend.Static.InheritanceExamples.dupList_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InheritanceExamples.dupList_refused
/-- info: 'Solidity.Frontend.Static.InheritanceExamples.dupListFixed_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InheritanceExamples.dupListFixed_ok
/-- info: 'Solidity.Frontend.Static.InheritanceExamples.argsTwice_paths_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InheritanceExamples.argsTwice_paths_refused
/-- info: 'Solidity.Frontend.Static.InheritanceExamples.modStyleBare_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InheritanceExamples.modStyleBare_refused
/-- info: 'Solidity.Frontend.Static.InheritanceExamples.modArgs_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InheritanceExamples.modArgs_count
/-- info: 'Solidity.Frontend.Static.InheritanceExamples.calldataMemory_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InheritanceExamples.calldataMemory_ok
/-- info: 'Solidity.Frontend.Static.InheritanceExamples.overridesSingle_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InheritanceExamples.overridesSingle_ok
/-- info: 'Solidity.Frontend.Static.InheritanceExamples.implThenUnimpl_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InheritanceExamples.implThenUnimpl_refused
/-- info: 'Solidity.Frontend.Static.InheritanceExamples.virtualDecl_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InheritanceExamples.virtualDecl_refused
