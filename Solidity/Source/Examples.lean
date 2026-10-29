import Solidity.Source.Decls
import Solidity.Source.Upstream

/-!
# S00 controls: concrete syntax trees

A counter contract inside the profile; programs using each syntax-level
exclusion, alone, nested in a modifier or an initializer, and together; the
in-profile neighbours of two exclusions (a literal `layout at` base, the
canonical rethrow); their rejections and declarations computed by the kernel;
and the intrinsic contexts as theorems (`break` outside a loop and nested
`unchecked` have no tree).  The trees are written by hand from their Solidity text (shown
in each docstring); parsing text into them is G08–G11's.
-/

namespace Solidity.Source.Examples

open Solidity.Source

/-- `uint256`. -/
def u256 : Syn .typeName := .elem (.int false 256 (by decide))

/-- `count++;` -/
def incStmt : Syn (.item .body) :=
  .stmtItem (.simpleStmt (.exprStmt (.unarySuffix .inc (.ident "count"))))

/-- A function `f() external { body }`. -/
def extFn (f : String) (body : Syn (.list (.item .body))) : Syn (.part false) :=
  .function (.ident f) .nil (some .external) none .nil false none .nil (.some (.block body))

/-- ```
contract Counter {
  uint256 public count;
  function inc() external { count++; }
}
``` -/
def counter : Syn .unit :=
  .unit (.cons (.contract false "Counter" .none .nil
    (.cons (.stateVar u256 (some .pub) none none false "count" .none)
      (.cons (extFn "inc" (.cons incStmt .nil)) .nil))) .nil)

theorem counter_inProfile : counter.rejections = [] := rfl

theorem counter_decls : counter.decls.map (fun d => (d.kind, d.name, d.scope)) =
    [(.contract, "Counter", none), (.stateVar, "count", some "Counter"),
      (.function, "inc", some "Counter")] := by decide +kernel

/-- The contract has no bases; `inc` mentions `count`. -/
theorem counter_refs : counter.decls.map Decl.refs = [[], [], [(.use, ⟨"count", []⟩)]] := by
  decide +kernel

/-- `function f() external { count++; assembly { } }` -/
def withAssembly : Syn .unit :=
  .unit (.cons (.contract false "A" .none .nil
    (.cons (extFn "f" (.cons incStmt (.cons (.stmtItem (.assembly false [] .nil)) .nil))) .nil)) .nil)

theorem withAssembly_rejected : withAssembly.rejections = [.inlineAssembly] := rfl

/-- `contract L layout at 1 { }`: a literal base, in the profile
(`logicalStorageBase`). -/
def withLiteralLayout : Syn .unit :=
  .unit (.cons (.contract false "L" (.some (.lit (.num (.dec 1 0 0)))) .nil .nil) .nil)

theorem withLiteralLayout_inProfile : withLiteralLayout.rejections = [] := rfl

/-- `contract L layout at B { }`: a non-literal base. -/
def withLayout : Syn .unit :=
  .unit (.cons (.contract false "L" (.some (.ident "B")) .nil .nil) .nil)

theorem withLayout_rejected : withLayout.rejections = [.storageLayout] := rfl

/-- `pragma experimental solidity;` -/
def withGeneric : Syn .unit := .unit (.cons (.pragma ["experimental", "solidity"]) .nil)

theorem withGeneric_rejected : withGeneric.rejections = [.removedGenericSolidity] := rfl

/-- `pragma solidity ^0.8.0;` -/
theorem pragmaVersion_inProfile :
    (Syn.unit (.cons (.pragma ["solidity", "^0.8.0"]) .nil)).rejections = [] := rfl

/-- `function f(bytes memory data) external { assembly { revert(add(data, 32), mload(data)) } }`:
the canonical rethrow, in the profile. -/
def rethrow : Syn (.stmt .body) :=
  .assembly false [] (.cons (.yulExprStmt (.yulCall "revert" (.cons (.yulCall "add" (.cons
    (.yulPath "data" []) (.cons (.yulLit (.dec 32)) .nil))) (.cons (.yulCall "mload"
    (.cons (.yulPath "data" []) .nil)) .nil)))) .nil)

theorem rethrow_inProfile : rethrow.rejections = [] := rfl

/-- The same with two different buffers is general assembly. -/
def notRethrow : Syn (.stmt .body) :=
  .assembly false [] (.cons (.yulExprStmt (.yulCall "revert" (.cons (.yulCall "add" (.cons
    (.yulPath "data" []) (.cons (.yulLit (.dec 32)) .nil))) (.cons (.yulCall "mload"
    (.cons (.yulPath "other" []) .nil)) .nil)))) .nil)

theorem notRethrow_rejected : notRethrow.rejections = [.inlineAssembly] := rfl

/-- `_;` -/
def placeholder : Syn (.item .body) := .stmtItem (.simpleStmt (.exprStmt (.ident "_")))

/-- `modifier m() { _; }` -/
theorem modifier_inProfile :
    (Syn.modifier "m" .none false none (.some (.block (.cons placeholder .nil)))).rejections = [] :=
  rfl

/-- `modifier m() { count++; }`: a concrete body without a placeholder. -/
theorem modifierNoPlaceholder_rejected :
    (Syn.modifier "m" .none false none (.some (.block (.cons incStmt .nil)))).rejections =
      [.invalidModifierBody] := rfl

/-- `modifier m();`: an abstract modifier needs no placeholder. -/
theorem abstractModifier_inProfile : (Syn.modifier "m" .none false none .none).rejections = [] := rfl

/-- `modifier m() { unchecked { _; } }` -/
theorem uncheckedPlaceholder_rejected :
    (Syn.modifier "m" .none false none (.some (.block (.cons
      (.uncheckedItem (.block (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "_")))) .nil)))
      .nil)))).rejections = [.invalidModifierBody] := rfl

/-- `modifier m() { _; x >>>= 1; }`: an exclusion inside a modifier. -/
theorem modifierShr_rejected :
    (Syn.modifier "m" .none false none (.some (.block (.cons placeholder (.cons (.stmtItem
      (.simpleStmt (.exprStmt (.assign .shr (.ident "x") (.lit (.num (.dec 1 0 0))))))) .nil))))
      ).rejections = [.unsignedRightShift] := rfl

/-- `uint256 x = 1 years;` in a contract, and `layout at B`: two
rejections, root first. -/
theorem two_rejected :
    (Syn.contract false "T" (.some (.ident "B")) .nil (.cons (.stateVar u256 none none none false "x"
      (.some (.litUnit (.dec 1 0 0) .years))) .nil)).rejections = [.storageLayout, .removedUnits] := rfl

/-- **`break` has no tree outside a loop.** -/
theorem no_break_outside_loop {u : Bool} (s : Syn (.stmt ⟨false, u⟩)) : s.ctor ≠ .breakStmt := by
  cases s <;> simp only [Syn.ctor, ne_eq, reduceCtorEq, not_false_eq_true]

/-- **`continue` has no tree outside a loop.** -/
theorem no_continue_outside_loop {u : Bool} (s : Syn (.stmt ⟨false, u⟩)) :
    s.ctor ≠ .continueStmt := by
  cases s <;> simp only [Syn.ctor, ne_eq, reduceCtorEq, not_false_eq_true]

/-- **`unchecked` blocks do not nest.** -/
theorem no_nested_unchecked {l : Bool} (s : Syn (.item ⟨l, true⟩)) : s.ctor ≠ .uncheckedItem := by
  cases s <;> simp only [Syn.ctor, ne_eq, reduceCtorEq, not_false_eq_true]

/-- `function f() external { count >>> 1; }` -/
def withShr : Syn .unit :=
  .unit (.cons (.contract false "S" .none .nil
    (.cons (extFn "f" (.cons (.stmtItem (.simpleStmt (.exprStmt
      (.shift .shr (.ident "count") (.lit (.num (.dec 1 0 0))))))) .nil)) .nil)) .nil)

theorem withShr_rejected : withShr.rejections = [.unsignedRightShift] := rfl

/-- `uint256 constant Y = 1 years;` at file level. -/
def withYears : Syn .unit :=
  .unit (.cons (.topPart (.constant u256 "Y" (.litUnit (.dec 1 0 0) .years))) .nil)

theorem withYears_rejected : withYears.rejections = [.removedUnits] := rfl

/-- `break` exists only inside a loop: `while (true) { break; }`. -/
def loopBreak : Syn (.stmt .body) :=
  .whileStmt (.lit (.bool true))
    (.blockStmt (.block (.cons (.stmtItem .breakStmt) .nil)))

theorem loopBreak_inProfile : loopBreak.rejections = [] := rfl

example : (counter.decls.map (·.name)) = ["Counter", "count", "inc"] := rfl
example : (counter.decls.map (·.kind)) = [.contract, .stateVar, .function] := rfl
example : (counter.decls.map (·.scope)) = [none, some "Counter", some "Counter"] := rfl

end Solidity.Source.Examples

/-- info: 'Solidity.Source.Syn.rejections_of_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.Syn.rejections_of_sub
/-- info: 'Solidity.Source.Ctor.mem_all' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Source.Ctor.mem_all
/-- info: 'Solidity.Source.Ctor.grammar_covers' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Source.Ctor.grammar_covers
/-- info: 'Solidity.Source.Syn.decls_ctor' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Source.Syn.decls_ctor
/-- info: 'Solidity.Source.Syn.nodes_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Source.Syn.nodes_eq
/-- info: 'Solidity.Source.Examples.withAssembly_rejected' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Source.Examples.withAssembly_rejected
/-- info: 'Solidity.Source.Syn.excl_ctor' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Source.Syn.excl_ctor
/-- info: 'Solidity.Source.Excl.mapped' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Source.Excl.mapped
/-- info: 'Solidity.Source.Examples.no_break_outside_loop' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Source.Examples.no_break_outside_loop
