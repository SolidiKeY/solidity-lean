import Solidity.Source.Decls
import Solidity.Source.Upstream

/-!
# S00 controls: concrete syntax trees

A counter contract inside the profile, and four programs each using one
syntax-level exclusion, with their rejections and declarations computed by
the kernel.  The trees are written by hand from their Solidity text (shown
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

/-- The contract's node mentions `count` (in `inc`), and so does `inc`'s. -/
theorem counter_refs : counter.decls.map Decl.refs = [[⟨"count", []⟩], [], [⟨"count", []⟩]] := by
  decide +kernel

/-- `function f() external { count++; assembly { } }` -/
def withAssembly : Syn .unit :=
  .unit (.cons (.contract false "A" .none .nil
    (.cons (extFn "f" (.cons incStmt (.cons (.stmtItem (.assembly false [] .nil)) .nil))) .nil)) .nil)

theorem withAssembly_rejected : withAssembly.rejections = [.inlineAssembly] := rfl

/-- `contract L layout at 1 { }` -/
def withLayout : Syn .unit :=
  .unit (.cons (.contract false "L" (.some (.lit (.num (.dec 1 0 0)))) .nil .nil) .nil)

theorem withLayout_rejected : withLayout.rejections = [.storageLayout] := rfl

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
/-- info: 'Solidity.Source.Examples.withAssembly_rejected' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Source.Examples.withAssembly_rejected
