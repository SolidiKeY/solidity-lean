import Solidity.Correctness.Lowering.Total.ConstructorPlacement

/-! Constructor placement in assembled function units and agreement of the
state declarations with `TransientDecode.decls`: explicit and implicit
constructors, no roots and no functions, initialized roots, and mixed
persistent/transient roots. Execution is not checked. -/
namespace Solidity.Examples.Lowering.Total.ConstructorPlacement

open Solidity.Correctness.Lowering.Total Solidity.Correctness.Lowering.Total.Decode
open Solidity.Correctness.Lowering.Total.Decode.Constructor
open Solidity.Correctness.Lowering.Total.TransientDecode (stateViews stateVarDecl)

def uint8 : Source.Elem := .int false 8 (by decide)
/-- `constructor() payable { b = 2; }` -/
def ctor : FunDecl :=
  { sourceDecl := some { mutability := .payable, callable := .constructor }, params := [],
    body := [.assign (.name "b") (.num 2)] }
/-- `function get() internal view returns (uint r) { return b; }` -/
def get : FunDecl :=
  { sourceDecl := some { name := "get", mutability := .viewFn, callable := .local .internalFn },
    params := [], rets := [("r", .prim .uint)], body := [.ret (some (.name "b"))] }
/-- `uint8 a = 1; uint b; uint c = a + 2;` with the constructor, and without one. -/
def explicit : Contract :=
  { vars := [("a", .prim .uint), ("b", .prim .uint), ("c", .prim .uint)], widths := [("a", 8)],
    inits := [("a", .num 1), ("c", .binop .add (.name "a") (.num 2))], ctor := some ctor }
def implicit : Contract := { explicit with ctor := none }
/-- No roots, no initializers, no constructor. -/
def empty : Contract := { vars := [] }
/-- `uint8 a = 7; bool transient t; uint transient n; uint b;` -/
def mixed : Contract :=
  { vars := [("a", .prim .uint), ("t", .prim .bool), ("n", .prim .uint), ("b", .prim .uint)],
    widths := [("a", 8)], transientRoots := ["t", "n"], inits := [("a", .num 7)] }

/-- The unit assembled from the generated prefix and the function entries. -/
def unitOf (C : Contract) (fs : List (Name × FunDecl)) : Option (Source.Syn .unit) := do
  Callee.withFunctions tablesS [] "C" (← declarationParts tablesS [] C) fs
def table (C : Contract) (fs : List (Name × FunDecl)) :=
  (unitOf C fs).map fun u => u.decls.map fun d => (d.kind, d.name, d.scope)
def envOf (C : Contract) (fs : List (Name × FunDecl)) : Source.Env :=
  ((unitOf C fs).map Source.Syn.env).getD ⟨[]⟩

/-! The assembled units, evaluated: `Callee.appendParts` is well-founded, so
these checks run compiled; the theorems below are the general facts. -/

-- The table: the contract, the constructor, the roots in order, then `get`.
#guard table explicit [("get", get)] == some [(.contract, "C", none),
    (.constructor, "", some "C"), (.stateVar, "a", some "C"), (.stateVar, "b", some "C"),
    (.stateVar, "c", some "C"), (.function, "get", some "C")]
-- The implicit constructor is the absence of a declaration; no functions.
#guard table implicit [] == some [(.contract, "C", none), (.stateVar, "a", some "C"),
    (.stateVar, "b", some "C"), (.stateVar, "c", some "C")]
-- No roots and no functions: the contract alone.
#guard table empty [] == some [(.contract, "C", none)]
-- Mixed roots with a function: the roots in order, then `get`.
#guard table mixed [("get", get)] == some [(.contract, "C", none), (.stateVar, "a", some "C"),
    (.stateVar, "t", some "C"), (.stateVar, "n", some "C"), (.stateVar, "b", some "C"),
    (.function, "get", some "C")]

-- The explicit constructor is found with the retained payable header; the
-- implicit one is absent; no roots, no state variables.
#guard ((envOf explicit [("get", get)]).ctorFrame "C").map (·.msgValue) == some true
#guard ((envOf implicit [("get", get)]).ctorDecl "C").isNone
#guard ((envOf empty []).stateVarsOf "C").isEmpty
-- The units elaborate; the program's initializers of `C` are in order, on their roots.
#guard Source.elaborates (envOf explicit [("get", get)])
#guard ((Source.progOf (envOf explicit [("get", get)])).inits "C").map (·.var.name) == ["a", "c"]
#guard Source.elaborates (envOf mixed [])
#guard ((Source.progOf (envOf mixed [])).inits "C").map (·.var.name) == ["a"]

/-- The parts of `mixed`: `a` keeps its initializer; `t` and `n` are transient. -/
def mixedParts : Source.Syn (.list (.part false)) :=
  .cons (.stateVar (.elem uint8) none none none false "a" (.some (num 7)))
    (.cons (stateVarDecl .bool true "t") (.cons (stateVarDecl uintElem true "n")
      (.cons (stateVarDecl uintElem false "b") .nil)))
theorem mixed_parts : declarationParts tablesS [] mixed = some mixedParts := rfl
/-- `TransientDecode.decls`: no initializer, transient at `t` and `n` only. -/
theorem mixed_decls : TransientDecode.decls mixed = .ok
    (.cons (stateVarDecl uint8 false "a") (.cons (stateVarDecl .bool true "t")
    (.cons (stateVarDecl uintElem true "n") (.cons (stateVarDecl uintElem false "b") .nil)))) := rfl

/-- Projection agreement, mixed roots: erasing `a = 7` gives `TransientDecode.decls`. -/
example : TransientDecode.decls mixed = .ok (stripInits mixedParts) := by
  rw [mixed_decls]; simp [mixedParts, stripInits, stripInit, stateVarDecl]
/-- The initializer is kept apart from the projection, on its root. -/
example : initsOf mixedParts = [("a", num 7)] := by
  simp [mixedParts, initsOf, initOf, stateVarDecl]
/-- The views: names, declared types and transient flags, in order. -/
example : stateViews mixedParts = [some ("a", .elem uint8, false), some ("t", .elem .bool, true),
    some ("n", .elem uintElem, true), some ("b", .elem uintElem, false)] := by
  simp [mixedParts, stateViews, TransientDecode.stateView, stateVarDecl]
/-- The explicit constructor contributes one `none` view before the roots'. -/
example {p} (hp : declarationParts tablesS [] explicit = some p) :
    (stateViews p).head? = some none := by
  obtain ⟨_, _, _, _, _, _, h, _⟩ := declarationParts_decls hp
  rw [h]; simp [explicit]

/-- The exported facts, instantiated on an assembled unit. -/
example {u} (hu : Callee.withFunctions tablesS [] "C" mixedParts [("get", get)] = some u) :=
  And.intro (withFunctions_placed mixed_parts hu) (And.intro (withFunctions_inits mixed_parts hu)
    (And.intro (withFunctions_ctor mixed_parts hu) (withFunctions_decls mixed_parts hu)))

end Solidity.Examples.Lowering.Total.ConstructorPlacement
