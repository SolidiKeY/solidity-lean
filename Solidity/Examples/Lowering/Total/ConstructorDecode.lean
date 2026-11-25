import Solidity.Correctness.Lowering.Total.ConstructorDecode

/-! Checks of constructor and state-initializer declaration assembly: what is
spelled, in which order, when assembly refuses, and what the placed parts give
in an actual Source unit. Execution is not checked here. -/
namespace Solidity.Examples.Lowering.Total.ConstructorDecode

open Solidity.Correctness.Lowering.Total Solidity.Correctness.Lowering.Total.Decode
open Solidity.Correctness.Lowering.Total.Decode.Constructor

/-- A retained constructor header. -/
def header (m : SourceMutability) : SourceFunction :=
  { mutability := m, callable := .constructor }

/-- A retained header of an ordinary internal function. -/
def internalHeader : SourceFunction := { callable := .local .internalFn }

/-- `constructor(uint8 x) payable { b = x; }` -/
def ctor : FunDecl :=
  { sourceDecl := some (header .payable), params := [("x", .prim .uint)], widths := [("x", 8)],
    body := [.assign (.name "b") (.name "x")], payable := true }

/-- `uint8 a = 1; uint b; uint c = a + 2;` with that constructor. -/
def explicit : Contract :=
  { vars := [("a", .prim .uint), ("b", .prim .uint), ("c", .prim .uint)], widths := [("a", 8)],
    inits := [("a", .num 1), ("c", .binop .add (.name "a") (.num 2))], ctor := some ctor }

/-- The same contract without a constructor. -/
def implicit : Contract := { explicit with ctor := none }

def uint8 : Source.Elem := .int false 8 (by decide)

/-- What a part list declares: kind, name and written initializer, in order. -/
def summary (parts : Option (Source.Syn (.list (.part false)))) :
    Option (List (Source.DeclKind × String × Option (Source.Syn .expr))) :=
  parts.map fun p => (p.collect (some "C")).map fun d => (d.kind, d.name, d.init?)

/-! ### Constructor -/

/-- Parameter name and width, payable status and body are the original ones. -/
example : constructorPart tablesS [] ctor = some
    (.constructor (.cons (.param (.elem uint8) none (some "x")) .nil) .nil true none
      (.block (.cons (.stmtItem (.simpleStmt (.exprStmt
        (.assign .assign (.ident "b") (.ident "x"))))) .nil))) := rfl

/-- Payable status is the retained header's, not the model flag's. -/
example : payable? (header .nonpayable) = some false := rfl
example : (constructorPart tablesS [] { ctor with sourceDecl := some (header .nonpayable) }).map
    (fun | .constructor _ _ pay _ _ => pay | _ => true) = some false := rfl

/-- Modifier applications stay invocations, in order, with their arguments. -/
example : (constructorPart tablesS [] { ctor with mods :=
      [⟨"first", [], [], [], [], []⟩, ⟨"second", [("y", .prim .uint)], [.name "x"], [], [], []⟩] }).map
      (fun | .constructor _ ms _ _ _ => some ms | _ => none) = some (some
    (.cons (.modInv ⟨"first", []⟩ (.some (.positional .nil)))
      (.cons (.modInv ⟨"second", []⟩ (.some (.positional (.cons (.ident "x") .nil)))) .nil))) := rfl

/-- Refused, not guessed: no retained header, a header of another role, a
`view` header, a return slot, a reference parameter, an unspelled body. -/
example : constructorPart tablesS [] { ctor with sourceDecl := none } = none := rfl
example : constructorPart tablesS [] { ctor with sourceDecl := some internalHeader } = none := rfl
example : constructorPart tablesS [] { ctor with sourceDecl := some (header .viewFn) } = none := rfl
example : constructorPart tablesS [] { ctor with rets := [("r", .prim .uint)] } = none := rfl
example : constructorPart tablesS [] { ctor with params := [("x", .ref (.array (.prim .uint)))] } =
    none := rfl
example : constructorPart tablesS [] { ctor with body := [.hole] } = none := rfl

/-! ### Initializers and order -/

/-- The constructor, then the roots in declaration order, each initializer on
its own root. -/
example : summary (declarationParts tablesS [] explicit) = some
    [(.constructor, "", none), (.stateVar, "a", some (num 1)), (.stateVar, "b", none),
     (.stateVar, "c", some (.addSub .add (.ident "a") (num 2)))] := rfl

/-- The implicit constructor is the absence of a declaration; the
initializers stay. -/
example : summary (declarationParts tablesS [] implicit) = some
    [(.stateVar, "a", some (num 1)), (.stateVar, "b", none),
     (.stateVar, "c", some (.addSub .add (.ident "a") (num 2)))] := rfl

/-- The width row is read: `a` is declared `uint8`, `b` is `uint256`. -/
example : (declarationParts tablesS [] implicit).map
    (fun p => (p.collect (some "C")).map fun d => d.varTy ⟨[]⟩) = some
    [some (uint8.ty .storage), some (uintElem.ty .storage), some (uintElem.ty .storage)] := rfl

/-- Refused: initializers out of root order, one naming no root, two for one
root, a reference root, an initializer with no spelling. -/
example : declarationParts tablesS [] { explicit with
    inits := [("c", .num 3), ("a", .num 1)] } = none := rfl
example : declarationParts tablesS [] { explicit with inits := [("z", .num 1)] } = none := rfl
example : declarationParts tablesS [] { explicit with
    inits := [("a", .num 1), ("a", .num 2)] } = none := rfl
example : declarationParts tablesS [] { explicit with
    vars := [("a", .ref (.array (.prim .uint)))], widths := [], inits := [] } = none := rfl
example : declarationParts tablesS [] { explicit with
    inits := [("a", .tuple [])] } = none := rfl

/-! ### In a unit -/

/-- The unit of a contract: its declaration parts and nothing else. -/
def unitOf (C : Contract) : Option (Source.Syn .unit) :=
  (declarationParts tablesS [] C).map fun parts =>
    .unit (.cons (.contract false "C" .none .nil parts) .nil)

def envOf (C : Contract) : Source.Env := ((unitOf C).map (·.env)).getD ⟨[]⟩

/-- Every initializer elaborates; the program's initializers are `a` then
`c`, each at its root's declared type. -/
example : (envOf explicit).decls.all (fun d =>
    d.init?.isNone || (Source.elabInit (envOf explicit) d).isSome) = true := rfl
example : ((Source.progOf (envOf explicit)).inits "C").map (fun i => (i.var.name, i.τ)) =
    [("a", uint8.ty .storage), ("c", uintElem.ty .storage)] := rfl

/-- Explicit: the constructor frame has the parameter `x : uint8` and reads
`msg.value`. Implicit: no constructor, not payable; the initializers remain. -/
example : ((envOf explicit).ctorFrame "C").map (fun f => (f.names, f.ps, f.rs, f.msgValue)) =
    some ([some "x"], [uint8.ty .memory], [], true) := rfl
example : (envOf explicit).ctorPayable "C" = true := rfl
/-- The spelled body types in that frame. -/
example : ((envOf explicit).ctorFrame "C").map (fun f =>
    (Source.ItemsD.infer (f.ctx (envOf explicit) (some "C")) f.locals f.body).isSome) =
    some true := rfl
example : (envOf implicit).ctorDecl "C" = none ∧ (envOf implicit).ctorPayable "C" = false :=
  ⟨rfl, rfl⟩
example : ((Source.progOf (envOf implicit)).inits "C").map (fun i => i.var.name) = ["a", "c"] := rfl

/-- The placement theorems apply to the landed unit builder's output. -/
example {parts : Source.Syn (.list (.part false))} {u : Source.Syn .unit}
    (hp : declarationParts tablesS [] implicit = some parts)
    (hu : Callee.withFunctions tablesS [] "C" parts [] = some u) :
    u.env.ctorDecl "C" = none :=
  (placed_implicit hp rfl (withFunctions_placed hu)).1

/-- Spelling is not typing: `uint8 a = 256` is spelled, and does not elaborate. -/
def overflow : Contract := { implicit with inits := [("a", .num 256)] }
example : (declarationParts tablesS [] overflow).isSome = true := rfl
example : Source.elaborates (envOf overflow) = false := rfl

/-- An invocation that names no modifier of the unit is spelled all the same;
`ModifiersResolve` is the obligation that fails. -/
def unresolved : Contract :=
  { explicit with ctor := some { ctor with mods := [⟨"only", [], [], [], [], []⟩] } }
example : (declarationParts tablesS [] unresolved).isSome = true := rfl
example : ((envOf unresolved).modifierAt (some "C") ⟨"only", []⟩).isSome = false := rfl

/-- An invocation whose name is a contract resolves as no modifier: Source
would read it as base-constructor arguments, which the model does not have.
`ModifiersResolve` excludes exactly this reading. -/
def baseLike : Contract :=
  { explicit with ctor := some { ctor with mods := [⟨"C", [], [], [], [], []⟩] } }
example : ((envOf baseLike).modifierAt (some "C") ⟨"C", []⟩).isSome = false ∧
    ((envOf baseLike).contractAt (some "C") ⟨"C", []⟩).isSome = true := ⟨rfl, rfl⟩
example : ¬ ModifiersResolve (envOf baseLike) (some "C")
    (.cons (.modInv ⟨"C", []⟩ (.some (.positional .nil))) .nil) :=
  fun h => absurd (h (⟨"C", []⟩, .some (.positional .nil)) (by simp [Source.Syn.invList]))
    (by rw [show ((envOf baseLike).modifierAt (some "C") ⟨"C", []⟩).isSome = false from rfl]; decide)

end Solidity.Examples.Lowering.Total.ConstructorDecode
