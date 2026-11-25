import Solidity.Correctness.Lowering.Total.ConstructorDecode

/-! Constructor and state-initializer declaration assembly: spelling, order,
refusals, and the unit that places the parts. Execution is not checked. -/
namespace Solidity.Examples.Lowering.Total.ConstructorDecode

open Solidity.Correctness.Lowering.Total Solidity.Correctness.Lowering.Total.Decode
open Solidity.Correctness.Lowering.Total.Decode.Constructor

def header (m : SourceMutability) : SourceFunction := { mutability := m, callable := .constructor }
def uint8 : Source.Elem := .int false 8 (by decide)
/-- `constructor(uint8 x) payable only(x) { b = x; }` -/
def ctor : FunDecl :=
  { sourceDecl := some (header .payable), params := [("x", .prim .uint)], widths := [("x", 8)],
    body := [.assign (.name "b") (.name "x")], mods := [⟨"only", [], [.name "x"], [], [], []⟩] }
/-- `uint8 a = 1; uint b; uint c = a + 2;` with that constructor, and without one. -/
def explicit : Contract :=
  { vars := [("a", .prim .uint), ("b", .prim .uint), ("c", .prim .uint)], widths := [("a", 8)],
    inits := [("a", .num 1), ("c", .binop .add (.name "a") (.num 2))], ctor := some ctor }
def implicit : Contract := { explicit with ctor := none }
def summary (C : Contract) := (declarationParts tablesS [] C).map fun p =>
  (p.collect (some "C")).map fun d => (d.kind, d.name, d.init?)
def envOf (C : Contract) : Source.Env := ((declarationParts tablesS [] C).map fun p =>
  (Source.Syn.unit (.cons (.contract false "C" .none .nil p) .nil)).env).getD ⟨[]⟩

/-- Parameter name and width, the invocation and its argument, the header's
payable status (the model flag is `false`) and the body are the original ones. -/
example : constructorPart tablesS [] ctor = some
    (.constructor (.cons (.param (.elem uint8) none (some "x")) .nil)
      (.cons (.modInv ⟨"only", []⟩ (.some (.positional (.cons (.ident "x") .nil)))) .nil) true none
      (.block (.cons (.stmtItem (.simpleStmt (.exprStmt
        (.assign .assign (.ident "b") (.ident "x"))))) .nil))) := rfl
/-- Refused, not guessed: no header, another role, `view`, a return, a reference parameter. -/
example : [{ ctor with sourceDecl := none }, { ctor with sourceDecl := some {} },
    { ctor with sourceDecl := some (header .viewFn) }, { ctor with rets := [("r", .prim .uint)] },
    { ctor with params := [("x", .ref (.array (.prim .uint)))] }].map
    (fun d => (constructorPart tablesS [] d).isSome) = [false, false, false, false, false] := rfl
/-- The constructor, then roots in order, each initializer on its own root. -/
example : summary explicit = some [(.constructor, "", none), (.stateVar, "a", some (num 1)),
    (.stateVar, "b", none), (.stateVar, "c", some (.addSub .add (.ident "a") (num 2)))] := rfl
/-- Refused: initializers out of root order, naming no root, two for one root, on
a transient root, with no spelling; an enum-marked root. -/
example : [{ explicit with inits := [("c", .num 3), ("a", .num 1)] },
    { explicit with inits := [("z", .num 1)] }, { explicit with inits := [("b", .num 1), ("b", .num 2)] },
    { explicit with transientRoots := ["b"], inits := [("b", .num 1)] },
    { explicit with inits := [("b", .tuple [])] }, { explicit with widths := [("b#enum", 2)] }].map
    (fun C => (declarationParts tablesS [] C).isSome) = [false, false, false, false, false, false] := rfl
/-- In the unit: initializers elaborate at the declared types, in order; the frame has
`x : uint8` and reads `msg.value`; no implicit constructor declaration; `uint8 a = 256`
does not elaborate; `only` fails `ModifiersResolve`, and `C` would be read as a base. -/
example : ((Source.progOf (envOf explicit)).inits "C").map (fun i => (i.var.name, i.τ)) =
    [("a", uint8.ty .storage), ("c", uintElem.ty .storage)] := rfl
example : ((envOf explicit).ctorFrame "C").map (fun f => (f.names, f.ps, f.rs, f.msgValue)) =
    some ([some "x"], [uint8.ty .memory], [], true) := rfl
example : (envOf implicit).ctorDecl "C" = none := rfl
example : Source.elaborates (envOf { implicit with inits := [("a", .num 256)] }) = false := rfl
example : ((envOf explicit).modifierAt (some "C") ⟨"only", []⟩).isSome = false ∧
    ((envOf explicit).modifierAt (some "C") ⟨"C", []⟩).isSome = false ∧
    ((envOf explicit).contractAt (some "C") ⟨"C", []⟩).isSome = true := ⟨rfl, rfl, rfl⟩
example {E : Source.Env} {p} (h : declarationParts tablesS [] explicit = some p) (hp : Placed E "C" p) :=
  And.intro (placed_inits h hp) (And.intro (placed_ctor h hp)
    (And.intro (@varDecl_elabInit E "C" uint8 false "a" (num 1)) (@elabMods_resolved E)))

end Solidity.Examples.Lowering.Total.ConstructorDecode
