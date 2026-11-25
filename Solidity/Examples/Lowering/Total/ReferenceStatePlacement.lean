import Solidity.Correctness.Lowering.Total.ReferenceStatePlacement

/-! Reference state roots and the constructor in assembled function units:
mixed primitive/reference roots, root and initializer order, explicit and
implicit constructors, a struct root the unit alone does not resolve, each
component failure, and agreement with the primitive placement. Execution is
not checked. -/
namespace Solidity.Examples.Lowering.Total.ReferenceStatePlacement

open Solidity.Correctness.Lowering.Total Solidity.Correctness.Lowering.Total.Decode
open Solidity.Correctness.Lowering.Total.ReferenceStatePlacement

/-- `constructor() payable { n = 2; }` -/
def ctor : FunDecl :=
  { sourceDecl := some { mutability := .payable, callable := .constructor }, params := [],
    body := [.assign (.name "n") (.num 2)] }
/-- `function get() internal view returns (uint r) { return z; }` -/
def get : FunDecl :=
  { sourceDecl := some { name := "get", mutability := .viewFn, callable := .local .internalFn },
    params := [], rets := [("r", .prim .uint)], body := [.ret (some (.name "z"))] }

/-- `uint8 n = 1; uint8[3][] xs; mapping(address => uint8[]) m; uint transient t;
uint[][2] ys; uint z = n + 2;` with the constructor. -/
def mixed : Contract :=
  { vars := [("n", .uint), ("xs", .ref (.array (.ref (.fixed .uint 3)))),
      ("m", .ref (.mapping .uint (.ref (.array .uint)))), ("t", .uint),
      ("ys", .ref (.fixed (.ref (.array .uint)) 2)), ("z", .uint)]
    widths := [("n", 8), ("xs[][]", 8), ("m{}#address", 20), ("m[][]", 8)]
    transientRoots := ["t"]
    inits := [("n", .num 1), ("z", .binop .add (.name "n") (.num 2))]
    ctor := some ctor }
/-- `mixed` with the implicit constructor. -/
def implicit : Contract := { mixed with ctor := none }
/-- `struct Pair { uint a; uint8 b; } uint8 n = 1; Pair p;`: a struct root. -/
def withStruct : Contract :=
  { vars := [("n", .uint), ("p", .ref (.struct "Pair{a:uint;b:uint8}"))], widths := [("n", 8)],
    structs := [("Pair", "Pair{a:uint;b:uint8}")], inits := [("n", .num 1)] }

def unitOf (C : Contract) (fs : List (Name × FunDecl)) : Option (Source.Syn .unit) :=
  (assemble tablesS [] C "C" fs).toOption
def table (C : Contract) (fs : List (Name × FunDecl)) :=
  (unitOf C fs).map fun u => u.decls.map fun d => (d.kind, d.name, d.scope)
def envOf (C : Contract) (fs : List (Name × FunDecl)) : Source.Env :=
  ((unitOf C fs).map Source.Syn.env).getD ⟨[]⟩

/-! The assembled units, evaluated; the theorems below are the general facts. -/

-- Explicit constructor, mixed roots, a function: the contract, the constructor,
-- every root in root order (primitive and reference alike), then `get`.
#guard table mixed [("get", get)] == some [(.contract, "C", none),
    (.constructor, "", some "C"), (.stateVar, "n", some "C"), (.stateVar, "xs", some "C"),
    (.stateVar, "m", some "C"), (.stateVar, "t", some "C"), (.stateVar, "ys", some "C"),
    (.stateVar, "z", some "C"), (.function, "get", some "C")]
-- The implicit constructor is the absence of a declaration.
#guard table implicit [] == some [(.contract, "C", none), (.stateVar, "n", some "C"),
    (.stateVar, "xs", some "C"), (.stateVar, "m", some "C"), (.stateVar, "t", some "C"),
    (.stateVar, "ys", some "C"), (.stateVar, "z", some "C")]
-- Roots in order with their transient flags; initializers in order on their roots.
#guard ((envOf mixed [("get", get)]).stateVarsOf "C").map (fun d => (d.name, d.isTransient)) ==
    [("n", false), ("xs", false), ("m", false), ("t", true), ("ys", false), ("z", false)]
#guard (((envOf mixed [("get", get)]).stateVarsOf "C").filter (·.init?.isSome)).map (·.name) ==
    ["n", "z"]
-- The constructor Source finds: explicit (payable header), implicit (none).
#guard ((envOf mixed [("get", get)]).ctorFrame "C").map (·.msgValue) == some true
#guard ((envOf implicit [("get", get)]).ctorDecl "C").isNone
-- The units elaborate; the program's initializers of `C` are `n`, then `z`.
#guard Source.elaborates (envOf mixed [("get", get)])
#guard ((Source.progOf (envOf mixed [("get", get)])).inits "C").map (·.var.name) == ["n", "z"]
#guard Source.elaborates (envOf implicit [])
#guard ((Source.progOf (envOf implicit [])).inits "C").map (·.var.name) == ["n", "z"]
#guard ((Source.progOf (envOf implicit [])).ctor "C").isNone
-- A struct root assembles, but the unit declares no `Pair`: its declared type
-- does not resolve there (its discharge needs the complete unit's structs).
#guard table withStruct [] == some [(.contract, "C", none), (.stateVar, "n", some "C"),
    (.stateVar, "p", some "C")]
#guard (((envOf withStruct []).stateVarsOf "C").map (·.varTy (envOf withStruct []))).map
    Option.isSome == [true, false]

/-! Component failures: each is the named gap of its component. -/

/-- An initializer out of root order: the reference state component refuses. -/
example : assemble tablesS [] { mixed with inits := [("z", .num 3), ("n", .num 1)] } "C" [] =
    .error (.state (.strayInit "n")) := rfl
/-- A constructor with no retained header: the constructor component refuses. -/
example : assemble tablesS [] { mixed with ctor := some { ctor with sourceDecl := none } } "C" [] =
    .error .constructor := rfl
/-- A function entry with no retained header: the function component refuses. -/
example : assemble tablesS [] mixed "C" [("get", { get with sourceDecl := none })] =
    .error .functions := rfl

/-! The exported facts, on an assembled unit. -/

example {u} (h : assemble tablesS [] mixed "C" [("get", get)] = .ok u) :=
  And.intro (assemble_owned h) (And.intro (assemble_roots h) (And.intro (assemble_ctor h)
    (And.intro (assemble_ctor_explicit h rfl) (assemble_functions h))))
example {u} (h : assemble tablesS [] implicit "C" [] = .ok u) := assemble_ctor_implicit h rfl
example {u} (h : assemble tablesS [] mixed "C" [] = .ok u) (hE : Source.elaborates u.env = true) :=
  assemble_inits h hE
/-- `mixed` mentions no struct, so the typing obligation is empty. -/
example {u} (h : assemble tablesS [] mixed "C" [] = .ok u) :=
  assemble_typed h (by
    intro v mv s ms
    simp only [mixed, List.mem_cons, List.not_mem_nil, or_false] at mv
    rcases mv with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [ReferenceDecode.structsTy, ReferenceDecode.structsRef] at ms)
/-- `Pair` resolves to nothing in the assembled unit alone. -/
example {u} (h : assemble tablesS [] withStruct "C" [] = .ok u) (d) :
    ¬ ReferenceDecode.Resolved u.env (some "C") "Pair" d := assemble_unresolved h _ _ _

/-! Agreement with the primitive placement on primitive roots. -/

/-- `uint8 a = 1; uint transient b; uint c = a + 2;` with the constructor. -/
def prims : Contract :=
  { vars := [("a", .uint), ("b", .uint), ("c", .uint)], widths := [("a", 8)], transientRoots := ["b"],
    inits := [("a", .num 1), ("c", .binop .add (.name "a") (.num 2))],
    ctor := some { ctor with body := [] } }
example : (prefixParts tablesS [] prims).toOption = Constructor.declarationParts tablesS [] prims := rfl
example : unitOf prims [("get", get)] =
    (Constructor.declarationParts tablesS [] prims).bind
      (Callee.withFunctions tablesS [] "C" · [("get", get)]) := rfl
example {p u} (hp : Constructor.declarationParts tablesS [] prims = some p)
    (h : assemble tablesS [] prims "C" [("get", get)] = .ok u) :=
  assemble_primitive_slots hp h
/-- `mixed` has reference roots: the primitive component refuses, this one does not. -/
example : (Constructor.declarationParts tablesS [] mixed).isNone ∧
    (prefixParts tablesS [] mixed).toOption.isSome := ⟨rfl, rfl⟩

end Solidity.Examples.Lowering.Total.ReferenceStatePlacement
