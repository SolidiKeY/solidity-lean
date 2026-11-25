import Solidity.Correctness.Lowering.Total.ReferenceStateDecode

/-! Reference state-root declarations: one mixed root list with nested arrays,
mappings, a struct by its written name, a transient primitive and initializers;
its Source types; every named failure; agreement with the primitive components. -/
namespace Solidity.Examples.Lowering.Total.ReferenceStateDecode

open Solidity.Correctness.Lowering.Total Solidity.Correctness.Lowering.Total.Decode
open Solidity.Correctness.Lowering.Total.ReferenceStateDecode Source

def pair : Ty := .ref (.struct "Pair{a:uint;b:uint8}")
def u8 : Syn .typeName := .elem (.int false 8 (by decide))
def u256 : Syn .typeName := .elem uintElem
def var (t : Syn .typeName) (transient : Bool) (x : Name) (init : Syn (.opt .expr)) :
    Syn (.part false) := .stateVar t none none none transient x init

/-- `struct Pair { uint a; uint8 b; }` (encoded `Pair{a:uint;b:uint8}`) and
`uint8 n = 1; uint8[3][] xs; mapping(address => uint8[]) m; Pair p;
mapping(uint => Pair[]) ps; uint transient t; uint[][2] ys; uint z = n + 2;`. -/
def mixed : Contract :=
  { vars := [("n", .uint), ("xs", .ref (.array (.ref (.fixed .uint 3)))),
      ("m", .ref (.mapping .uint (.ref (.array .uint)))), ("p", pair),
      ("ps", .ref (.mapping .uint (.ref (.array pair)))), ("t", .uint),
      ("ys", .ref (.fixed (.ref (.array .uint)) 2)), ("z", .uint)]
    widths := [("n", 8), ("xs[][]", 8), ("m{}#address", 20), ("m[][]", 8)]
    transientRoots := ["t"]
    structs := [("Pair", "Pair{a:uint;b:uint8}")]
    inits := [("n", .num 1), ("z", .binop .add (.name "n") (.num 2))] }

/-- Every root once, in order: nesting, lengths, widths, the mapping key, the
written struct name, the transient flag, and each initializer on its own root. -/
theorem mixed_state : state tablesS [] mixed = .ok
    (.cons (var u8 false "n" (.some (num 1)))
    (.cons (var (.array (.array u8 (.some (num 3))) .none) false "xs" .none)
    (.cons (var (.mapping (.elem .address (by decide)) none (.array u8 .none) none) false "m" .none)
    (.cons (var (.userType ⟨"Pair", []⟩) false "p" .none)
    (.cons (var (.mapping (.elem uintElem (by decide)) none
      (.array (.userType ⟨"Pair", []⟩) .none) none) false "ps" .none)
    (.cons (var u256 true "t" .none)
    (.cons (var (.array (.array u256 .none) (.some (num 2))) false "ys" .none)
    (.cons (var u256 false "z" (.some (.addSub .add (.ident "n") (num 2)))) .nil)))))))) := rfl

example : (state tablesS [] mixed).map (fun p => (p.collect (some "C")).map (·.name)) =
    .ok (mixed.vars.map (·.1)) := rfl
example {p} (h : state tablesS [] mixed = .ok p) := partsOf_names h "C"

/-- The declared Source types, once `Pair` resolves to a declaration `d`. -/
example (E : Source.Env) (d : Source.DeclName) (h : ReferenceDecode.Resolved E (some "C") "Pair" d) :
    ∃ p, state tablesS [] mixed = .ok p ∧ (p.collect (some "C")).map (·.varTy E) =
      [some (.int ⟨false, 8, by decide⟩),
        some (.array .storage (.array .storage (.int ⟨false, 8, by decide⟩) (some 3)) none),
        some (.mapping (.address false) (.array .storage (.int ⟨false, 8, by decide⟩) none)),
        some (.struct .storage d),
        some (.mapping (.int ⟨false, 256, by decide⟩) (.array .storage (.struct .storage d) none)),
        some (.int ⟨false, 256, by decide⟩),
        some (.array .storage (.array .storage (.int ⟨false, 256, by decide⟩) none) (some 2)),
        some (.int ⟨false, 256, by decide⟩)] :=
  ⟨_, mixed_state, by
    have none : Source.arrayLen .none = some none := rfl
    have len : ∀ n, n ≠ 0 → Source.arrayLen (.some (num n)) = some (some n) :=
      fun _ => ReferenceDecode.arrayLen_lenLit
    simp [Source.Syn.collect, Source.Decl.varTy, Source.Syn.ty, Source.Syn.tys, h.userTy,
      Source.Env.keyTy, len, none, var, u8, u256, uintElem, Source.Elem.ty]⟩

/-- The exported typing fact: only struct resolution is asked. -/
example (E : Source.Env) (d : Source.DeclName) (h : ReferenceDecode.Resolved E (some "C") "Pair" d)
    {p} (hp : state tablesS [] mixed = .ok p) :=
  state_typed (E := E) hp "C" (by
    intro v mv s ms w hw
    have : s = "Pair{a:uint;b:uint8}" := by
      simp only [mixed, List.mem_cons, List.not_mem_nil, or_false] at mv
      rcases mv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [ReferenceDecode.structsTy, ReferenceDecode.structsRef, pair] at ms <;> exact ms
    subst this; cases hw; exact ⟨d, h⟩)

/-- In a unit declaring `Pair` and placing the parts, Source itself resolves the
struct and finds the roots in order at these types; the initializers elaborate. -/
def unit : Syn .unit := ((state tablesS [] mixed).toOption.map fun p =>
  Syn.unit (.cons (.contract false "C" .none .nil
    (.cons (.struct "Pair" (.structMember u256 "a") (.cons (.structMember u8 "b") .nil)) p))
    .nil)).getD (.unit .nil)
example : (unit.env.stateVarsOf "C").map (fun d => (d.name, d.isTransient, (d.varTy unit.env).isSome)) =
    [("n", false, true), ("xs", false, true), ("m", false, true), ("p", false, true),
      ("ps", false, true), ("t", true, true), ("ys", false, true), ("z", false, true)] := by decide
example : ((unit.env.stateVarsOf "C").drop 3).head?.bind (·.varTy unit.env) =
    some (.struct .storage ⟨some "C", "Pair"⟩) := by decide
example : ((Source.progOf unit.env).inits "C").map (fun i => i.var.name) = ["n", "z"] := by decide

/-! Failures: each names the root and the reason; nothing is dropped. -/

local macro "one! " T:term:max w:term:max s:term:max : term =>
  `(({ vars := [("a", .uint), ("r", $T)], widths := $w, structs := $s } : Contract))

-- An enum-marked primitive root; an enum element; a function-type element; a stale root row.
example : state tablesS [] (one! .uint [("r#enum", 2)] []) = .error (.noElem "r" .uint) := rfl
example : state tablesS [] (one! (.ref (.array .uint)) [("r[]#enum", 2)] []) =
    .error (.unreadRow "r" "r[]#enum" 2) := rfl
example : state tablesS [] (one! (.ref (.array .uint)) [("r[]#function()", 1)] []) =
    .error (.unreadRow "r" "r[]#function()" 1) := rfl
example : state tablesS [] (one! (.ref (.array .uint)) [("r", 8)] []) = .error (.unreadRow "r" "r" 8) := rfl
-- `bytes` and `bytes1[]` share their rows; a zero length; a non-elementary key.
example : state tablesS [] (one! (.ref (.array .uint)) [("r[]", 8), ("r[]#bytes", 1)] []) =
    .error (.type "r" (.erasedBytes "r")) := rfl
example : state tablesS [] (one! (.ref (.fixed .uint 0)) [] []) = .error (.type "r" (.zeroLength "r")) := rfl
example : state tablesS [] (one! (.ref (.mapping .uint (.ref (.array .uint)))) [("r{}", 7)] []) =
    .error (.type "r" (.unrepresentable "r{}" .uint)) := rfl
-- A struct no identifier is read as; one two identifiers are read as.
example : state tablesS [] (one! (.ref (.array (.ref (.struct "A{a:uint}")))) [] []) =
    .error (.type "r" (.unknownStruct "r[]" "A{a:uint}")) := rfl
example : state tablesS [] (one! (.ref (.struct "A{a:uint}")) [] [("A", "A{a:uint}"), ("B", "A{a:uint}")]) =
    .error (.type "r" (.ambiguousStruct "r" "A{a:uint}" ["A", "B"])) := rfl
-- Initializers: out of root order, naming no root, on a transient root, unspelled.
example : state tablesS [] { mixed with inits := [("z", .num 3), ("n", .num 1)] } =
    .error (.strayInit "n") := rfl
example : state tablesS [] { mixed with inits := [("q", .num 1)] } = .error (.strayInit "q") := rfl
example : state tablesS [] { mixed with inits := [("t", .num 1)] } = .error (.transientInit "t") := rfl
example : state tablesS [] { mixed with inits := [("xs", .tuple [])] } =
    .error (.unspelledInit "xs" (.tuple [])) := rfl
/-- An initializer of a reference root stays on it, as spelled. -/
example : (state tablesS [] { mixed with inits := [("ys", .name "xs")] }).map
    (fun p => (p.collect (some "C")).filterMap fun d => d.init?.map (d.name, ·)) =
    .ok [("ys", .ident "xs")] := rfl
/-- A transient reference root: no contract has one (`ref_not_transient`). -/
example : partsOf (rootType mixed (TransientDecode.elemOf mixed)) (fun _ => true) (Calls.expr tablesS [])
    [("q", .ref (.array .uint))] [] = .error (.transientReference "q") := rfl
example (r : Name) := state_ne_transientReference tablesS [] mixed r
/-- A refused constructor (no retained header) is a failure of the assembly. -/
example : declarationParts tablesS [] { mixed with ctor := some { params := [], body := [] } } =
    .error .constructor := rfl

/-! Agreement with the primitive components on primitive roots. -/

def prims : Contract :=
  { vars := [("a", .uint), ("b", .uint), ("c", .uint)], widths := [("a", 8)], transientRoots := ["b"],
    inits := [("a", .num 1), ("c", .binop .add (.name "a") (.num 2))] }
example : (declarationParts tablesS [] prims).toOption = Constructor.declarationParts tablesS [] prims := rfl
example : (state tablesS [] { prims with inits := [] }).toOption =
    (TransientDecode.decls { prims with inits := [] }).toOption := rfl
example {p} (h : Constructor.declarationParts tablesS [] prims = some p) :
    declarationParts tablesS [] prims = .ok p := declarationParts_compat.1 h
example {E : Source.Env} {p} (h : declarationParts tablesS [] mixed = .ok p)
    (hp : Constructor.Placed E "C" p) := placed_declarations h hp

end Solidity.Examples.Lowering.Total.ReferenceStateDecode
