import Lean.Data.Json
import Solidity.Syntax
import Solidity.Frontend.Source

/-!
# solc's JSON: types, expressions and statements

What is left out and why, reading the JSON, types, and expressions and
statements.

A piece of `Frontend/SolcJson.lean`, whose docstring describes the whole.
-/

namespace Solidity.Frontend

open Lean (Json)

open Semantics

/-- Quote only emitted syntax. Semantic names and declaration lookup keys stay
raw, including Solidity's `$` names and names that Lean reserves. -/
def identText (name : String) : String :=
  if name.isEmpty then "" else "«" ++ name ++ "»"

/-- A resolved type is either a primitive spelling or a declared identifier. -/
def typeIdentText (name : String) : String :=
  if ["bool", "address", "address payable", "string", "bytes", "uint", "int"].contains name ||
      (narrowTy? name).isSome || (bytesTy? name).isSome then name else identText name


/-- Why a function, or a state variable, is left out. -/
inductive Gap where
  /-- The model has no counterpart (`docs/testsuite-proofs.md` lists them). -/
  | excluded (msg : String) (line : Nat := 0)
  /-- The printer or the grammar lacks the form. -/
  | unsupported (msg : String) (line : Nat := 0)
  deriving Repr, Inhabited

def Gap.msg : Gap → String
  | .excluded m _ | .unsupported m _ => m

/-- The source line of the statement it arose in, `0` if none. -/
def Gap.line : Gap → Nat
  | .excluded _ l | .unsupported _ l => l

/-- Scope diagnostics retain their category in the import report; the body
reader uses the existing two lowering outcomes. -/
def Source.Diagnostic.toGap (d : Source.Diagnostic) : Gap :=
  match d.kind with
  | .excluded => .excluded s!"{d.name}: {d.reason}" d.line
  | _ => .unsupported s!"{d.name}: {d.reason}" d.line

def Source.ScopeScan.ensure (scan : Source.ScopeScan) : Except Gap Unit :=
  match scan.diagnostic? with
  | none => .ok ()
  | some diagnostic => .error diagnostic.toGap

/-- solkey's obligation for a function, from its `@custom:key` clauses and
its contract's (`tagOf`). -/
inductive Tag where
  /-- unspecified: `⟨f⟩ true` -/
  | diamond
  /-- unspecified, `@custom:key box`: `[f] true` -/
  | box
  /-- `@custom:key skip`: no obligation -/
  | skip
  /-- a `requires`, `ensures` or `invariant` clause, its own or its
  contract's: solkey's obligation is the specification's, not stated here -/
  | specified
  /-- neither `public` nor `external`: solkey states no obligation -/
  | internal
  /-- a clause solkey refuses to read: no obligation -/
  | malformed
  deriving Repr, DecidableEq, Inhabited

def Tag.toStr : Tag → String
  | .diamond => "diamond"
  | .box => "box"
  | .skip => "skip"
  | .specified => "specified"
  | .internal => "internal"
  | .malformed => "malformed"

/-- A function as read: its parameters (name, `sol` type) and its body as
statements of `sol` text, or why there is none. -/
structure SolcFun where
  name : String
  /-- The Solidity name, before disambiguating overloaded declarations. -/
  sourceName : String := ""
  /-- Exact source role and ABI identity, before model-name/type lowering. -/
  sourceDecl : Option SourceFunction := none
  /-- The source parameter types, before enums, aliases or addresses are lowered. -/
  sourceSignature : String := ""
  /-- The scope scan is independent of the implementation inventory. -/
  sourceScope : Source.ScopeScan := default
  /-- Modifier applications in source order, for the existing inliner. -/
  modifierApps : String := ""
  line : Nat
  tag : Tag
  params : List (String × String)
  /-- The statements, each with the source line of the statement it prints. -/
  body : Except Gap (List (Nat × String))
  /-- Its return variables (name, `sol` type), the name `""` when unnamed. -/
  rets : List (String × String) := []
  /-- The functions of the contract it calls, directly or not, callees first. -/
  calls : List String := []
  /-- Declared `payable`: what a constructor's member keeps (`Contract.deploy`
  refuses value sent to one that is not). -/
  payable : Bool := false
  /-- It, a modifier it applies or a function it calls holds a `writingCall`. -/
  writingCall : Bool := true
  /-- The parameters the ABI decoder bounds below their `PrimTy`'s range: a
  narrow integer's, an enum's members (name, least, greatest value). -/
  paramRanges : List (String × Int × Int) := []
  /-- The memory array parameters whose elements the ABI decoder bounds so:
  name, least and greatest value, and a fixed array's length. -/
  elemRanges : List (String × Int × Int × Option Nat) := []
  /-- Specification members, retained only for the testing import mode. -/
  specMembers : String := ""
  /-- Raw directive/text pairs, for validating one clause at a time before
  interpolating them into a contract member. -/
  specClauses : List (String × String) := []
  deriving Inhabited

/-- A contract as read: the `contract!` members of the state variables it
keeps, the ones it leaves out and why, its functions. -/
structure SolcContract where
  name : String
  members : List String
  dropped : List (String × Gap)
  funs : List SolcFun
  /-- The functions some function, the constructor or an initializer calls,
  each as its `contract!` member (`function f(uint x) returns (uint) { … }`),
  callees first. -/
  funMembers : List (String × String) := []
  /-- Compiler lowering helpers are callable only by their generated direct
  calls; they do not denote source-level function values or ABI entries. -/
  internalFuns : List String := []
  /-- Metadata for emitted function members, including synthesized getters. -/
  sourceDecls : List (String × SourceFunction) := []
  modifierMembers : List String := []
  /-- The constructor, named `constructor` (solc names it `""`), if the
  contract declares one. -/
  ctor : Option SolcFun := none
  /-- `members`, each state variable with an initializer written with it
  (`uint x = 5;`), in declaration order: what a deployment runs first.
  `members` itself when none has one, or when one does not print
  (`initGap`). -/
  initMembers : List String := []
  /-- Why an initializer does not print, if one does not: the constructor
  is then left out, since a deployment would skip it. -/
  initGap : Option Gap := none
  deriving Inhabited

/-! ## Reading the JSON -/

namespace J

def get (j : Json) (k : String) : Except Gap Json :=
  match j.getObjVal? k with
  | .ok v => pure v
  | .error e => throw (.unsupported s!"solc JSON: {e}")

def opt (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with
  | .ok .null => none
  | .ok v => some v
  | .error _ => none

def str (j : Json) (k : String) : Except Gap String :=
  match j.getObjValAs? String k with
  | .ok v => pure v
  | .error e => throw (.unsupported s!"solc JSON: {e}")

def arr (j : Json) (k : String) : Except Gap (List Json) := do
  match (← get j k).getArr? with
  | .ok a => pure a.toList
  | .error e => throw (.unsupported s!"solc JSON: {e}")

/-- The string at `k`, if there is one. -/
def str? (j : Json) (k : String) : Option String := (j.getObjValAs? String k).toOption

/-- The array at `k`, if there is one. -/
def arr? (j : Json) (k : String) : Option (Array Json) := (opt j k).bind (·.getArr?.toOption)

/-- The array at `k`, empty if there is none. -/
def arrD (j : Json) (k : String) : Array Json := (arr? j k).getD #[]

def kind (j : Json) : String := (J.str? j "nodeType").getD ""

def line (j : Json) : Nat := (j.getObjValAs? Nat "line").toOption.getD 0

def ref? (j : Json) : Option Int := (j.getObjValAs? Int "referencedDeclaration").toOption

def id? (j : Json) : Option Int := (j.getObjValAs? Int "id").toOption

/-- solc's type of an expression, `typeDescriptions.typeString`. -/
def tyStr (j : Json) : String :=
  ((j.getObjVal? "typeDescriptions").toOption.bind
    fun t => J.str? t "typeString").getD ""

/-- Nominal scalar identity retained by modern fixtures for user-defined value types. -/
def tyId (j : Json) : String :=
  ((J.opt j "typeDescriptions").bind (J.str? · "typeIdentifier")).getD ""

/-- The annotation belongs to an operator, including malformed/null annotations. -/
def hasOperatorFunction (j : Json) : Bool :=
  ["UnaryOperation", "BinaryOperation"].contains (kind j) &&
    (j.getObjVal? "function").isOk

/-- An operator's resolved callee, when its annotation is an integer. -/
def operatorFunction? (j : Json) : Option Int :=
  if hasOperatorFunction j then (j.getObjValAs? Int "function").toOption else none

/-- A nominal type node names its compiler declaration, including path nodes. -/
def typeRef? (j : Json) : Option Int :=
  (ref? j).orElse fun _ => (opt j "pathNode").bind ref?

/-- The names of the variable declarations among `ns`. -/
def varDeclNames (ns : List Json) : List String :=
  ns.filterMap fun n => if kind n == "VariableDeclaration" then str? n "name" else none

/-- Every node of `j`, depth first. -/
partial def nodes (j : Json) : List Json :=
  match j with
  | .arr a => a.toList.flatMap nodes
  | .obj kvs =>
    let sub := kvs.toList.flatMap fun (_, v) => nodes v
    if (j.getObjVal? "nodeType").isOk then j :: sub else sub
  | _ => []

end J

/-- Solc gives language builtins negative declaration identities. -/
def builtinNamed (node : Json) (name : String) : Bool :=
  J.kind node == "Identifier" && J.str? node "name" == some name &&
    (J.ref? node).any (· < 0)

def nativeMember (node : Json) : Bool := (J.ref? node).all (· < 0)

/-! ## Types -/

/-- Lean's reserved words a Solidity local could be named. -/
def leanKeywords : List String :=
  ["at", "by", "do", "fun", "have", "show", "from", "in", "let", "then", "with", "where",
   "match", "end", "open", "import", "structure", "class", "instance", "theorem", "def",
   "example", "abbrev", "namespace", "section", "variable", "universe", "local", "macro",
   "syntax", "deriving", "mutual", "partial", "private", "protected", "noncomputable",
   r"unsafe", "calc", "suffices", "obtain", "nomatch", "nofun", "forall", "exists", "Type",
   "to", "count", "listing",
   "Sort", "Prop", "if", "else", "for", "unless", "return", "try", "catch", "finally",
   "break", "continue", "mut", "rec", "fun", "λ", "delete", "new", "true", "false"]

/-- The structs as the import reads them: the Solidity name, and the table's
name or why it is left out. -/
abbrev Structs := List (String × Except Gap String)

/-- The `sol` spelling of an elementary type. -/
def elemTy (name : String) (payable : Bool) : String :=
  match name with
  | "uint256" => "uint"
  | "int256" => "int"
  | "address" => if payable then "address payable" else "address"
  | n => n

/-- Normalize elementary source type tokens without changing user-defined names. -/
def sourceType (s : String) : String := Id.run do
  let normalize (t : String) : String :=
    if t == "uint256" then "uint" else if t == "int256" then "int" else t
  let mut word := ""
  let mut out := ""
  for c in s.toList do
    if c.isAlphanum || c == '_' || c == '$' then word := word.push c
    else
      out := (out ++ normalize word).push c
      word := ""
  return out ++ normalize word

/-- Contextual source casts retain the kind inspected by ABI and arrays. -/
def sourceCast (t value : String) : String :=
  if t == "bool" then s!"({value})"
  else if t == "address" || t == "address payable" then s!"address({value})"
  else s!"{t}({value})"

/-- Function visibility from the outer type only. A nested parameter or return
may itself be an external function; that must not admit an internal receiver.
Normalized compiler fixtures may omit `typeIdentifier`, so inspect the same
source type string that the rest of the reader consumes. -/
private def externalFunctionType (ty : String) : Bool := Id.run do
  if !ty.startsWith "function " then return false
  let mut depth : Nat := 0
  let mut outer := ""
  for c in ty.toList do
    if c == '(' || c == '[' then
      if depth == 0 then outer := outer.push ' '
      depth := depth + 1
    else if c == ')' || c == ']' then
      depth := depth - 1
      if depth == 0 then outer := outer.push ' '
    else if depth == 0 then outer := outer.push c
  let words := (outer.split Char.isWhitespace).filter (· != "")
  return words.contains "external" && !words.contains "internal"

/-- A stored external function projection whose numeric lowering may safely
read the receiver twice. Restrict receivers to stable places: the native
selector lowering duplicates its receiver, so calls, increments and assignments
must stay refused until that lowering captures their value exactly once.
The explicit result cast preserves the ABI kind after `fnPure` erases the
function marker into arithmetic. -/
def storedFunctionMemberType? (j : Json) : Option String := do
  guard (J.kind j == "MemberAccess")
  let member ← J.str? j "memberName"
  let result ← match member with
    | "address" => some "address"
    | "selector" => some "bytes4"
    | _ => none
  guard (J.tyStr j == result)
  let receiver ← J.opt j "expression"
  guard (externalFunctionType (J.tyStr receiver))
  let desc ← J.opt receiver "typeDescriptions"
  if let some typeId := J.str? desc "typeIdentifier" then
    guard (typeId.startsWith "t_function_external_")
  guard ((J.nodes receiver).all fun node =>
    ["Identifier", "MemberAccess", "IndexAccess", "Literal"].contains (J.kind node) ||
      (J.kind node == "TupleExpression" && (J.arrD node "components").size == 1))
  pure result

/-- The evaluated outer dimension supplied by solc. A named bound has no
literal `value`; nested types must use their last, outermost dimension. -/
def solcArrayLength? (j : Json) : Option Nat := do
  let suffix ← ((J.tyStr j).splitOn "[").getLast?
  let digits := suffix.takeWhile Char.isDigit
  guard (!digits.isEmpty && (suffix.drop digits.length).startsWith "]")
  digits.toNat?

/-- A type node as `sol` text: a mapping's `bool` key is its `uint`.  A narrow
type may stand inside it (`expandStateTyW`, `elabTyW`). -/
partial def tyText (S : Structs) (j : Json) : Except Gap String := do
  match J.kind j with
  | "ElementaryTypeName" =>
    let n ← J.str j "name"
    pure (elemTy n ((J.opt j "stateMutability").any (· == .str "payable")))
  | "UserDefinedTypeName" =>
    if let some id := (J.ref? j).orElse fun _ => (J.opt j "pathNode").bind J.ref? then
      match lookupBy s!"#solc{id}" S with
      | some resolved => return typeIdentText (← resolved)
      | none => throw (.unsupported s!"type declaration #{id} is not among the visible validated types")
    let n ← match J.opt j "pathNode" with
      | some p => J.str p "name"
      | none => J.str j "name"
    match lookupBy n S with
    | some (.ok m) => pure (typeIdentText m)
    | some (.error g) => throw g
    | none => throw (.unsupported s!"type `{n}` is not a struct of the contract")
  | "ArrayTypeName" =>
    let b ← tyText S (← J.get j "baseType")
    match J.opt j "length" with
    | none => pure s!"{b}[]"
    | some l =>
      let some n := (solcArrayLength? j).orElse fun _ => (J.str? l "value").bind String.toNat?
        | throw (.unsupported "an array without its evaluated compiler bound")
      pure s!"{b}[{n}]"
  | "Mapping" =>
    let k ← tyText S (← J.get j "keyType")
    let k := if k == "bool" then "uint" else k
    let v ← tyText S (← J.get j "valueType")
    pure s!"mapping({k} => {v})"
  | "FunctionTypeName" =>
    -- an internal function type, its tag a `uint` (`fnTy?`); an external
    -- one is printed too, and a call through it refused by the elaborator
    let ps := ((J.opt j "parameterTypes").bind (J.arr? · "parameters")).getD #[] |>.toList
    let rs := ((J.opt j "returnParameterTypes").bind (J.arr? · "parameters")).getD #[] |>.toList
    if (ps ++ rs).any fun p => ["memory", "storage", "calldata"].contains ((J.str? p "storageLocation").getD "") then
      throw (.unsupported "a function type with a reference parameter or return")
    let ps ← ps.mapM fun p => do tyText S (← J.get p "typeName")
    let rs ← rs.mapM fun p => do tyText S (← J.get p "typeName")
    let ext := if J.str? j "visibility" == some "external" then " external" else ""
    let ret := if rs.isEmpty then "" else s!" returns ({", ".intercalate rs})"
    pure s!"function ({", ".intercalate ps}){ext}{ret}"
  | k => throw (.unsupported s!"type node `{k}`")


/-- A type written where `abi.decode` reads one, `(uint[], S)`: an
elementary type's name, `T[]` and `T[k]` of one (`IndexAccess`), a struct by
its name in the table (`Identifier`); the elaborator decodes them
(`abiDecodeWith`). -/
partial def abiTyText (S : Structs) (t : Json) : Except Gap String := do
  match J.kind t with
  | "ElementaryTypeNameExpression" => J.str (← J.get t "typeName") "name"
  | "IndexAccess" =>
    let b ← abiTyText S (← J.get t "baseExpression")
    match J.opt t "indexExpression" with
    | none | some .null => pure s!"{b}[]"
    | some k =>
      match (solcArrayLength? t).orElse fun _ => (J.str? k "value").bind String.toNat? with
      | some n => pure s!"{b}[{n}]"
      | none => throw (.unsupported "abi.decode to an array without its evaluated compiler bound")
  | "Identifier" =>
    match (J.ref? t).bind fun id => lookupBy s!"#solc{id}" S with
    | some (.ok m) => pure (typeIdentText m)
    | _ => throw (.unsupported "abi.decode to a type other than a value type, an array of values \
        or a struct")
  | _ => throw (.unsupported "abi.decode to a type other than a value type, an array of values \
      or a struct")
/-- A type node as a `Ty`, to compare a struct's members with the table: a
narrow type is its `uint`/`int` (its width is `narrowShape`'s). -/
partial def tyOf (S : List (String × String)) (j : Json) : Except String Ty := do
  match J.kind j with
  | "ElementaryTypeName" =>
    let n ← (j.getObjValAs? String "name")
    match PrimTy.ofName? n, narrowTy? n with
    | some p, _ | none, some (p, _) => pure (.prim p)
    | none, none =>
      -- a `bytesN` is a `uint`, `bytes` and `string` a `uint[]` (`valueRows?`)
      if (bytesTy? n).isSome then pure .uint
      else if dynBytesTy n then pure (.ref (.array .uint))
      else throw s!"type `{n}`"
  | "UserDefinedTypeName" =>
    if let some id := (J.ref? j).orElse fun _ => (J.opt j "pathNode").bind J.ref? then
      match lookupBy s!"#solc{id}" S with
      | some m => return .ref (.struct m)
      | none => throw s!"type declaration #{id} is not among the visible structs"
    let n ← match (j.getObjVal? "pathNode").toOption with
      | some p => p.getObjValAs? String "name"
      | none => j.getObjValAs? String "name"
    pure (.ref (.struct ((lookupBy n S).getD n)))
  | "ArrayTypeName" =>
    let b ← tyOf S (← j.getObjVal? "baseType")
    match (j.getObjVal? "length").toOption with
    | none | some .null => pure (.ref (.array b))
    | some l =>
      match (solcArrayLength? j).orElse fun _ => (J.str? l "value").bind String.toNat? with
      | some n => pure (.ref (.fixed b n))
      | none => throw "array without its evaluated compiler bound"
  | "Mapping" =>
    let key ← j.getObjVal? "keyType"
    -- a byte string as a key: its `keccak256`, a `uint` (`hashKeyRows`)
    let keyTy ← if dynBytesTy ((J.str? key "name").getD "") then pure Ty.uint else tyOf S key
    match keyTy with
    | .prim k => pure (.ref (.mapping k (← tyOf S (← j.getObjVal? "valueType"))))
    | t => throw s!"mapping key `{t.toStr}`"
  -- a function type's value is a tag (`fnTy?`)
  | "FunctionTypeName" => pure .uint
  | k => throw s!"type node `{k}`"

/-- The narrow positions of a type node, keyed by their path below it as
`Semantics.structWidths` keys a member's (`uint8[]` is `[("[]", 8)]`). -/
partial def narrowShape (j : Json) : List (String × Nat) :=
  match J.kind j with
  | "ElementaryTypeName" =>
    let n := (J.str? j "name").getD ""
    -- an `address`'s marker is not compared: the table's structs carry none
    if dynBytesTy n then dynBytesRowsOf n
    else (((valueRows? n).map (·.2)).getD []).filter (·.1 != "#address")
  | "ArrayTypeName" =>
    ((J.opt j "baseType").map narrowShape).getD [] |>.map fun (k, n) => ("[]" ++ k, n)
  | "Mapping" =>
    let key := (J.opt j "keyType").getD .null
    (if dynBytesTy ((J.str? key "name").getD "") then hashKeyRows
      else narrowShape key |>.map fun (k, n) => ("{}" ++ k, n)) ++
      (((J.opt j "valueType").map narrowShape).getD [] |>.map fun (k, n) => ("[]" ++ k, n))
  -- a function type's marker: no struct of the table has one
  | "FunctionTypeName" => [("#function", 0)]
  | _ => []

/-- Does the type node name the struct `s`? -/
partial def mentionsStruct (s : String) (j : Json) : Bool :=
  (J.nodes j).any fun n =>
    J.kind n == "UserDefinedTypeName" &&
      ((J.opt n "pathNode").bind (fun p => J.str? p "name")) == some s

/-- Does a mapping inside the type node name the struct `s`? -/
def mentionsThroughMapping (s : String) (j : Json) : Bool :=
  (J.nodes j).any fun n => J.kind n == "Mapping" && mentionsStruct s n

/-- The visible structs: each renamed by `ren`, the table's under its name
when its members are the table's, in order, at the same types (and narrow
widths), else the contract's own, which the import declares as a `struct`
member (`ownStructMembers`), under its name, or `S_<id>` when another visible
struct has that name.  Declaration keys preserve solc's resolution when a
contract shadows a file-level name.  Also the own ones, by declaration. -/
def readStructs (ren : List (String × String)) (defs : List Json) :
    Structs × List (Json × String) := Id.run do
  let printed (d : Json) : String :=
    let n := (J.str? d "name").getD ""
    let m := (lookupBy n ren).getD n
    let clash := defs.any fun e => J.str? e "name" == some n && J.id? e != J.id? d
    if clash then s!"{m}_{(J.id? d).getD 0}" else m
  let identities := defs.filterMap fun d => do
    let i ← J.id? d
    pure (s!"#solc{i}", printed d)
  let shapes := defs.map fun d =>
    let n := (J.str? d "name").getD ""
    let m := (lookupBy n ren).getD n
    let line := J.line d
    let check : Except Gap (String × Bool) := do
      let ms ← J.arr d "members"
      if ms.any (fun x => (J.opt x "typeName").any (mentionsThroughMapping n)) then
        throw (.excluded s!"struct `{n}` (line {line}) is recursive through a mapping: \
          its default value is infinite, and the model's are finite")
      if ms.any (fun x => (J.opt x "typeName").any (mentionsStruct n)) then
        throw (.unsupported s!"struct `{n}` (line {line}) is recursive through an array: \
          the struct table is well-founded by rank (`structDef_rank_lt`), so no struct \
          contains itself")
      let got ← ms.mapM fun x => do
        let f ← J.str x "name"
        match tyOf (identities ++ ren) (← J.get x "typeName") with
        | .ok t => pure (f, t)
        | .error e => throw (.unsupported s!"struct `{n}`, member `{f}`: {e}")
      -- the narrow members' widths, against the table's (`structWidths`)
      let widths := ms.flatMap fun x =>
        (narrowShape ((J.opt x "typeName").getD .null)).map fun (k, n) =>
          ((J.str? x "name").getD "" ++ k, n)
      let tw := structWidths m
      let sameW := widths.all (tw.contains ·) && tw.all (widths.contains ·)
      if structDef m == got && sameW && printed d == m then pure (m, false)
      else pure (printed d, true)
    (d, n, check)
  let mut checked := shapes
  -- A table-shaped parent also requires every actual referenced declaration
  -- to pass. Propagate failures through at most one edge per round.
  for _ in [:defs.length] do
    checked := checked.map fun (d, n, shape) =>
      let checkedShape : Except Gap (String × Bool) := do
        let (m, own) ← shape
        -- a table-shaped struct whose member is an own struct is an own one
        let mut own := own
        for member in (← J.arr d "members") do
          let typeNode ← J.get member "typeName"
          for node in (J.nodes typeNode).filter (J.kind · == "UserDefinedTypeName") do
            let some id := (J.ref? node).orElse fun _ => (J.opt node "pathNode").bind J.ref?
              | throw (.unsupported s!"struct `{n}` has a member type without declaration identity")
            let some (_, dep, result) := checked.find? fun (decl, _, _) => J.id? decl == some id
              | throw (.unsupported s!"struct `{n}` refers to an unvalidated type declaration #{id}")
            match result with
            | .ok (_, depOwn) => own := own || depOwn
            | .error _ => throw (.unsupported s!"struct `{n}` depends on invalid struct `{dep}`")
        pure (if own then printed d else m, own)
      (d, n, checkedShape)
  let S : Structs := checked.flatMap fun (d, n, check) =>
    let check := check.map (·.1)
    ((J.id? d).toList.map fun i => (s!"#solc{i}", check)) ++ [(n, check)]
  let own := checked.filterMap fun (d, _, check) =>
    match check with
    | .ok (p, true) => some (d, p)
    | _ => none
  return (S, own)

/-- The contract's own structs (`readStructs`), as `contract!` members:
`struct S { uint8 a; T[] xs; }`, each member's type as `sol` text. -/
def ownStructMembers (S : Structs) (own : List (Json × String)) : Except Gap (List String) :=
  own.mapM fun (d, p) => do
    let ms ← (← J.arr d "members").mapM fun x => do
      pure s!"{← tyText S (← J.get x "typeName")} {identText (← J.str x "name")};"
    pure s!"struct {identText p} \{ {" ".intercalate ms} }"

/-! ## Expressions and statements -/

/-- Keep each dotted name whole and every separator verbatim. NatSpec has no
solc expression AST, so resolving a declaration must not replace substrings. -/
partial def specTokens (text : String) : List String :=
  if text.isEmpty then [] else
    let word (c : Char) : Bool := c.isAlphanum || c == '_' || c == '$' || c == '.'
    let token := if word (text.toList.head!) then text.takeWhile word
      else String.mk [text.toList.head!]
    token :: specTokens (text.drop token.length)

/-- A builtin's call head is syntax, even when a constant shares its name. -/
def specBuiltinHead (token : String) (rest : List String) : Bool :=
  if ["net", "address", "uint"].contains token then
    rest.find? (fun t => !(t.toList.all Char.isWhitespace)) == some "(" else false

def resolveSpecTokens (format : Nat → String) (values : List (String × Nat))
    (blocked : List String) : List String → List String
  | [] => []
  | "\\" :: keyword :: rest => "\\" :: keyword :: resolveSpecTokens format values blocked rest
  | token :: rest =>
    let replacement := if specBuiltinHead token rest || blocked.contains ((token.splitOn ".").head!) then token else
      match values.filter (·.1 == token) with
      | [(_, value)] => format value
      | _ => token
    replacement :: resolveSpecTokens format values blocked rest

/-- Actual variable references, excluding builtin heads and escaped keywords. -/
def specReadsName (name : String) : List String → Bool
  | [] => false
  | "\\" :: _ :: rest => specReadsName name rest
  | token :: rest =>
    (!specBuiltinHead token rest && (token == name || token.startsWith (name ++ "."))) ||
      specReadsName name rest

/-- Resolve only unshadowed literal names. Clauses with quantifiers or escaped
identifiers stay verbatim: resolving their binders needs the specification
parser, including its comments. Parameters, returns and locals block a head;
ambiguous aliases remain unresolved instead of choosing a declaration. -/
def resolveSpecValues (format : Nat → String) (values : List (String × Nat)) (blocked : List String)
    (text : String) : String :=
  if text.contains '«' || text.contains '»' ||
      (text.splitOn "forall").length > 1 || (text.splitOn "exists").length > 1 then text else
  String.join (resolveSpecTokens format values blocked (specTokens text))

def resolveSpecEnums := resolveSpecValues toString

/-- A fixed uint constant must not acquire a numeral's contextual coercions. -/
def resolveSpecConstants := resolveSpecValues fun n => s!"uint({n})"

/-- The printer's state: the name each declaration is printed as, the state
variables left out, the structs, each function's parameter names (by its
declaration's id), the statements to put before the current one (a pushed
element's storage local), a counter for their names, and whether the
current position may hoist a push. -/
structure PState where
  /-- Validated solc declarations, retained by identity for source metadata.
  This is importer input, not a second representation of typed model terms. -/
  declarations : List Json := []
  /-- Pure selector helpers evaluate a receiver argument in its original
  expression position, including a lazy conditional arm. -/
  selectorHelpers : List (Int × String) := []
  /-- Member resolution is separate from bare identifiers: a getter's alias
  must never replace the storage root of the same declaration identity. -/
  externalNames : List (Int × String) := []
  /-- Unsupported getters are refused at their use, never treated as an
  unspecified self-call which the external world could answer. -/
  getterGaps : List (Int × Gap) := []
  names : List (Int × String) := []
  /-- Original function-version names, for an explicit `Base.f()` call. -/
  staticNames : List (Int × String) := []
  /-- Contract declaration identities in this contract's C3 lineage. -/
  baseContracts : List Int := []
  /-- Each `super.f` of the declaration printed (by solc's static
  `referencedDeclaration`), as the base version it names: the next contract
  after the declaration's own in the most-derived C3 order that implements
  `f` (`superTarget`). -/
  superNames : List (Int × String) := []
  dropped : List (Int × String × Gap) := []
  structs : Structs := []
  funParams : List (Int × List String) := []
  /-- Named-error operands: IR source order, legacy declaration order. -/
  namedErrorSourceOrder : Bool := false
  constants : List (Int × (String × Json)) := []
  constStack : List Int := []
  enumValues : List (Int × Nat) := []
  enumBounds : List (Int × Nat) := []
  specEnums : List (String × Nat) := []
  specBlocked : List String := []
  specConstants : List (String × Nat) := []
  specConstBlocked : List String := []
  /-- Visible source locals, newest first, and their printed names. -/
  specLocals : List (String × String) := []
  /-- State names of the declaration's lexical owner, excluding body locals. -/
  sourceStateNames : List String := []
  sourceModelNames : List String := []
  sourceScope : Source.ScopeScan := default
  scanLoop : List String → List String → String → Source.ScopeScan := fun _ _ _ => default
  /-- The importer parses loop expressions before renaming their variables. -/
  rewriteLoop : List (String × String) → String → Except String String :=
    fun names text => if names.any (fun (a, b) => a != b) then
      .error "loop specification needs renamed locals: not imported" else .ok text
  valueTypes : List (Int × String) := []
  /-- How many discarded values (`a + b;`) were named so far. -/
  discards : Nat := 0
  freeFunctions : List Int := []
  libraries : List Int := []
  pre : Array String := #[]
  fresh : Nat := 0
  pushOk : Bool := false
  deriving Inhabited

/-- Supported scalar UDVT underlyings keep the existing typed primitive and
its exact source width/byte/address metadata; no new runtime value is introduced. -/
def valueTypeSupported (t : String) : Bool :=
  (PrimTy.ofName? t).isSome || (narrowTy? t).isSome || (bytesTy? t).isSome ||
    t == "address payable"

/-- A UDVT expression cannot fall back to a builtin operator when its resolved
annotation is absent. Name fallback is only a rejection check for old fixtures. -/
def valueTypeExpr (declarations : List Json) (j : Json) : Bool :=
  if (J.tyId j).startsWith "t_userDefinedValueType" then true else
  let t := J.tyStr j
  -- Ordinary arithmetic avoids a declaration-table scan on each operand.
  if (PrimTy.ofName? t).isSome || (narrowTy? t).isSome || (bytesTy? t).isSome ||
      ["uint256", "int256", "address payable"].contains t ||
      t.startsWith "int_const " || t.startsWith "rational_const " then false else
  declarations.any fun d =>
    J.kind d == "UserDefinedValueTypeDefinition" &&
      (J.tyStr j == (J.str? d "canonicalName").getD ((J.str? d "name").getD "") ||
       J.tyStr j == (J.str? d "name").getD "")

/-- Validate solc's resolved operator annotation before either admission or
printing. JSON is the external compiler boundary, not a second executable term
language. The result is only a declaration identity and its source operands;
the printer lowers it through the existing intrinsically typed call elaborator.
In particular, matching erased primitive types never establishes nominal equality. -/
def operatorAlias? (declarations : List Json) (j : Json) :
    Except Gap (Option (Int × List Json)) := do
  unless ["UnaryOperation", "BinaryOperation"].contains (J.kind j) do return none
  let unary := J.kind j == "UnaryOperation"
  let args ← if unary then do pure [← J.get j "subExpression"]
    else do pure [← J.get j "leftExpression", ← J.get j "rightExpression"]
  let op ← J.str j "operator"
  unless J.hasOperatorFunction j do
    if op != "delete" && args.any (valueTypeExpr declarations) then
      throw (.unsupported "a UDVT operator lacks its resolved function annotation" (J.line j))
    return none
  let some id := J.operatorFunction? j |
    throw (.unsupported "a malformed resolved operator function annotation" (J.line j))
  unless id > 0 do
    throw (.unsupported "an operator alias must name a positive declaration identity" (J.line j))
  unless (if unary then ["-", "~"] else
      ["&", "|", "^", "+", "/", "%", "*", "-", "==", ">", ">=", "<", "<=", "!="]).contains op do
    throw (.unsupported "an illegal user-defined operator signature" (J.line j))
  if unary && J.opt j "prefix" != some (.bool true) then
    throw (.unsupported "a user-defined unary operator must be a prefix" (J.line j))
  let some target := declarations.find? (J.id? · == some id) |
    throw (.unsupported s!"operator function #{id} is absent from the compiler AST" (J.line j))
  unless J.kind target == "FunctionDefinition" && J.str? target "kind" == some "freeFunction" &&
      J.str? target "stateMutability" == some "pure" &&
      (J.opt target "body").any (J.kind · == "Block") do
    throw (.unsupported "an operator alias must resolve to a defined pure free function" (J.line j))
  let ps ← J.arr (← J.get target "parameters") "parameters"
  unless ps.length == args.length do
    throw (.unsupported "an operator alias has the wrong parameter arity" (J.line j))
  let some first := ps.head? |
    throw (.unsupported "an operator alias has no UDVT parameter" (J.line j))
  let some tn := J.opt first "typeName" |
    throw (.unsupported "an operator parameter lacks its nominal type" (J.line j))
  let some typeId := J.typeRef? tn |
    throw (.unsupported "an operator parameter lacks its type declaration identity" (J.line j))
  let some typeDecl := declarations.find? (J.id? · == some typeId) |
    throw (.unsupported "an operator parameter type declaration is missing" (J.line j))
  unless typeId > 0 && J.kind tn == "UserDefinedTypeName" &&
      J.kind typeDecl == "UserDefinedValueTypeDefinition" do
    throw (.unsupported "an operator parameter is not a user-defined value type" (J.line j))
  let underlying ← tyText [] (← J.get typeDecl "underlyingType")
  unless valueTypeSupported underlying do
    throw (.unsupported s!"unsupported operator underlying type `{underlying}`" (J.line j))
  let nominal := J.tyId first
  unless nominal.startsWith "t_userDefinedValueType" &&
      nominal.endsWith ("_$" ++ toString typeId) &&
      ps.all (fun p => (J.opt p "typeName").any (fun t =>
        J.kind t == "UserDefinedTypeName" && J.typeRef? t == some typeId) &&
        J.tyId p == nominal) && args.all (fun a => J.tyId a == nominal) do
    throw (.unsupported "operator operands do not match the same nominal UDVT (regenerate a modern fixture)" (J.line j))
  let rs ← J.arr (← J.get target "returnParameters") "parameters"
  let [r] := rs |
    throw (.unsupported "an operator alias must return exactly one value" (J.line j))
  let comparison := ["==", "!=", "<", ">", "<=", ">="].contains op
  if comparison then
    unless (J.opt r "typeName").any (fun t => J.kind t == "ElementaryTypeName" &&
        J.str? t "name" == some "bool") && J.tyStr r == "bool" && J.tyStr j == "bool" do
      throw (.unsupported "a comparison alias must return bool" (J.line j))
  else
    unless (J.opt r "typeName").any (fun t =>
        J.kind t == "UserDefinedTypeName" && J.typeRef? t == some typeId) &&
        J.tyId r == nominal && J.tyId j == nominal do
      throw (.unsupported "an operator alias must return its nominal operand type" (J.line j))
  return some (id, args)

/-- The source expression's lowered scalar type, including a discarded UDVT
operator result. The original declarations remain available for alias checking. -/
def modelExprType (st : PState) (j : Json) : String :=
  match st.valueTypes.find? (fun (id, _) =>
      (J.tyId j).startsWith "t_userDefinedValueType" &&
        (J.tyId j).endsWith ("_$" ++ toString id)) with
  | some (_, t) => t
  | none => match lookupBy (J.tyStr j) st.structs with
    | some (.ok t) => t
    | _ => elemTy (J.tyStr j) false

abbrev PM := StateT PState (Except Gap)

def PM.lift {α : Type} (x : Except Gap α) : PM α := StateT.lift x

/-- An exact rational in lowest terms, `den > 0`: the value solc gives an
expression of literals only. -/
structure Q where
  num : Int
  den : Nat := 1
  deriving BEq, Inhabited

namespace Q

/-- `n / d` in lowest terms; `none` for `d = 0`. -/
def make (n d : Int) : Option Q :=
  if d == 0 then none else
  let g : Nat := Nat.gcd n.natAbs d.natAbs
  let s : Int := if d < 0 then -1 else 1
  some { num := s * n / g, den := d.natAbs / g }

def ofInt (n : Int) : Q := { num := n }

def add (a b : Q) : Option Q := make (a.num * b.den + b.num * a.den) (a.den * b.den)
def sub (a b : Q) : Option Q := make (a.num * b.den - b.num * a.den) (a.den * b.den)
def mul (a b : Q) : Option Q := make (a.num * b.num) (a.den * b.den)
def div (a b : Q) : Option Q := make (a.num * b.den) (a.den * b.num)

/-- The integer, if it is one. -/
def int? (a : Q) : Option Int := if a.den == 1 then some a.num else none

/-- `a ** e`, refused past 4096 bits, as solc refuses a too large constant. -/
def pow (a : Q) (e : Q) : Option Q := do
  let e ← e.int?
  if e == 0 then return ofInt 1
  -- solc handles zero before the reciprocal of a negative power.
  if a.num == 0 then return ofInt 0
  if a.den == 1 && a.num == 1 then return ofInt 1
  if a.den == 1 && a.num == -1 then return ofInt (if e.natAbs % 2 == 0 then 1 else -1)
  let bits : Nat := Nat.max (Nat.log2 a.num.natAbs) (Nat.log2 a.den) + 1
  if a.num.natAbs > 1 || a.den > 1 then
    if bits * e.natAbs > 4096 then none
  let p : Q := { num := a.num ^ e.natAbs, den := a.den ^ e.natAbs }
  if e < 0 then make p.den p.num else pure p

end Q

/-- A literal's rational value: `0x…` hex, `_` separators, a decimal point,
`MeN` with `N` possibly negative. -/
def parseRational (s : String) : Option Q :=
  let s := s.replace "_" ""
  if s.startsWith "0x" || s.startsWith "0X" then
    (s.drop 2).foldl (fun acc c => do
      let a ← acc
      let d ← if c.isDigit then some (c.toNat - '0'.toNat)
        else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
        else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
        else none
      pure (Q.ofInt (a.num * 16 + d))) (some (Q.ofInt 0))
  else do
    let (m, e) ← match (s.replace "E" "e").splitOn "e" with
      | [m] => some (m, (0 : Int))
      | [m, e] => do
        let e ← if e.startsWith "-" then (e.drop 1).toNat?.map fun n => -(n : Int) else e.toInt?
        pure (m, e)
      | _ => none
    let (i, f) ← match m.splitOn "." with
      | [i] => some (i, "")
      | [i, f] => some (i, f)
      | _ => none
    let digits := i ++ f
    if digits.isEmpty then none
    let n ← digits.toNat?
    if n == 0 then return Q.ofInt 0
    if e.natAbs > 4096 then none
    let q ← Q.make n (10 ^ f.length)
    if e < 0 then Q.div q (Q.ofInt (10 ^ e.natAbs)) else Q.mul q (Q.ofInt (10 ^ e.natAbs))

/-- Is solc's type of the expression a compile-time constant? -/
def constTy (j : Json) : Bool :=
  let t := J.tyStr j
  t.startsWith "int_const" || t.startsWith "rational_const"

/-- Infinite two's-complement operations before contextual Solidity widths. -/
private def constAnd : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a &&& b)
  | .negSucc a, .ofNat b => .ofNat (b - (a &&& b))
  | .ofNat a, .negSucc b => .ofNat (a - (a &&& b))
  | .negSucc a, .negSucc b => .negSucc (a ||| b)

private def constOr : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a ||| b)
  | .negSucc a, .ofNat b => .negSucc (a - (a &&& b))
  | .ofNat a, .negSucc b => .negSucc (b - (a &&& b))
  | .negSucc a, .negSucc b => .negSucc (a &&& b)

private def constXor : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a ^^^ b)
  | .negSucc a, .ofNat b => .negSucc (a ^^^ b)
  | .ofNat a, .negSucc b => .negSucc (a ^^^ b)
  | .negSucc a, .negSucc b => .ofNat (a ^^^ b)

/-- Solc's exact literal arithmetic, including signed bit operations and
rational remainder with the dividend's sign. -/
partial def constVal (j : Json) : Option Q := do
  match J.kind j with
  | "Literal" =>
    let v ← J.str? j "value"
    let q ← parseRational v
    match J.opt j "subdenomination" with
    | some (.str u) => Q.mul q (Q.ofInt (← unitFactor? u))
    | _ => pure q
  | "TupleExpression" =>
    match J.arr? j "components" with
    | some #[c] => constVal c
    | _ => none
  | "UnaryOperation" =>
    let a ← constVal (← (j.getObjVal? "subExpression").toOption)
    match J.str? j "operator" with
    | some "-" => pure { a with num := - a.num }
    | some "~" => pure (Q.ofInt (- (← a.int?) - 1))
    | _ => none
  | "BinaryOperation" =>
    let a ← constVal (← (j.getObjVal? "leftExpression").toOption)
    let b ← constVal (← (j.getObjVal? "rightExpression").toOption)
    let nat (q : Q) : Option Nat := do
      let n ← q.int?
      if n < 0 then none else pure n.toNat
    match J.str? j "operator" with
    | some "+" => a.add b
    | some "-" => a.sub b
    | some "*" => a.mul b
    | some "/" => a.div b
    | some "%" =>
      if b.num == 0 then none else
        Q.make ((a.num * b.den).tmod (b.num * a.den)) (a.den * b.den)
    | some "**" => a.pow b
    | some "&" => pure (Q.ofInt (constAnd (← a.int?) (← b.int?)))
    | some "|" => pure (Q.ofInt (constOr (← a.int?) (← b.int?)))
    | some "^" => pure (Q.ofInt (constXor (← a.int?) (← b.int?)))
    | some "<<" =>
      let x ← a.int?
      let k ← nat b
      if k ≥ 2 ^ 32 then none
      else if x == 0 then pure (Q.ofInt 0)
      else if k > 4096 then none else pure (Q.ofInt (x * 2 ^ k))
    | some ">>" =>
      let x ← a.int?
      let k ← nat b
      if k ≥ 2 ^ 32 then none
      else if k ≥ Nat.log2 x.natAbs + 1 then pure (Q.ofInt (if x < 0 then -1 else 0))
      else pure (Q.ofInt (x >>> k))
    | _ => none
  | _ => none

/-- Is the node an operand that needs parentheses inside an operator? -/
def compound (j : Json) : Bool :=
  ["BinaryOperation", "Conditional", "Assignment"].contains (J.kind j)

/-- The declarations some assignment, `++`/`--` or `delete` writes by name. -/
def writtenIds (ast : Json) : List Int :=
  (J.nodes ast).filterMap fun n => do
    let target ← match J.kind n with
      | "Assignment" => J.opt n "leftHandSide"
      | "UnaryOperation" =>
        guard ((J.opt n "operator").any fun o => o == .str "++" || o == .str "--" || o == .str "delete")
        J.opt n "subExpression"
      | _ => none
    guard (J.kind target == "Identifier")
    J.ref? target

/-- The default of a value type `t`, as the literal solc would write. -/
def defaultLiteral (t : String) : Json :=
  if t == "bool" then Json.mkObj [("nodeType", "Literal"), ("kind", "bool"), ("value", "false")]
  else Json.mkObj [("nodeType", "Literal"), ("kind", "number"), ("value", "0")]

def unsupported {α : Type} (msg : String) : PM α := throw (.unsupported msg)

/-- A compiler-provided selector has exactly its ABI width; malformed or
trimmed metadata fails closed instead of acquiring a default selector. -/
def declarationSelector (d : Json) (key : String) (bytes : Nat) :
    Except Gap (Fin (2 ^ (8 * bytes))) := do
  let text ← J.str d key
  unless text.length == 2 * bytes do
    throw (.unsupported s!"malformed {key} on declaration #{(J.id? d).getD 0}")
  let value ← text.toList.foldlM (fun n c => do
    let digit ← if c.isDigit then pure (c.toNat - '0'.toNat)
      else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
      else if 'A' ≤ c && c ≤ 'F' then pure (c.toNat - 'A'.toNat + 10)
      else throw (.unsupported s!"non-hexadecimal {key}")
    pure (n * 16 + digit)) 0
  if bound : value < 2 ^ (8 * bytes) then return ⟨value, bound⟩
  else throw (.unsupported s!"out-of-range {key}")

/-- `this.x`/`c.x` denotes a public variable's synthesized getter. A bare
function-valued variable `x` instead denotes its stored value; its selector
must never be mistaken for the getter's declaration selector. -/
def isPublicGetterMember (declaration member : Json) : Bool :=
  J.kind declaration == "VariableDeclaration" &&
    J.opt declaration "stateVariable" == some (.bool true) &&
    J.str? declaration "visibility" == some "public" &&
    J.kind member == "MemberAccess" && (J.tyStr member).startsWith "function " &&
    ((J.tyStr member).splitOn " external").length > 1 &&
    !(J.opt member "expression").any (fun owner => (J.tyStr owner).startsWith "struct ")

/-- Declaration metadata is resolved by solc identity, never a short name.
Only a static declaration or `this.f` can fold a function selector here:
an arbitrary receiver expression must retain its evaluation effects. -/
def declarationMetadata (declarations : List Json) (e : Json) (member : String) :
    Except Gap (Option String) := do
  let find (id : Int) : Option Json := declarations.find? (J.id? · == some id)
  if J.kind e == "FunctionCall" && ["name", "interfaceId"].contains member then
    let some head := J.opt e "expression" | return none
    if J.kind head != "Identifier" || J.ref? head != some (-27) then return none
    let some args := J.arr? e "arguments" | return none
    if args.size != 1 then return none
    let some arg := args[0]? | return none
    let some d := (J.ref? arg).bind find | return none
    if J.kind d != "ContractDefinition" then return none
    if member == "name" then return some (← J.str d "name").quote
    unless J.str? d "contractKind" == some "interface" do
      throw (.unsupported "interfaceId metadata requires an interface declaration")
    -- Inherited declarations are deliberately absent from this list. An
    -- interface's own override is present and contributes its selector once.
    let own := (J.arrD d "nodes").toList.filter fun f =>
      J.kind f == "FunctionDefinition" &&
        J.str? f "kind" == some "function" &&
        [some "public", some "external"].contains (J.str? f "visibility")
    let value ← own.foldlM (fun value f => do
      pure (value ^^^ (← declarationSelector f "functionSelector" 4).val)) 0
    return some s!"bytes4({value})"
  if member != "selector" then return none
  let some d := (J.ref? e).bind find | return none
  match J.kind d with
  | "ErrorDefinition" =>
    return some s!"bytes4({(← declarationSelector d "errorSelector" 4).val})"
  | "EventDefinition" =>
    if (d.getObjValAs? Bool "anonymous").toOption == some true then
      throw (.unsupported "an anonymous event has no selector")
    return some s!"bytes32({(← declarationSelector d "eventSelector" 32).val})"
  | "FunctionDefinition" | "VariableDeclaration" =>
    if J.kind d == "VariableDeclaration" && !isPublicGetterMember d e then return none
    let static := (J.ref? e).isSome &&
      (J.kind e == "Identifier" || J.kind e == "IdentifierPath" ||
        (J.kind e == "MemberAccess" && ((J.opt e "expression").any fun receiver =>
          ((J.ref? receiver).bind find).any (J.kind · == "ContractDefinition") ||
          (J.kind receiver == "Identifier" && J.ref? receiver == some (-28)))))
    if static && (J.str? d "functionSelector").isSome then
      let value ← declarationSelector d "functionSelector" 4
      -- Preserve the existing `fnPure` literal form of `this.f.selector`.
      -- An extra cast introduces a capture into every function-value proof.
      let self := (J.opt e "expression").any fun receiver =>
        J.kind receiver == "Identifier" && J.ref? receiver == some (-28)
      return some (if self then toString value.val else s!"bytes4({value.val})")
    return none
  | _ => return none

/-- `e ? 1 : 0`, solc's encoding of a `bool` key, folded on a literal. -/
def boolKey (j : Json) (e : String) : String :=
  if J.kind j == "Literal" then (if e == "true" then "1" else "0") else s!"({e} ? 1 : 0)"

/-- Bounds of a solc-validated integer or enum type, as compile-time values. -/
def typeBound? (enums : List (Int × Nat)) (j : Json) (member : String) : Option Int := do
  guard (member == "min" || member == "max")
  guard (J.kind j == "FunctionCall")
  let f ← J.opt j "expression"
  guard (J.kind f == "Identifier" && J.opt f "name" == some (.str "type"))
  let [a] ← (J.arr? j "arguments").map (·.toList) | none
  if let some n := (J.ref? a).bind (lookupBy · enums) then
    return if member == "min" then 0 else (n : Int)
  let t ← J.opt a "typeName"
  let name ← J.str? t "name"
  let signed := name.startsWith "int"
  guard (signed || name.startsWith "uint")
  let suffix := name.drop (if signed then 3 else 4)
  let bits ← if suffix.isEmpty then some 256 else suffix.toNat?
  guard (0 < bits && bits ≤ 256 && bits % 8 == 0)
  return if signed then
    if member == "min" then -(2 ^ (bits - 1) : Int) else 2 ^ (bits - 1) - 1
  else if member == "min" then 0 else 2 ^ bits - 1

/-- The declared name of a local, as printed. -/
def nameOf (j : Json) : PM String := do
  let n ← PM.lift (J.str j "name")
  match J.id? j with
  | some i => pure ((lookupBy i (← get).names).getD n)
  | none => pure n

/-- The element type of a `push()`, from solc's type of the call. -/
def pushedTy (j : Json) : PM String := do
  let t := J.tyStr j
  let t := (t.replace " storage ref" "").replace " storage pointer" ""
  let t := if t.startsWith "struct " then
      ((t.drop 7).splitOn ".").getLast!
    else t
  match lookupBy t (← get).structs with
  | some (.ok m) => pure (typeIdentText m)
  | some (.error g) => throw g
  | none => unsupported s!"a member of a pushed `{t}`"

/-- A storage reference's type, from solc's type string, as `sol` text:
`uint256[][] storage ref` is `uint[][]`, `struct C.Token[] storage ref` is
`Token[]`. -/
def storageRefTy (j : Json) : PM String := do
  let t := ((J.tyStr j).replace " storage ref" "").replace " storage pointer" ""
  let base := t.takeWhile (· != '[')
  let dims := t.drop base.length
  let base ← if base.startsWith "struct " then
      let n := ((base.drop 7).splitOn ".").getLast!
      match lookupBy n (← get).structs with
      | some (.ok m) => pure (typeIdentText m)
      | some (.error g) => throw g
      | none => unsupported s!"a reference to `{n}`"
    else pure (sourceType base)
  pure s!"{base}{sourceType dims}"

/-- Is the node `x.push()`? -/
def isPushCall (e : Json) : Bool :=
  J.kind e == "FunctionCall" &&
    ((J.opt e "expression").any fun f => J.kind f == "MemberAccess" &&
      J.str? f "memberName" == some "push" && nativeMember f)

/-- Is the node `x.push().f`? -/
def isPushedMember (e : Json) : Bool :=
  J.kind e == "MemberAccess" && (J.opt e "expression").any isPushCall

/-- A contract-qualified member, never an object or `this` call. -/
def isBaseMember (contracts : List Int) (f : Json) : Bool :=
  J.kind f == "MemberAccess" && (J.opt f "expression").any fun receiver =>
    J.kind receiver == "Identifier" &&
      J.opt receiver "name" != some (.str "this") && J.opt receiver "name" != some (.str "super") &&
      (J.ref? receiver).any contracts.contains

/-- Is the node a member that names an external function, `r.f` in `r.f(a)`? -/
def isExternalMember (f : Json) : Bool :=
  J.kind f == "MemberAccess" && (J.tyStr f).startsWith "function " &&
    ((J.tyStr f).splitOn " external").length > 1 &&
    -- a struct's member of an external function type is a value, not a call
    !(J.opt f "expression").any (fun b => (J.tyStr b).startsWith "struct ")

/-- Is the callee a function value that is not a name: a struct's member, an
element, a call's value, a parenthesised one (`callValueName`)? -/
def isValueCallee (f : Json) : Bool :=
  !(J.kind f == "Identifier") && !isExternalMember f && (J.tyStr f).startsWith "function (" &&
    (["IndexAccess", "FunctionCall", "TupleExpression"].contains (J.kind f) ||
      (J.kind f == "MemberAccess" &&
        (J.opt f "expression").any fun b =>
          (J.tyStr b).startsWith "struct " && !((J.tyStr b).splitOn "[").length > 1))

def isSuperMember (f : Json) : Bool :=
  J.kind f == "MemberAccess" && (J.opt f "expression").any fun receiver =>
    J.kind receiver == "Identifier" && J.opt receiver "name" == some (.str "super")

/-- `x` run where a pushed member may be hoisted, or not. -/
def withPush {α : Type} (ok : Bool) (x : PM α) : PM α := do
  modify fun st => { st with pushOk := ok }
  let a ← x
  modify fun st => { st with pushOk := false }
  pure a

/-- An expression with no effect and no call: its value does not depend on
when it is read among others of its kind (a read may still panic). -/
partial def pureExpr (j : Json) : Bool :=
  let sub (k : String) : Bool := (J.opt j k).all pureExpr
  match J.kind j with
  | "Literal" | "Identifier" | "ElementaryTypeNameExpression" => true
  | "BinaryOperation" => !J.hasOperatorFunction j && sub "leftExpression" && sub "rightExpression"
  | "UnaryOperation" =>
    !J.hasOperatorFunction j && !(J.opt j "operator").any (fun o => o == .str "++" || o == .str "--" || o == .str "delete") &&
      sub "subExpression"
  | "IndexAccess" => sub "baseExpression" && sub "indexExpression"
  | "MemberAccess" => sub "expression"
  | "Conditional" => sub "condition" && sub "trueExpression" && sub "falseExpression"
  | "TupleExpression" =>
    (J.arr? j "components").all (·.all pureExpr)
  | "FunctionCall" =>
    (J.opt j "kind").any (· == .str "typeConversion") &&
      (J.arr? j "arguments").all (·.all pureExpr)
  | _ => false

/-- `(c ? f : g)(as)`, a conditional callee: its condition and the two calls
`f(as)`, `g(as)`.  solc's legacy pipeline evaluates the arguments before the
callee, the condition after them, so the import reads it so only where
neither has an effect (`condCalleeOk`). -/
def condCalleeMsg : String :=
  "a conditional callee whose condition or arguments have an effect: solc evaluates \
    the arguments before the callee"

def condCalleeOk (j : Json) : Bool :=
  ((J.opt j "expression").all pureExpr) &&
    (J.arr? j "arguments").all (·.all pureExpr)

def condCallee? (j : Json) : Option (Json × Json × Json) := do
  guard (J.kind j == "FunctionCall")
  let f ← J.opt j "expression"
  let f ← if J.kind f == "TupleExpression" then
      match J.arr? f "components" with
      | some #[c] => some c
      | _ => none
    else some f
  guard (J.kind f == "Conditional")
  pure (← J.opt f "condition", j.setObjVal! "expression" (← J.opt f "trueExpression"),
    j.setObjVal! "expression" (← J.opt f "falseExpression"))

/-- Canonical decoded bytes supplied by solc, rather than a source token. -/
def validHexBytes (s : String) : Bool :=
  s.length % 2 == 0 && s.toList.all fun c =>
    c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- Ordinary strings may contain non-UTF8 escaped bytes. Unicode literals
must decode as UTF8; two supplied representations must agree. -/
def byteLiteralText (kind : String) (j : Json) : Except Gap String := do
  match J.str? j "hexValue" with
  | some h =>
    unless validHexBytes h do throw (.unsupported "malformed compiler literal bytes")
    let some bytes := hexBytes? h
      | throw (.unsupported "malformed compiler literal bytes")
    let encoded : ByteArray := ⟨(bytes.map UInt8.ofNat).toArray⟩
    if kind == "unicodeString" then
      unless (String.fromUTF8? encoded).isSome do
        throw (.unsupported "a Unicode literal with invalid UTF8 bytes")
    if let some value := J.str? j "value" then
      unless value.toUTF8 == encoded do
        throw (.unsupported "inconsistent compiler literal text and bytes")
    return s!"hex\"{h}\""
  | none =>
    if kind == "hexString" then throw (.unsupported "a hex literal without its bytes")
    return (← J.str j "value").quote

/-- Parentheses carry no literal coercion of their own. Bound their traversal
independently of the declaration/type graph; a missing/omitted component fails. -/
def abiUnparen? : Nat → Json → Option Json
  | 0, _ => none
  | fuel + 1, j =>
    if J.kind j == "TupleExpression" &&
        !((J.opt j "isInlineArray").any (· == .bool true)) then
      match J.arr? j "components" with
      | some #[a] => abiUnparen? fuel a
      | _ => none
    else some j

/-- A numeric hex token's digits, retaining leading zeros but ignoring legal
separators. Unlike hex-string literals, numeric tokens require one exact target
width; a decimal numeral with the same value has no such coercion. -/
def abiHexDigits? (token : String) : Option String := do
  guard (token.startsWith "0x")
  let chars := (token.drop 2).toList
  let isDigit (c : Char) : Bool :=
    c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')
  let mut previous := false
  let mut digits : List Char := []
  for (c, i) in chars.zipIdx do
    if c == '_' then
      guard (previous && (chars[i + 1]?).any isDigit)
      previous := false
    else
      guard (isDigit c)
      digits := c :: digits
      previous := true
  guard previous
  pure (String.mk digits.reverse)

/-- Source lexical evidence admitted for one `bytesN` argument. The successful
value carries its byte-width bound; this is importer input evidence, never a
new untyped program/value in the intrinsic calculus. Address literals, decimal
constants, arithmetic expressions and shorter/longer hex tokens do not qualify. -/
def abiHexLiteral? (n : Nat) (j : Json) : Option (Fin (2 ^ (8 * n))) := do
  guard (0 < n && n ≤ 32)
  let j ← abiUnparen? 64 j
  guard (J.kind j == "Literal" && J.str? j "kind" == some "number" && constTy j)
  let token ← J.str? j "value"
  let digits ← abiHexDigits? token
  guard (digits.length == 2 * n)
  let bytes ← hexBytes? digits
  let value := bytes.foldl (fun v b => v * 256 + b) 0
  if h : value < 2 ^ (8 * n) then some ⟨value, h⟩ else none

/-- Keep the direct tuple shape used by solc. Parentheses around a
multi-argument tuple create one tuple-valued component, not extra grouping:
flattening it would admit source calls that solc rejects. -/
def abiCallComponents? (j : Json) : Option (List Json) := do
  if J.kind j != "TupleExpression" ||
      (J.opt j "isInlineArray").any (· == .bool true) then return [j]
  let cs ← J.arr? j "components"
  guard (cs.all fun c => !(J.kind c).isEmpty)
  pure cs.toList

/-- Retained declaration identity determines contextual argument widths. A
function declaration and an external function-typed variable use the same
parameter-list shape. Other parameter types remain `none`, so this reader
cannot turn a numeric argument into a reference, enum or arbitrary byte kind. -/
def abiCallBytesParams? (declarations : List Json) (target : Json) :
    Option (List (Option Nat)) := do
  let target ← abiUnparen? 64 target
  let id ← J.ref? target
  let d ← declarations.find? (J.id? · == some id)
  let params ← match J.kind d with
    | "FunctionDefinition" => do
      guard (["public", "external"].contains ((J.str? d "visibility").getD ""))
      J.opt d "parameters"
    | "VariableDeclaration" => do
      let ty ← J.opt d "typeName"
      guard (J.kind ty == "FunctionTypeName" && J.str? ty "visibility" == some "external")
      J.opt ty "parameterTypes"
    | _ => none
  let params ← J.arr? params "parameters"
  pure (params.toList.map fun p => do
    let ty ← J.opt p "typeName"
    guard (J.kind ty == "ElementaryTypeName")
    let name ← J.str? ty "name"
    bytesTy? name)

mutual

partial def expr (j : Json) : PM String := do
  if let some (id, args) ← PM.lift (operatorAlias? (← get).declarations j) then
    let some name := lookupBy id (← get).names |
      unsupported s!"operator function #{id} is not in the resolved call graph"
    let args ← args.mapM expr
    return s!"{identText name}({", ".intercalate args})"
  if constTy j && ["Literal", "UnaryOperation", "BinaryOperation", "TupleExpression"].contains
      (J.kind j) then
    let some q := constVal j
      | unsupported s!"the constant expression of type `{J.tyStr j}`"
    let some n := q.int?
      | unsupported s!"the constant `{q.num}/{q.den}`, which is not an integer"
    return toString n
  match J.kind j with
  | "Identifier" =>
    let n ← PM.lift (J.str j "name")
    match J.ref? j with
    | some r =>
      if let some (t, value) := lookupBy r (← get).constants then
        if (← get).constStack.contains r then unsupported "a cyclic constant definition"
        let stack := (← get).constStack
        modify fun st => { st with constStack := r :: stack }
        let value ← expr value
        modify fun st => { st with constStack := stack }
        return sourceCast t value
      if let some (v, g) := lookupBy r (← get).dropped then
        throw (match g with
          | .excluded m _ => .excluded s!"it reads the state variable `{v}`: {m}"
          | .unsupported m _ => .unsupported s!"it reads the state variable `{v}`: {m}")
      let name := (lookupBy r (← get).names).getD n
      pure (if r < 0 then name else identText name)
    | none => pure (identText n)
  | "Literal" =>
    match (← PM.lift (J.str j "kind")) with
    | "bool" =>
      let v ← PM.lift (J.str j "value")
      unless v == "true" || v == "false" do unsupported "a malformed boolean literal"
      pure v
    | "number" =>
      let v ← PM.lift (J.str j "value")
      match (parseRational v).bind Q.int? with
      | some n =>
        -- Its source type matters to packed ABI encoding and array inference.
        if J.tyStr j == "address" then
          unless v.startsWith "0x" && v.length == 42 &&
              validHexBytes (v.drop 2) && 0 ≤ n && n < 2 ^ 160 do
            unsupported "a malformed compiler address literal"
          pure s!"address({n})"
        else pure (toString n)
      | none => unsupported s!"the number literal `{v}`"
    | "string" => PM.lift (byteLiteralText "string" j)
    | "unicodeString" => PM.lift (byteLiteralText "unicodeString" j)
    | "hexString" => PM.lift (byteLiteralText "hexString" j)
    | k => unsupported s!"a {k} literal"
  | "TupleExpression" =>
    let cs ← PM.lift (J.arr j "components")
    if (J.opt j "isInlineArray").any (· == .bool true) then
      -- Solc has already found a common element type. Preserve scalar
      -- context before the model independently infers the array's shape.
      let t := ((J.tyStr j).splitOn "[").head!
      let scalar := ((J.tyStr j).splitOn "[").length == 2 &&
        ((narrowTy? t).isSome || (bytesTy? t).isSome ||
          t == "bool" || t == "uint" || t == "int" || t == "address")
      let es ← cs.mapM fun c => do
        let e ← expr c
        pure (if !scalar then e else if t == "address" then s!"address({e})" else sourceCast t e)
      pure s!"[{", ".intercalate es}]"
    else match cs with
    | [c] => pure s!"({← expr c})"
    | _ => unsupported "a tuple"
  | "UnaryOperation" =>
    let a ← J.get j "subExpression" |> PM.lift
    let s ← operand a false
    let pre := (J.opt j "prefix").any (· == .bool true)
    match (← PM.lift (J.str j "operator")) with
    | "!" => pure s!"!{s}"
    | "-" => pure s!"-{s}"
    | "~" => pure s!"~{s}"
    | "++" => pure (if pre then s!"++{s}" else s!"{s}++")
    | "--" => pure (if pre then s!"−−{s}" else s!"{s}−−")
    | "delete" => pure s!"delete {s}"
    | o => unsupported s!"the operator `{o}`"
  | "BinaryOperation" =>
    let op ← PM.lift (J.str j "operator")
    let l ← operand (← PM.lift (J.get j "leftExpression")) (op == "**")
    let r ← operand (← PM.lift (J.get j "rightExpression")) (op == "**")
    pure s!"{l} {op} {r}"
  | "Conditional" =>
    let c ← operand (← PM.lift (J.get j "condition")) false
    let a ← operand (← PM.lift (J.get j "trueExpression")) false
    let b ← operand (← PM.lift (J.get j "falseExpression")) false
    let value := s!"{c} ? {a} : {b}"
    let t := elemTy (J.tyStr j) false
    -- Literal arms have no declared width in `sol` syntax. Preserve solc's
    -- result width before a surrounding operation, not only at its target.
    let literals := constTy (← PM.lift (J.get j "trueExpression")) &&
      constTy (← PM.lift (J.get j "falseExpression"))
    pure (if literals && (narrowTy? t).isSome then sourceCast t value else value)
  | "Assignment" =>
    -- inside an expression an assignment is parenthesized: `(x = e)`; its
    -- statement prints it bare (`assignText`)
    pure s!"({← assignText j})"
  | "IndexAccess" =>
    let b ← expr (← PM.lift (J.get j "baseExpression"))
    let some ij := J.opt j "indexExpression" | unsupported "an index access with no index"
    let i ← expr ij
    pure s!"{b}[{if J.tyStr ij == "bool" then boolKey ij i else i}]"
  | "MemberAccess" =>
    let e ← PM.lift (J.get j "expression")
    let m ← PM.lift (J.str j "memberName")
    if let some value ← PM.lift (declarationMetadata (← get).declarations e m) then
      return value
    -- Keep stored projections typed for ABI/concat consumers. Known function
    -- declarations keep their selector helper, which evaluates the receiver.
    let declarations := (← get).declarations
    let knownFunction := ((J.ref? e).bind fun id =>
      declarations.find? (J.id? · == some id)).any fun declaration =>
        J.kind declaration == "FunctionDefinition" || isPublicGetterMember declaration e
    if !knownFunction then
      if let some t := storedFunctionMemberType? j then
        let value ← expr e
        return sourceCast t s!"{value}.{m}"
    -- `fnPure` folds a known function's selector. A pure helper consumes
    -- the receiver first, in this expression's original (possibly lazy)
    -- position; hoisting into `pre` would eagerly evaluate a skipped arm.
    if m == "selector" && J.kind e == "MemberAccess" then
      let declarations := (← get).declarations
      if let some d := (J.ref? e).bind fun id =>
          declarations.find? (J.id? · == some id) then
        if (J.kind d == "FunctionDefinition" || isPublicGetterMember d e) &&
            (J.str? d "functionSelector").isSome then
          let receiver ← PM.lift (J.get e "expression")
          let value ← expr receiver
          let _ ← PM.lift (declarationSelector d "functionSelector" 4)
          let some name := (J.id? d).bind (lookupBy · (← get).selectorHelpers)
            | unsupported "a dynamic function selector without its receiver helper"
          return s!"{identText name}(address({value}))"
    if isExternalMember j then
      if let some id := J.ref? j then
        if let some gap := lookupBy id (← get).getterGaps then throw gap
        if let some name := lookupBy id (← get).externalNames then
          let receiver ← expr e
          return s!"({receiver}).{identText name}"
    if let some bound := typeBound? (← get).enumBounds e m then
      let t := if (J.tyStr j).startsWith "enum " then "uint" else elemTy (J.tyStr j) false
      return s!"{t}({bound})"
    if let some r := J.ref? j then
      if (← get).freeFunctions.contains r then
        if let some name := lookupBy r (← get).names then return identText name
      if let some value := lookupBy r (← get).enumValues then return toString value
      if let some (t, value) := lookupBy r (← get).constants then
        if (← get).constStack.contains r then unsupported "a cyclic constant definition"
        let stack := (← get).constStack
        modify fun st => { st with constStack := r :: stack }
        let value ← expr value
        modify fun st => { st with constStack := stack }
        return sourceCast t value
    if isPushCall e then
      -- `x.push().f`: the element read through a storage local first
      unless (← get).pushOk do
        unsupported "a member of a pushed element (`x.push().f`) other than an assignment's \
          left-hand side of a constant or a declaration's whole initial value: hoisting the \
          push would change solc's order of evaluation"
      modify fun st => { st with pushOk := false }
      let T ← pushedTy e
      let call ← expr e
      let st ← get
      let x := s!"pushRef{st.fresh + 1}"
      set { st with fresh := st.fresh + 1, pre := st.pre.push s!"{T} storage {x} = {call}" }
      pure s!"{x}.{identText m}"
    else if (J.ref? j).any (· ≥ 0) then
      let receiver ← expr e
      let magicName := J.kind e == "Identifier" &&
        ["msg", "block", "tx", "this"].contains ((J.str? e "name").getD "")
      let receiver := if compound e || magicName then s!"({receiver})" else receiver
      pure s!"{receiver}.{identText m}"
    else pure s!"{← expr e}.{m}"
  | "FunctionCall" => call j
  | "NewExpression" =>
    pure s!"new {← PM.lift (tyText (← get).structs (← PM.lift (J.get j "typeName")))}"
  -- a calldata slice, a view of the caller's data: `sol{}` reads it as one
  -- (`RawStmt.sliceViews`; docs/semantic-gaps.md, "Bytes and strings")
  | "IndexRangeAccess" =>
    let b ← operand (← PM.lift (J.get j "baseExpression")) false
    let i ← match J.opt j "startExpression" with
      | some e => expr e
      | none => pure ""
    let k ← match J.opt j "endExpression" with
      | some e => expr e
      | none => pure ""
    if i.isEmpty && k.isEmpty then pure s!"{b}[0:]"
    else pure s!"{b}[{i}:{k}]"
  | k => unsupported s!"the expression `{k}`"

/-- An assignment's text, `l op r`; a nested assignment on the right
parenthesized by `expr`. -/
partial def assignText (j : Json) : PM String := do
  let op ← PM.lift (J.str j "operator")
  pure s!"{← expr (← PM.lift (J.get j "leftHandSide"))} {op} {← expr (← PM.lift (J.get j "rightHandSide"))}"

/-- An operand, parenthesised when it is itself an operator (`pow`: also a
unary one, which `**` would otherwise take inside). -/
partial def operand (j : Json) (pow : Bool) : PM String := do
  let s ← expr j
  pure (if compound j || (pow && J.kind j == "UnaryOperation") then s!"({s})" else s)

partial def call (j : Json) : PM String := do
  let f ← PM.lift (J.get j "expression")
  let args ← PM.lift (J.arr j "arguments")
  if let some (c, a, b) := condCallee? j then
    unless condCalleeOk j do unsupported condCalleeMsg
    return s!"({← operand c false} ? {← call a} : {← call b})"
  if J.kind f == "MemberAccess" then
    let member := (J.str? f "memberName").getD ""
    -- `string.concat(…)`, `bytes.concat(…)`: a builtin of the type's name
    if member == "concat" then
      if let some owner := J.opt f "expression" then
        if J.kind owner == "ElementaryTypeNameExpression" then
          let n ← PM.lift (J.str (← PM.lift (J.get owner "typeName")) "name")
          return s!"{n}.concat({", ".intercalate (← args.mapM expr)})"
    -- Consume lexical hex evidence before `expr` folds a numeric constant
    -- to decimal text. Only the call's declared fixed-byte argument supplies
    -- context; ordinary abi.encode(0xabcd) keeps its numeric ABI kind.
    if member == "encodeCall" && (J.opt f "expression").any (builtinNamed · "abi") then
      match args with
      | [target, tuple] =>
        -- Getter identities refer to VariableDeclaration, not FunctionDefinition.
        -- They still consume the direct tuple shape. Native encodeCall validates
        -- its exact signature; lack of a fixed-byte context never invents one.
        let components? := abiCallComponents? tuple
        let knownWidths := abiCallBytesParams? (← get).declarations target
        let widths := knownWidths.getD (List.replicate (components?.getD []).length none)
        let some components := components? |
          unsupported "abi.encodeCall: incomplete argument tuple"
        unless components.length == widths.length do
          unsupported "abi.encodeCall: argument tuple disagrees with its declaration"
        let values ← (widths.zip components).mapM fun (width, a) => do
          if let some n := width then
            if let some value := abiHexLiteral? n a then
              return sourceCast s!"bytes{n}" (toString value.val)
          let value ← expr a
          -- Metadata such as `this.f.selector` may deliberately print as
          -- a numeral. Preserve its established byte kind, as at the
          -- other ABI encoders, without inventing a kind for plain numbers.
          let ty := J.tyStr a
          return if (bytesTy? ty).isSome && !(value.startsWith (ty ++ "(")) then
            sourceCast ty value else value
        return s!"abi.encodeCall({← expr target}, ({", ".intercalate values}))"
      | _ => unsupported "abi.encodeCall with other than two arguments"
    -- `abi.decode(b, (T, U))`: the types written as names
    if member == "decode" && (J.opt f "expression").any (fun o =>
        builtinNamed o "abi") then
      match args with
      | [b, ts] =>
        let tyName (t : Json) : PM String := do PM.lift (abiTyText (← get).structs t)
        let names ← match J.kind ts, J.arr? ts "components" with
          | "TupleExpression", some cs => cs.toList.mapM tyName
          | _, _ => do pure [← tyName ts]
        return s!"abi.decode({← expr b}, ({", ".intercalate names}))"
      | _ => unsupported "abi.decode with other than two arguments"
    if member == "wrap" || member == "unwrap" then
      if let some owner := J.opt f "expression" then
        if let some t := (J.ref? owner).bind (lookupBy · (← get).valueTypes) then
          match args with
          | [a] => return sourceCast t (← expr a)
          | _ => unsupported "wrap or unwrap with multiple arguments"
  match (← PM.lift (J.str j "kind")) with
  | "typeConversion" =>
    match args with
    | [a] =>
      let to := J.tyStr f
      if to.startsWith "type(address" || to.startsWith "type(contract " then
        pure s!"address({← expr a})"
      else if to.startsWith "type(enum " then
        -- `E(x)`: the enum is a `contract!` member (`enumMembers`), and the
        -- elaborator asserts that `x` names one of its members
        let e := ((to.drop 10).dropRight 1).splitOn "." |>.getLast!
        pure s!"{identText e}({← expr a})"
      else
        let n ← match J.kind f with
          | "ElementaryTypeNameExpression" =>
            PM.lift (J.str (← PM.lift (J.get f "typeName")) "name")
          | _ => unsupported s!"the conversion to `{to}`"
        pure s!"{elemTy n false}({← expr a})"
    | _ => unsupported "a conversion of several arguments"
  | "functionCall" =>
    let superNames := (← get).superNames
    let superName := if isSuperMember f then (J.ref? f).bind (lookupBy · superNames) else none
    if isSuperMember f && superName.isNone then
      unsupported "a super call with no implementation after its contract in the C3 order"
    let staticBase := isBaseMember (← get).baseContracts f
    let attached := !staticBase && (J.ref? f).any ((← get).freeFunctions.contains) &&
      J.kind f == "MemberAccess" &&
      !((J.opt f "expression").bind J.ref?).any ((← get).libraries.contains)
    let names : List String := (J.arr? j "names").map
      (·.toList.filterMap (·.getStr?.toOption)) |>.getD []
    let args ← if names.isEmpty then pure args else
      -- named arguments, put in the callee's parameter order
      let some ps := (J.ref? f).bind (lookupBy · (← get).funParams)
        | unsupported "named arguments to a callee whose parameters the import does not know"
      let ps := if attached then ps.tail else ps
      ps.mapM fun p => match names.idxOf? p with
        | some i => match args[i]? with
          | some a => pure a
          | none => unsupported s!"the named argument `{p}`"
        | none => unsupported s!"the named arguments leave out `{p}`"
    let args ← if attached then do
        pure ((← PM.lift (J.get f "expression")) :: args)
      else pure args
    -- a call through a function value that is not a name (a member, an
    -- element, a call's value): the callee printed as an operand, which the
    -- elaborator captures first (`callValueName`)
    let valueCallee := !isSuperMember f && !staticBase && !attached && isValueCallee f
    let as ← args.mapM expr
    -- `abi.encodePacked` packs an enum at one byte: a member, printed as its
    -- position, is printed as the enum's conversion `E(n)` so that it keeps
    -- its type (`markOf?`)
    let packed := J.str? f "memberName" == some "encodePacked"
    let abiEncoder := J.kind f == "MemberAccess" &&
      ["encode", "encodePacked", "encodeWithSelector", "encodeWithSignature", "encodeCall"].contains
        ((J.str? f "memberName").getD "") &&
      (J.opt f "expression").any (builtinNamed · "abi")
    let as := if abiEncoder then
        (args.zip as).map fun (a, t) =>
          -- Constant metadata can print as a numeral. Preserve the source
          -- byte kind at ABI sites, including alignment in ordinary encode.
          if (bytesTy? (J.tyStr a)).isSome && !(t.startsWith (J.tyStr a ++ "(")) then
            sourceCast (J.tyStr a) t
          else if packed && (J.tyStr a).startsWith "enum " && J.kind a == "MemberAccess" then
            s!"{identText ((((J.tyStr a).drop 5).splitOn ".").getLast!)}({t})"
          else t
      else as
    let name ← if let some n := superName then pure (identText n)
      else if staticBase then
        match (J.ref? f).bind (lookupBy · (← get).staticNames) with
        | some name => pure (identText name)
        | none => unsupported "a base-qualified call without an imported function declaration"
      else if isExternalMember f then
        -- `I(0).f`: the receiver an address, `address(0).f` (`0.f` does not parse)
        let r ← expr (← PM.lift (J.get f "expression"))
        let r := if r.front.isDigit then s!"address({r})" else r
        if let some id := J.ref? f then
          if let some gap := lookupBy id (← get).getterGaps then throw gap
        let original ← PM.lift (J.str f "memberName")
        let name := ((J.ref? f).bind (lookupBy · (← get).externalNames)).getD original
        pure s!"({r}).{identText name}"
      else if valueCallee && J.kind f == "FunctionCall" then pure s!"({← expr f})"
      else expr f
    pure s!"{name}({", ".intercalate as})"
  | "structConstructorCall" =>
    -- `S(a, b)` or `S({b: y, a: x})`: the struct by its declaration, as the
    -- import names it (the table's, or the contract's own)
    let some id := J.ref? f | unsupported "a struct constructor without its declaration"
    let name ← match lookupBy s!"#solc{id}" (← get).structs with
      | some (.ok m) => pure (typeIdentText m)
      | some (.error g) => unsupported g.msg
      | none => unsupported s!"a struct constructor of the type declaration #{id}"
    let as ← args.mapM expr
    let names : List String := (J.arr? j "names").map
      (·.toList.filterMap (·.getStr?.toOption)) |>.getD []
    if names.isEmpty then pure s!"{name}({", ".intercalate as})"
    else
      pure s!"{name}(\{{", ".intercalate ((names.zip as).map fun (n, a) => s!"{identText n}: {a}")}})"
  | k => unsupported s!"a call of kind `{k}`"

end

/-- The node inside its redundant parentheses: `((a, b))` is `(a, b)`. -/
partial def unparen (j : Json) : Json :=
  match J.kind j, (J.arr? j "components").map (·.toList) with
  | "TupleExpression", some [c] =>
    if (J.opt j "isInlineArray").any (· == .bool true) || c == .null then j else unparen c
  | _, _ => j

/-- Is the node a tuple of several components, `(a, b)`, and not an inline
array (`SolJSONParser.isTuple`)? -/
def isTuple (j : Json) : Bool :=
  J.kind j == "TupleExpression" && !(J.opt j "isInlineArray").any (· == .bool true) &&
    (J.arr? j "components").any (·.size > 1)

/-- Is the node a call by name, `f(a)`: of a function of the contract, where
a tuple is its value (`SolJSONParser.requireTupleValue`)? -/
def isNamedCall (j : Json) (helpers : List Int := []) (contracts : List Int := []) : Bool :=
  J.kind j == "FunctionCall" && (J.opt j "expression").any (fun f =>
    J.kind f == "Identifier" ||
    isBaseMember contracts f || isSuperMember f ||
    (J.kind f == "MemberAccess" && (J.ref? f).any helpers.contains))

/-- The receiver and the amount of `(bool ok, ) = R.call{value: V}("")`, the
one value call solkey reads, matched as `SolJSONParser.isValueCall` matches
it: two declarations, a `bool` and an empty one; the options exactly
`value`; the member `call`; one argument, the empty string. -/
def valueCall? (j : Json) : Option (Json × Json × Json) := do
  guard (J.kind j == "VariableDeclarationStatement")
  let [d, Json.null] := (J.arr? j "declarations").map (·.toList) |>.getD []
    | none
  let call ← J.opt j "initialValue"
  let opts ← J.opt call "expression"
  let m ← J.opt opts "expression"
  guard (d != .null && J.tyStr d == "bool")
  guard (J.kind call == "FunctionCall" && J.kind opts == "FunctionCallOptions")
  let [Json.str "value"] := (J.arr? opts "names").map (·.toList) |>.getD []
    | none
  guard (J.kind m == "MemberAccess" && nativeMember m && J.str? m "memberName" == some "call")
  let [a] := (J.arr? call "arguments").map (·.toList) |>.getD []
    | none
  guard (J.kind a == "Literal" && J.str? a "kind" == some "string" &&
    J.str? a "value" == some "")
  let [v] ← (J.arr? opts "options").map Array.toList | none
  pure (d, ← J.opt m "expression", v)

/-- A tuple's components, one left out printed empty: `(a, , b)`. -/
def tuple (j : Json) : PM String := do
  let cs ← (← PM.lift (J.arr j "components")).mapM fun c =>
    if c == .null then pure "" else expr c
  pure s!"({", ".intercalate cs})"

/-- What a tuple is assigned from: a tuple, or a call of a function of the
contract (`SolJSONParser.requireTupleValue`). -/
def tupleValue (v : Json) : PM String := do
  if isTuple v then tuple v
  else if isNamedCall v (← get).freeFunctions (← get).baseContracts then expr v
  -- `abi.decode(d, (T, U))`: the elaborator decodes each component
  else if J.kind v == "FunctionCall" && (J.opt v "expression").any (fun f =>
      J.kind f == "MemberAccess" && J.str? f "memberName" == some "decode" &&
        (J.opt f "expression").any (builtinNamed · "abi"))
  then expr v
  else unsupported "a tuple assigned from neither a tuple, nor a call of a function of this \
    contract, nor `(bool ok, ) = a.call{value: v}(\"\")`"

/-- A local's declaration, `T [storage|memory] x`. -/
def declText (d : Json) : PM String := do
  let T ← PM.lift (tyText (← get).structs (← PM.lift (J.get d "typeName")))
  let loc ← match J.opt d "storageLocation" with
    | some (.str "storage") => pure " storage"
    | some (.str "memory") => pure " memory"
    -- Preserve the location: slice locals retain views, memory locals copy.
    | some (.str "calldata") => pure " calldata"
    | _ => pure ""
  let name ← nameOf d
  if let some source := J.str? d "name" then
    unless source.isEmpty do
      modify fun st => { st with specLocals := (source, name) :: st.specLocals }
  pure s!"{T}{loc} {identText name}"

/-- A source block, loop initializer or catch has a lexical local scope. -/
def withSpecScope {α : Type} (action : PM α) : PM α := do
  let names := (← get).specLocals
  let result ← action
  modify fun st => { st with specLocals := names }
  pure result

private def yulArgs? (name : String) (j : Json) : Option (List Json) := do
  guard (J.kind j == "YulFunctionCall")
  let f ← J.opt j "functionName"
  guard (J.kind f == "YulIdentifier" && J.str? f "name" == some name)
  (J.arr? j "arguments").map Array.toList

/-- Only the canonical byte-buffer rethrow; no other assembly is erased. -/
def memoryRethrow? (declarations : List Json) (j : Json) : Option Json := do
  let ast ← J.opt j "AST"
  guard (J.kind ast == "YulBlock")
  let [stmt] ← (J.arr? ast "statements").map Array.toList | none
  guard (J.kind stmt == "YulExpressionStatement")
  let [ptr, len] ← yulArgs? "revert" (← J.opt stmt "expression") | none
  let [data, offset] ← yulArgs? "add" ptr | none
  let [same] ← yulArgs? "mload" len | none
  guard (J.kind data == "YulIdentifier" && J.kind same == "YulIdentifier")
  let name ← J.str? data "name"
  guard (J.str? same "name" == some name)
  guard (J.kind offset == "YulLiteral" && J.str? offset "kind" == some "number")
  guard (((J.str? offset "value").bind parseRational).bind Q.int? == some 32)
  let [left, right] ← (J.arr? j "externalReferences").map Array.toList | none
  let declaration (r : Json) : Option Int := do
    guard (J.opt r "isOffset" == some (.bool false) && J.opt r "isSlot" == some (.bool false))
    guard ((r.getObjValAs? Nat "valueSize").toOption == some 1)
    (r.getObjValAs? Int "declaration").toOption
  guard ((declaration left).isSome && declaration left == declaration right)
  let id ← declaration left
  let decl ← declarations.find? (J.id? · == some id)
  guard (J.kind decl == "VariableDeclaration" && J.tyStr decl == "bytes" &&
    J.str? decl "storageLocation" == some "memory" && J.str? decl "name" == some name)
  pure decl

mutual

/-- A statement as `sol` text, after the storage locals it reads pushed
elements through. -/
partial def stmt (j : Json) : PM (List String) := do
  let line := J.line j
  let s ← tryCatch (stmt1 j) fun g => throw (match g with
    | .excluded m 0 => .excluded m line
    | .unsupported m 0 => .unsupported m line
    | g => g)
  let st ← get
  set { st with pre := #[] }
  pure (st.pre.toList ++ s)

partial def block (j : Json) : PM String := withSpecScope do
  let ss ← if J.kind j == "Block" || J.kind j == "UncheckedBlock" then
      do (← PM.lift (J.arr j "statements")).flatMapM stmt
    else stmt j
  pure ("{ " ++ String.join (ss.map (· ++ "; ")) ++ "}")

partial def stmt1 (j : Json) : PM (List String) := do
  match J.kind j with
  | "PlaceholderStatement" => pure ["_"]
  | "ExpressionStatement" =>
    let e ← PM.lift (J.get j "expression")
    -- Reading a resolved scalar variable as an expression statement has no
    -- effects or failing bounds. The source admission walker still checks its
    -- declaration; do not drop unresolved names, calls or indexed reads.
    let scalar := (PrimTy.ofName? (J.tyStr e)).isSome ||
      (narrowTy? (J.tyStr e)).isSome || (bytesTy? (J.tyStr e)).isSome ||
      ["address", "address payable"].contains (J.tyStr e)
    let declarations := (← get).declarations
    if J.kind e == "Identifier" && scalar then
      if ((J.ref? e).bind fun id => declarations.find? (J.id? · == some id)).any
          (J.kind · == "VariableDeclaration") then return []
    if J.kind e == "Assignment" && (J.opt e "operator").any (· == .str "=") &&
        (J.opt e "leftHandSide").any (isTuple ∘ unparen) then
      -- `(a, , b) = v`, and `((a, b)) = v` as it
      return [s!"{← tuple (unparen (← PM.lift (J.get e "leftHandSide")))} = \
        {← tupleValue (unparen (← PM.lift (J.get e "rightHandSide")))}"]
    -- `x.push().f = c`: solc pushes, then stores the constant
    let ok := J.kind e == "Assignment" && (J.opt e "leftHandSide").any isPushedMember &&
      (J.opt e "rightHandSide").any fun r =>
        constTy r || (J.kind r == "Literal" && J.tyStr r == "bool")
    -- `x.pop;`, `x.push;`: the member named, not called: the receiver is
    -- evaluated (its effects, its bounds checks) into a fresh storage alias and
    -- dropped (solkey's `storagePopReference_unfold_leftFstReceiver`,
    -- `storagePopReferenceDiscard`)
    if J.kind e == "MemberAccess" &&
        nativeMember e &&
        (J.opt e "memberName").any (fun m => m == .str "pop" || m == .str "push") &&
        (J.tyStr e).startsWith "function" then
      let r ← PM.lift (J.get e "expression")
      let k := (← get).discards + 1
      modify fun st => { st with discards := k }
      return [s!"{← storageRefTy r} storage discarded{k} = {← expr r}"]
    -- `(c ? f : g)();` of no value: `if (c) { f(); } else { g(); }`
    if let some (c, a, b) := condCallee? e then
      unless condCalleeOk e do unsupported condCalleeMsg
      if J.tyStr e == "tuple()" then
        return [s!"if ({← expr c}) {"{"} {← call a}; {"}"} else {"{"} {← call b}; {"}"}"]
    -- `r.f(a);`, an external call outside a `try`: a `try` whose every
    -- failure reverts the caller, as the call's revert does (and a call to an
    -- address with no code reverts in both)
    if J.kind e == "FunctionCall" && J.str? e "kind" == some "functionCall" &&
        (J.opt e "expression").any isExternalMember then
      return [s!"try {← expr e} \{ } catch \{ revert(); }"]
    -- an operator's value discarded, `a + b;`: held in a fresh local, its
    -- effects and its revert kept (solkey's `discardAddExpression`, …)
    if ["BinaryOperation", "Conditional"].contains (J.kind e) then
      let t := modelExprType (← get) e
      let k := (← get).discards + 1
      modify fun st => { st with discards := k }
      return [s!"{t} discarded{k} = {← expr e}"]
    pure [← withPush ok (if J.kind e == "Assignment" then assignText e else expr e)]
  | "VariableDeclarationStatement" =>
    if let some (d, r, v) := valueCall? j then
      -- `(bool ok, ) = R.call{value: V}("")`: a send with all the gas, which may call back
      -- under either `transferSemantics` (`Stmt.send`'s `full`)
      return [s!"({← declText d}, ) = {← operand r false}.call\{value: {← expr v}}(\"\")"]
    let ds ← PM.lift (J.arr j "declarations")
    if ds.length ≥ 2 then
      -- `(uint a, , bool b) = v`
      -- a component's location left out: `sol{}`'s tuple declaration writes
      -- none, and the elaborator reads a reference component as memory
      let ts ← ds.mapM fun d => if d == .null then pure "" else do
        let t ← declText d
        pure (t.replace " memory " " ")
      let some v := J.opt j "initialValue" | unsupported "a declaration of several variables, \
        with no value"
      return [s!"({", ".intercalate ts}) = {← tupleValue v}"]
    let [d] := ds | unsupported "a declaration of no variable"
    let dt ← declText d
    match J.opt j "initialValue" with
    | some v => pure [s!"{dt} = {← withPush (isPushedMember v) (expr v)}"]
    | none => pure [dt]
  | "Return" =>
    match J.opt j "expression" with
    | none => pure ["return"]
    | some e => pure [s!"return {← if isTuple e then tuple e else expr e}"]
  | "Block" => pure [← block j]
  | "UncheckedBlock" => pure [s!"unchecked {← block j}"]
  | "IfStatement" =>
    let c ← expr (← PM.lift (J.get j "condition"))
    let t ← block (← PM.lift (J.get j "trueBody"))
    match J.opt j "falseBody" with
    | some e => pure [s!"if ({c}) {t} else {← block e}"]
    | none => pure [s!"if ({c}) {t}"]
  | "TryStatement" => withSpecScope do
    let outerLocals := (← get).specLocals
    let c ← expr (← PM.lift (J.get j "externalCall"))
    match (← PM.lift (J.arr j "clauses")) with
    | ok :: catches =>
      let params (cl : Json) : PM (List String) := do
        match J.opt cl "parameters" with
        | some ps => (← PM.lift (J.arr ps "parameters")).mapM fun p => do
            let t ← declText p
            pure (if J.str? p "name" == some "" then t.trimRight else t)
        | none => pure []
      -- an unnamed return value is bound to a fresh local no statement reads:
      -- `sol{}` names what an external call returns
      let rets ← match J.opt ok "parameters" with
        | some ps => (← PM.lift (J.arr ps "parameters")).mapM fun p => do
            let t ← declText p
            if J.str? p "name" != some "" then pure t else
              let st ← get
              set { st with fresh := st.fresh + 1 }
              pure s!"{t.trimRight} tryRet{st.fresh + 1}"
        | none => pure []
      let rets := if rets.isEmpty then "" else s!" returns ({", ".intercalate rets})"
      let okLocals := (← get).specLocals
      modify fun st => { st with specLocals := outerLocals }
      let cs ← catches.mapM fun cl => do
        withSpecScope do
          let e := (J.str? cl "errorName").getD ""
          let ps ← params cl
          let b ← block (← PM.lift (J.get cl "block"))
          match e, ps with
          | "", [] => pure s!"catch {b}"
          | "", [p] => pure s!"catch ({p}) {b}"
          | "Error", [p] => pure s!"catch Error({p}) {b}"
          | "Panic", [p] => pure s!"catch Panic({p}) {b}"
          | e, _ => unsupported s!"the catch clause `{e}`"
      modify fun st => { st with specLocals := okLocals }
      let b ← block (← PM.lift (J.get ok "block"))
      pure [s!"try {c}{rets} {b} {" ".intercalate cs}"]
    | [] => unsupported "a try with no clause"
  | "WhileStatement" =>
    let c ← expr (← PM.lift (J.get j "condition"))
    pure [s!"{← loopSpec j}while ({c}) {← block (← PM.lift (J.get j "body"))}"]
  | "DoWhileStatement" =>
    let c ← expr (← PM.lift (J.get j "condition"))
    pure [s!"{← loopSpec j}do {← block (← PM.lift (J.get j "body"))} while ({c})"]
  | "ForStatement" => withSpecScope do
    -- `for (init; c; upd)`, each part optional
    let part (k : String) : PM String := do
      match J.opt j k with
      | none | some .null => pure ""
      | some p =>
        match ← stmt1 p with
        | [t] => pure t
        | _ => unsupported s!"a `for` whose {k} is not one statement"
    let init ← part "initializationExpression"
    let c ← match J.opt j "condition" with
      | none | some .null => pure ""
      | some c => expr c
    let upd ← part "loopExpression"
    pure [s!"{← loopSpec j}for ({init}; {c}; {upd}) {← block (← PM.lift (J.get j "body"))}"]
  | "Break" => pure ["break"]
  | "Continue" => pure ["continue"]
  | "InlineAssembly" =>
    let some declaration := memoryRethrow? (← get).declarations j |
      unsupported "assembly other than revert(add(data, 32), mload(data))"
    let some source := J.str? declaration "name" | unsupported "a raw rethrow without its source name"
    let some name := lookupBy source (← get).specLocals |
      unsupported "raw rethrow of a value outside the local scope"
    pure [s!"assembly \{ revert(add({identText name}, 32), mload({identText name})) }"]
  -- `revert E(a, b);`: the custom error by its name, declared as a member
  -- (`errorMembers`)
  | "EmitStatement" =>
    let call ← PM.lift (J.get j "eventCall")
    unless J.kind call == "FunctionCall" && J.str? call "kind" == some "functionCall" do
      unsupported "an emit without a direct event call"
    let callee ← PM.lift (J.get call "expression")
    unless J.kind callee == "Identifier" do
      unsupported "an event named through a qualified expression"
    let some id := J.ref? callee | unsupported "an event without its declaration identity"
    let [declaration] := (← get).declarations.filter (fun d => J.id? d == some id)
      | unsupported "an event whose declaration identity is missing or ambiguous"
    unless J.kind declaration == "EventDefinition" do
      unsupported "an emit whose resolved declaration is not an event"
    let some name := J.str? declaration "name" | unsupported "an unnamed event declaration"
    unless !name.isEmpty && J.str? callee "name" == some name do
      unsupported "an emit whose name disagrees with its resolved event"
    let parameters ← PM.lift (J.get declaration "parameters")
    let params ← PM.lift (J.arr parameters "parameters")
    let args ← PM.lift (J.arr call "arguments")
    unless params.length == args.length && params.all (fun p => J.kind p == "VariableDeclaration") do
      unsupported "an emit whose arguments disagree with its resolved event"
    let rawNames := (J.arrD call "names").toList
    let names := rawNames.filterMap (·.getStr?.toOption)
    unless names.length == rawNames.length do unsupported "malformed named event arguments"
    unless names.isEmpty do
      let ps := params.map (fun p => (J.str? p "name").getD "")
      unless names.length == args.length && names.eraseDups.length == names.length &&
          ps.all (fun p => !p.isEmpty && names.contains p) do
        unsupported "named event arguments disagree with their resolved parameters"
      -- Legacy orders named operands by parameters; viaIR keeps source order.
      -- The body printer has no pipeline context, so do not guess a schedule.
      unsupported "named event arguments require pipeline-aware lowering"
    -- Logs are abstracted, but positional operands still run in source order
    -- in both supported pipelines. Resolve overloads by declaration identity.
    let args ← args.mapM expr
    pure [s!"emit {identText name}({", ".intercalate args})"]
  | "RevertStatement" =>
    let call ← PM.lift (J.get j "errorCall")
    let callee ← PM.lift (J.get call "expression")
    unless J.kind callee == "Identifier" do
      unsupported "a custom error named through a member access"
    let some e := J.str? callee "name" | unsupported "a custom error with no name"
    let args ← PM.lift (J.arr call "arguments")
    let rawNames := (J.arrD call "names").toList
    let some id := J.ref? callee | unsupported "a custom error without its declaration identity"
    let [decl] := (← get).declarations.filter (fun d => J.id? d == some id)
      | unsupported "a custom error whose declaration is missing or ambiguous"
    unless J.kind decl == "ErrorDefinition" && J.str? decl "name" == some e do
      unsupported "a custom error whose name disagrees with its resolved declaration"
    let st ← get
    let owners := st.declarations.filter fun owner => J.kind owner == "SourceUnit" ||
      (J.kind owner == "ContractDefinition" && (J.id? owner).any st.baseContracts.contains)
    let visible := owners.flatMap fun owner => (J.arrD owner "nodes").toList
    let [rendered] := visible.filter (fun d => J.kind d == "ErrorDefinition" &&
        J.str? d "name" == some e)
      | unsupported "custom error identities sharing a name need a nominal signature adapter"
    unless J.id? rendered == some id do
      unsupported "custom error identity is outside the rendered declaration scope"
    let ps ← PM.lift (J.arr (← PM.lift (J.get decl "parameters")) "parameters")
    unless ps.length == args.length && ps.all (fun p => J.kind p == "VariableDeclaration") do
      unsupported "custom error argument arity disagrees with declaration"
    if rawNames.isEmpty then
      let as ← args.mapM expr
      return [s!"revert {identText e}({", ".intercalate as})"]
    let names := rawNames.filterMap (·.getStr?.toOption)
    let pn := ps.map (fun p => (J.str? p "name").getD "")
    unless names.length == rawNames.length && names.length == args.length &&
        names.length == ps.length && names.eraseDups.length == names.length &&
        pn.eraseDups.length == pn.length && pn.all (fun p => !p.isEmpty && names.contains p) do
      unsupported "named error arguments disagree with their resolved parameters"
    -- Capture at the formal types BEFORE permuting values. In particular an
    -- effect/failure must not move when names are out of declaration order.
    let order := if (← get).namedErrorSourceOrder then names else pn
    let mut captures : List (String × String) := []
    let mut pre : List String := []
    for n in order do
      let some i := names.idxOf? n | unsupported "missing named error operand"
      let some k := pn.idxOf? n | unsupported "unknown named error operand"
      let some a := args[i]? | unsupported "missing named error operand"
      let some p := ps[k]? | unsupported "missing named error parameter"
      let ty ← PM.lift (tyText (← get).structs (← PM.lift (J.get p "typeName")))
      let value ← expr a
      let st ← get
      let taken := J.varDeclNames st.declarations ++ st.names.map (·.2)
      let mut x := s!"solcErrorCapture{st.fresh}"
      for _ in [:taken.length + 1] do
        if !taken.contains x then break
        x := x ++ "_"
      set { st with fresh := st.fresh + 1, pre := #[] }
      pre := pre ++ st.pre.toList
      let reference := ty == "string" || ty == "bytes" || ty.endsWith "]"
      -- Storage operands are POINTERS until the encoder reads them. Copying
      -- now would snapshot bytes before a later operand mutates storage.
      let storage := (J.tyStr a).endsWith " storage ref" || (J.tyStr a).endsWith " storage pointer"
      let loc := if reference then (if storage then " storage" else " memory") else ""
      pre := pre ++ [s!"{ty}{loc} {identText x} = {value}"]
      captures := captures ++ [(n, identText x)]
    let as ← pn.mapM fun n => match lookupBy n captures with
      | some x => pure x
      | none => unsupported "missing captured named error operand"
    pure (pre ++ [s!"revert {identText e}({", ".intercalate as})"])

  | k => unsupported s!"the statement `{k}`"

/-- A loop's specification, the `/// @custom:key` clauses above it that the
fixture keeps (`loopSpec`, read from the source by the loop's `src` offset as
solkey's `LoopSpecCompiler` reads them), each on a line of its own.  A
quantified clause (`\forall T x; a -> c`) the grammar reads as one; the rest
of the specification language (`\old`, `\exists`) is not a program
expression. -/
partial def loopSpec (j : Json) : PM String := do
  let some (.arr cs) := J.opt j "loopSpec" | pure ""
  let mut out := ""
  for c in cs do
    let some t := c.getStr?.toOption | unsupported "a loop clause that is not text"
    -- a quantifier, `\forall T x; …`, reads as a loop clause of its own
    -- (`RawInv`); the rest of the specification language does not
    if t.contains '\\' && (!t.startsWith "invariant \\forall " ||
        (t.splitOn "\\").tail.any (!·.startsWith "forall ")) then
      unsupported s!"the loop clause `{t}`: the specification language"
    let t := resolveSpecConstants (← get).specConstants (← get).specConstBlocked t
    let t := resolveSpecEnums (← get).specEnums (← get).specBlocked t
    let st ← get
    let bound := st.sourceStateNames ++ st.specLocals.flatMap (fun (a, b) => [a, b])
    let modelNames := st.sourceModelNames ++ st.specLocals.flatMap (fun (a, b) => [a, b])
    let scan := match st.scanLoop bound modelNames t with
      | .rejected features diagnostic => .rejected features { diagnostic with line := J.line j }
      | scan => scan
    modify fun state => { state with sourceScope := state.sourceScope.append scan }
    let t ← PM.lift ((st.rewriteLoop st.specLocals t).mapError (.unsupported · (J.line j)))
    out := out ++ s!"/// @custom:key {t}\n"
  pure out

end

end Solidity.Frontend
