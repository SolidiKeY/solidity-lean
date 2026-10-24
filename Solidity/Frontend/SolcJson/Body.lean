import Lean.Data.Json
import Solidity.Syntax

/-!
# solc's JSON: types, expressions and statements

What is left out and why, reading the JSON, types, and expressions and
statements.

A piece of `Frontend/SolcJson.lean`, whose docstring describes the whole.
-/

namespace Solidity.Frontend

open Lean (Json)

open Semantics

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
  /-- The source parameter types, before enums, aliases or addresses are lowered. -/
  sourceSignature : String := ""
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

/-- Arithmetic casts preserve signedness and width. Solc-validated boolean
and address expressions already retain their model type without a cast. -/
def sourceCast (t value : String) : String :=
  if t == "bool" || t == "address" || t == "address payable" then s!"({value})"
  else s!"{t}({value})"

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
      | some resolved => return ← resolved
      | none => throw (.unsupported s!"type declaration #{id} is not among the visible validated types")
    let n ← match J.opt j "pathNode" with
      | some p => J.str p "name"
      | none => J.str j "name"
    match lookupBy n S with
    | some (.ok m) => pure m
    | some (.error g) => throw g
    | none => throw (.unsupported s!"type `{n}` is not a struct of the contract")
  | "ArrayTypeName" =>
    let b ← tyText S (← J.get j "baseType")
    match J.opt j "length" with
    | none => pure s!"{b}[]"
    | some l => pure s!"{b}[{← J.str l "value"}]"
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
      match (J.str? k "value").bind (·.toNat?) with
      | some n => pure s!"{b}[{n}]"
      | none => throw (.unsupported "abi.decode to an array whose length is not a literal")
  | "Identifier" =>
    match (J.ref? t).bind fun id => lookupBy s!"#solc{id}" S with
    | some (.ok m) => pure m
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
      let v ← l.getObjValAs? String "value"
      match v.toNat? with
      | some n => pure (.ref (.fixed b n))
      | none => throw s!"array length `{v}`"
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
      pure s!"{← tyText S (← J.get x "typeName")} {← J.str x "name"};"
    pure s!"struct {p} \{ {" ".intercalate ms} }"

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
    if digits.isEmpty || e.natAbs > 4096 then none
    let n ← digits.toNat?
    let q ← Q.make n (10 ^ f.length)
    if e < 0 then Q.div q (Q.ofInt (10 ^ e.natAbs)) else Q.mul q (Q.ofInt (10 ^ e.natAbs))

/-- Is solc's type of the expression a compile-time constant? -/
def constTy (j : Json) : Bool :=
  let t := J.tyStr j
  t.startsWith "int_const" || t.startsWith "rational_const"

/-- The value of an expression of literals only, as solc computes it: exact
rational arithmetic, the bitwise operators and shifts on integers (`&`, `|`,
`^` on non-negative ones), `%` with the dividend's sign. -/
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
      let x ← a.int?
      let y ← b.int?
      if y == 0 then none else pure (Q.ofInt (x.tmod y))
    | some "**" => a.pow b
    | some "&" => pure (Q.ofInt ((← nat a) &&& (← nat b)))
    | some "|" => pure (Q.ofInt ((← nat a) ||| (← nat b)))
    | some "^" => pure (Q.ofInt ((← nat a) ^^^ (← nat b)))
    | some "<<" =>
      let k ← nat b
      if k > 4096 then none else pure (Q.ofInt ((← a.int?) * 2 ^ k))
    | some ">>" =>
      let k ← nat b
      if k > 4096 then none else pure (Q.ofInt ((← nat a) / 2 ^ k))
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
  | some (.ok m) => pure m
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
      | some (.ok m) => pure m
      | some (.error g) => throw g
      | none => unsupported s!"a reference to `{n}`"
    else pure (sourceType base)
  pure s!"{base}{sourceType dims}"

/-- Is the node `x.push()`? -/
def isPushCall (e : Json) : Bool :=
  J.kind e == "FunctionCall" &&
    ((J.opt e "expression").any fun f => J.kind f == "MemberAccess" &&
      J.str? f "memberName" == some "push")

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
  | "BinaryOperation" => sub "leftExpression" && sub "rightExpression"
  | "UnaryOperation" =>
    !(J.opt j "operator").any (fun o => o == .str "++" || o == .str "--" || o == .str "delete") &&
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

mutual

partial def expr (j : Json) : PM String := do
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
      pure ((lookupBy r (← get).names).getD n)
    | none => pure n
  | "Literal" =>
    let v ← PM.lift (J.str j "value")
    match (← PM.lift (J.str j "kind")) with
    | "bool" => pure v
    | "number" =>
      -- an address literal: its type is `address`, not a constant's
      match (parseRational v).bind Q.int? with
      | some n => pure (toString n)
      | none => unsupported s!"the number literal `{v}`"
    -- a literal of bytes, read at the type it meets (`RawExpr.bytesLit`):
    -- quoted when its text is, else spelt by its bytes
    | "string" | "unicodeString" =>
      match J.str? j "value" with
      | some v => pure v.quote
      | none => match J.str? j "hexValue" with
        | some h => pure s!"hex\"{h}\""
        | none => unsupported "a string literal without its value"
    | "hexString" =>
      match J.str? j "hexValue" with
      | some h => pure s!"hex\"{h}\""
      | none => unsupported "a hex literal without its value"
    | k => unsupported s!"a {k} literal"
  | "TupleExpression" =>
    match (← PM.lift (J.arr j "components")) with
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
    if let some bound := typeBound? (← get).enumBounds e m then
      let t := if (J.tyStr j).startsWith "enum " then "uint" else elemTy (J.tyStr j) false
      return s!"{t}({bound})"
    if let some r := J.ref? j then
      if (← get).freeFunctions.contains r then
        if let some name := lookupBy r (← get).names then return name
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
      pure s!"{x}.{m}"
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
    -- `abi.decode(b, (T, U))`: the types written as names
    if member == "decode" && (J.opt f "expression").any (fun o =>
        J.kind o == "Identifier" && J.str? o "name" == some "abi") then
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
      if to.startsWith "type(address" || to.startsWith "type(contract " then expr a
      else if to.startsWith "type(enum " then
        -- `E(x)`: the enum is a `contract!` member (`enumMembers`), and the
        -- elaborator asserts that `x` names one of its members
        let e := ((to.drop 10).dropRight 1).splitOn "." |>.getLast!
        pure s!"{e}({← expr a})"
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
    let as := if J.kind f == "MemberAccess" && J.str? f "memberName" == some "encodePacked" then
        (args.zip as).map fun (a, t) =>
          if (J.tyStr a).startsWith "enum " && J.kind a == "MemberAccess" then
            s!"{(((J.tyStr a).drop 5).splitOn ".").getLast!}({t})"
          else t
      else as
    let name ← if let some n := superName then pure n
      else if staticBase then
        match (J.ref? f).bind (lookupBy · (← get).staticNames) with
        | some name => pure name
        | none => unsupported "a base-qualified call without an imported function declaration"
      else if isExternalMember f then
        -- `I(0).f`: the receiver an address, `address(0).f` (`0.f` does not parse)
        let r ← expr (← PM.lift (J.get f "expression"))
        let r := if r.front.isDigit then s!"address({r})" else r
        pure s!"{r}.{← PM.lift (J.str f "memberName")}"
      else if valueCallee && J.kind f == "FunctionCall" then pure s!"({← expr f})"
      else expr f
    pure s!"{name}({", ".intercalate as})"
  | "structConstructorCall" =>
    -- `S(a, b)` or `S({b: y, a: x})`: the struct by its declaration, as the
    -- import names it (the table's, or the contract's own)
    let some id := J.ref? f | unsupported "a struct constructor without its declaration"
    let name ← match lookupBy s!"#solc{id}" (← get).structs with
      | some (.ok m) => pure m
      | some (.error g) => unsupported g.msg
      | none => unsupported s!"a struct constructor of the type declaration #{id}"
    let as ← args.mapM expr
    let names : List String := (J.arr? j "names").map
      (·.toList.filterMap (·.getStr?.toOption)) |>.getD []
    if names.isEmpty then pure s!"{name}({", ".intercalate as})"
    else
      pure s!"{name}(\{{", ".intercalate ((names.zip as).map fun (n, a) => s!"{n}: {a}")}})"
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
  let [d, Json.null] := (J.arr? j "declarations").map (·.toList) |>.getD []
    | none
  let call ← J.opt j "initialValue"
  let opts ← J.opt call "expression"
  let m ← J.opt opts "expression"
  guard (d != .null && J.tyStr d == "bool")
  guard (J.kind call == "FunctionCall" && J.kind opts == "FunctionCallOptions")
  let [Json.str "value"] := (J.arr? opts "names").map (·.toList) |>.getD []
    | none
  guard (J.kind m == "MemberAccess" && J.str? m "memberName" == some "call")
  let [a] := (J.arr? call "arguments").map (·.toList) |>.getD []
    | none
  guard (J.kind a == "Literal" && J.str? a "kind" == some "string" &&
    J.str? a "value" == some "")
  let v ← (J.arr? opts "options").bind (·[0]?)
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
        (J.opt f "expression").any (fun o => J.kind o == "Identifier" && J.str? o "name" == some "abi"))
  then expr v
  else unsupported "a tuple assigned from neither a tuple, nor a call of a function of this \
    contract, nor `(bool ok, ) = a.call{value: v}(\"\")`"

/-- A local's declaration, `T [storage|memory] x`. -/
def declText (d : Json) : PM String := do
  let T ← PM.lift (tyText (← get).structs (← PM.lift (J.get d "typeName")))
  let loc ← match J.opt d "storageLocation" with
    | some (.str "storage") => pure " storage"
    | some (.str "memory") => pure " memory"
    -- a calldata local: a memory one bound to calldata, read only
    -- (`calldataCheck`)
    | some (.str "calldata") => pure " memory"
    | _ => pure ""
  let name ← nameOf d
  if let some source := J.str? d "name" then
    unless source.isEmpty do
      modify fun st => { st with specLocals := (source, name) :: st.specLocals }
  pure s!"{T}{loc} {name}"

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
private def memoryRethrow? (j : Json) : Option String := do
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
  pure name

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
      let t := elemTy (J.tyStr e) false
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
    let some source := memoryRethrow? j |
      unsupported "assembly other than revert(add(data, 32), mload(data))"
    let some name := lookupBy source (← get).specLocals |
      unsupported "raw rethrow of a value outside the local scope"
    pure [s!"assembly \{ revert(add({name}, 32), mload({name})) }"]
  -- `revert E(a, b);`: the custom error by its name, declared as a member
  -- (`errorMembers`)
  | "RevertStatement" =>
    let call ← PM.lift (J.get j "errorCall")
    let callee ← PM.lift (J.get call "expression")
    unless J.kind callee == "Identifier" do
      unsupported "a custom error named through a member access"
    let some e := J.str? callee "name" | unsupported "a custom error with no name"
    let as ← (← PM.lift (J.arr call "arguments")).mapM expr
    pure [s!"revert {e}({", ".intercalate as})"]
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
    let t ← PM.lift ((st.rewriteLoop st.specLocals t).mapError (.unsupported · (J.line j)))
    out := out ++ s!"/// @custom:key {t}\n"
  pure out

end

end Solidity.Frontend
