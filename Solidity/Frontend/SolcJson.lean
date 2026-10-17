import Lean.Data.Json
import Solidity.Syntax

/-!
# solc's JSON AST, printed as `sol` text

The front end reads a contract from the AST solc writes
(`scripts/solc-ast.mjs` makes the fixture) and prints each function's body
as the text `sol_raw!{ … }` reads, so the one lowering path is the macros'
(`Syntax.lean`): nothing here builds a `RawStmt`.  The printer only
normalises what the grammar spells differently from Solidity:

* an expression of literals only (solc's type `int_const …` or
  `rational_const …`) is folded to its decimal value, in exact rational
  arithmetic as solc evaluates it at compile time (`2**256 - 1`,
  `7 / 2 * 2` is `7`), units (`1 gwei`, `2 days`, `unitFactor?`) and
  spellings (`0xff`, `1_000`, `2e3`, `0.5 ether`) included; a value that is
  not an integer is a `Gap`;
* a conversion to `address`, `address payable` or a contract is the address
  itself (an `address` is a `uint`), so `payable(owner)` is `owner`;
* `++`/`--` are spelt from solc's `prefix` flag, the decrement `−−` (two
  U+2212: `--` opens a Lean comment);
* a `bool` key of a mapping is the `uint` solc encodes it as, `0` or `1`: the
  mapping is declared `mapping(uint => V)` and `m[b]` is `m[b ? 1 : 0]`;
* a member of a pushed element reads the element through a storage local
  declared before the statement
  (`T storage pushRef1 = x.push(); pushRef1.f = v;`), only where that is
  solc's order: the left-hand side of an assignment of a constant, or a
  declaration's whole initial value.  Anywhere else (a right-hand side that
  reads state, a condition, a short-circuit operand) the hoisted push would
  run before, or instead of, what solc runs first, so it is a `Gap`;
* named arguments, `h({b: 1, a: 2})`, are put in the callee's parameter
  order, the order solc evaluates them in;
* a local named like a state variable or a Lean keyword is renamed with a
  trailing `_`, by its declaration (`referencedDeclaration`), so a member of
  the same name is untouched;
* a struct is the struct table's (`Semantics.structDef`), under the renames
  the import names, and its members are checked against the table, member
  by member; a struct that is not there, or differs, leaves out what uses it;
* a tuple of several components is printed where solkey reads one
  (`SolJSONParser.parseTupleStatement`): `(a, , b) = v`,
  `(uint x, , bool y) = v` and `return (a, b)`, the value a tuple or a call
  of a function by name (`requireTupleValue`);
* `(bool ok, ) = R.call{value: V}("")`, matched exactly as
  `SolJSONParser.isValueCall` matches it, is `bool ok = R.send(V)`; any
  other value call is a `Gap`.  solc forwards all gas there and `send` the
  2300-gas stipend, so the result is faithful only under the callback
  reading (`holdsC`, `docs/solc-alignment.md`);
* an unnamed value a `try`'s call returns is bound to a fresh `tryRetN`,
  which nothing reads;
* a loop is printed as written, `while`, `for`, `do … while`, `break`,
  `continue` (the macros lower them), its `/// @custom:key` clauses above it
  from the fixture's `loopSpec` (`loopSpec`);
* every function called by name is a `contract!` member
  (`SolcContract.funMembers`), callees first: a call is inlined where it is
  called.  A call that recurses, or of a function left out, leaves the
  caller out.

What the printer cannot write is a `Gap`, reported with its source line:
`excluded` where the model has no counterpart (a struct recursive through a
mapping), `unsupported` where the printer or the grammar lacks the form.
What would change a function's meaning if it were dropped is a `Gap` too:
an unsupported modifier or an immutable state variable. A contract that inherits is
refused whole. Supported constants are inlined by declaration identity;
unsupported constant types remain gaps. Overloads receive distinct internal
names, their calls resolve by solc declaration identity, and reports retain
their source signatures. Enums become their ordinal values and primitive
user-defined value types their underlying types. Numeric bounds and wrappers
retain arithmetic casts, including signedness and width. Narrow aliases and
runtime casts into enums remain unsupported.

The constructor (`kind` `constructor`, which solc names `""`) is read as a
function named `constructor` (`SolcContract.ctor`), as solkey's
`SolidityOutline` names it: a root of the calls, whatever its visibility,
and its supported modifiers run through the existing inliner. A mutable state
variable's initializer is printed with it, `uint x = 5;`
(`SolcContract.initMembers`), and a deployment runs it first.  One that
does not print, or calls a function left out, leaves the constructor out,
not the variable: a function's obligation holds from any well-typed storage
(solkey's do too), so no function needs it.
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

def kind (j : Json) : String := (j.getObjValAs? String "nodeType").toOption.getD ""

def line (j : Json) : Nat := (j.getObjValAs? Nat "line").toOption.getD 0

def ref? (j : Json) : Option Int := (j.getObjValAs? Int "referencedDeclaration").toOption

def id? (j : Json) : Option Int := (j.getObjValAs? Int "id").toOption

/-- solc's type of an expression, `typeDescriptions.typeString`. -/
def tyStr (j : Json) : String :=
  ((j.getObjVal? "typeDescriptions").toOption.bind
    fun t => (t.getObjValAs? String "typeString").toOption).getD ""

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
   "unsafe", "calc", "suffices", "obtain", "nomatch", "nofun", "forall", "exists", "Type",
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

/-- A type node as `sol` text: a mapping's `bool` key is its `uint`. -/
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
    if (narrowTy? b).isSome then
      throw (.unsupported s!"a narrow array element `{b}` is not modelled")
    match J.opt j "length" with
    | none => pure s!"{b}[]"
    | some l => pure s!"{b}[{← J.str l "value"}]"
  | "Mapping" =>
    let k ← tyText S (← J.get j "keyType")
    if (narrowTy? k).isSome then
      throw (.unsupported s!"a narrow mapping key `{k}` is not modelled")
    let k := if k == "bool" then "uint" else k
    let v ← tyText S (← J.get j "valueType")
    if (narrowTy? v).isSome then
      throw (.unsupported s!"a narrow mapping value `{v}` is not modelled")
    pure s!"mapping({k} => {v})"
  | k => throw (.unsupported s!"type node `{k}`")

/-- A type node as a `Ty`, to compare a struct's members with the table. -/
partial def tyOf (S : List (String × String)) (j : Json) : Except String Ty := do
  match J.kind j with
  | "ElementaryTypeName" =>
    let n ← (j.getObjValAs? String "name")
    match PrimTy.ofName? n with
    | some p => pure (.prim p)
    | none => throw s!"type `{n}`"
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
    match ← tyOf S (← j.getObjVal? "keyType") with
    | .prim k => pure (.ref (.mapping k (← tyOf S (← j.getObjVal? "valueType"))))
    | t => throw s!"mapping key `{t.toStr}`"
  | k => throw s!"type node `{k}`"

/-- Does the type node name the struct `s`? -/
partial def mentionsStruct (s : String) (j : Json) : Bool :=
  (J.nodes j).any fun n =>
    J.kind n == "UserDefinedTypeName" &&
      ((J.opt n "pathNode").bind (fun p => (p.getObjValAs? String "name").toOption)) == some s

/-- Does a mapping inside the type node name the struct `s`? -/
def mentionsThroughMapping (s : String) (j : Json) : Bool :=
  (J.nodes j).any fun n => J.kind n == "Mapping" && mentionsStruct s n

/-- The visible structs against the table: each renamed by `ren`, and
kept when its members are the table's, in order, at the same types.
Declaration keys preserve solc's resolution when a contract shadows a
file-level name. -/
def readStructs (ren : List (String × String)) (defs : List Json) : Structs := Id.run do
  let identities := defs.filterMap fun d => do
    let i ← J.id? d
    let n ← (d.getObjValAs? String "name").toOption
    pure (s!"#solc{i}", (lookupBy n ren).getD n)
  let shapes := defs.map fun d =>
    let n := ((d.getObjValAs? String "name").toOption).getD ""
    let m := (lookupBy n ren).getD n
    let line := J.line d
    let check : Except Gap String := do
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
      if structDef m == got then pure m
      else if (structDef m).isEmpty then
        throw (.unsupported s!"struct `{n}` (line {line}) is not in the struct table \
          (`Semantics.structDef`)")
      else
        throw (.unsupported s!"struct `{n}` (line {line}) differs from the table's `{m}`: \
          {got.map (·.1)} against {(structDef m).map (·.1)}")
    (d, n, check)
  let mut checked := shapes
  -- A table-shaped parent also requires every actual referenced declaration
  -- to pass. Propagate failures through at most one edge per round.
  for _ in [:defs.length] do
    checked := checked.map fun (d, n, shape) =>
      let checkedShape : Except Gap String := do
        let m ← shape
        for member in (← J.arr d "members") do
          let typeNode ← J.get member "typeName"
          for node in (J.nodes typeNode).filter (J.kind · == "UserDefinedTypeName") do
            let some id := (J.ref? node).orElse fun _ => (J.opt node "pathNode").bind J.ref?
              | throw (.unsupported s!"struct `{n}` has a member type without declaration identity")
            let some (_, dep, result) := checked.find? fun (decl, _, _) => J.id? decl == some id
              | throw (.unsupported s!"struct `{n}` refers to an unvalidated type declaration #{id}")
            match result with
            | .ok _ => pure ()
            | .error _ => throw (.unsupported s!"struct `{n}` depends on invalid struct `{dep}`")
        pure m
      (d, n, checkedShape)
  return checked.flatMap fun (d, n, check) =>
    ((J.id? d).toList.map fun i => (s!"#solc{i}", check)) ++ [(n, check)]

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
    let v ← (j.getObjValAs? String "value").toOption
    let q ← parseRational v
    match J.opt j "subdenomination" with
    | some (.str u) => Q.mul q (Q.ofInt (← unitFactor? u))
    | _ => pure q
  | "TupleExpression" =>
    match (j.getObjVal? "components").toOption.bind (·.getArr?.toOption) with
    | some #[c] => constVal c
    | _ => none
  | "UnaryOperation" =>
    let a ← constVal (← (j.getObjVal? "subExpression").toOption)
    match (j.getObjValAs? String "operator").toOption with
    | some "-" => pure { a with num := - a.num }
    | some "~" => pure (Q.ofInt (- (← a.int?) - 1))
    | _ => none
  | "BinaryOperation" =>
    let a ← constVal (← (j.getObjVal? "leftExpression").toOption)
    let b ← constVal (← (j.getObjVal? "rightExpression").toOption)
    let nat (q : Q) : Option Nat := do
      let n ← q.int?
      if n < 0 then none else pure n.toNat
    match (j.getObjValAs? String "operator").toOption with
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
  let [a] ← ((J.opt j "arguments").bind (·.getArr?.toOption)).map (·.toList) | none
  if let some n := (J.ref? a).bind (lookupBy · enums) then
    return if member == "min" then 0 else (n : Int)
  let t ← J.opt a "typeName"
  let name ← (t.getObjValAs? String "name").toOption
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

/-- Is the node `x.push()`? -/
def isPushCall (e : Json) : Bool :=
  J.kind e == "FunctionCall" &&
    ((J.opt e "expression").any fun f => J.kind f == "MemberAccess" &&
      (f.getObjValAs? String "memberName").toOption == some "push")

/-- Is the node `x.push().f`? -/
def isPushedMember (e : Json) : Bool :=
  J.kind e == "MemberAccess" && (J.opt e "expression").any isPushCall

/-- A contract-qualified member, never an object or `this` call. -/
def isBaseMember (contracts : List Int) (f : Json) : Bool :=
  J.kind f == "MemberAccess" && (J.opt f "expression").any fun receiver =>
    J.kind receiver == "Identifier" &&
      J.opt receiver "name" != some (.str "this") && J.opt receiver "name" != some (.str "super") &&
      (J.ref? receiver).any contracts.contains

def isSuperMember (f : Json) : Bool :=
  J.kind f == "MemberAccess" && (J.opt f "expression").any fun receiver =>
    J.kind receiver == "Identifier" && J.opt receiver "name" == some (.str "super")

/-- `x` run where a pushed member may be hoisted, or not. -/
def withPush {α : Type} (ok : Bool) (x : PM α) : PM α := do
  modify fun st => { st with pushOk := ok }
  let a ← x
  modify fun st => { st with pushOk := false }
  pure a

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
  if J.kind f == "MemberAccess" then
    let member := (f.getObjValAs? String "memberName").toOption.getD ""
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
      else
        let n ← match J.kind f with
          | "ElementaryTypeNameExpression" =>
            PM.lift (J.str (← PM.lift (J.get f "typeName")) "name")
          | _ => unsupported s!"the conversion to `{to}`"
        pure s!"{elemTy n false}({← expr a})"
    | _ => unsupported "a conversion of several arguments"
  | "functionCall" =>
    if isSuperMember f then
      unsupported "a super call: contextual next-base dispatch is not modelled"
    let staticBase := isBaseMember (← get).baseContracts f
    let attached := !staticBase && (J.ref? f).any ((← get).freeFunctions.contains) &&
      J.kind f == "MemberAccess" &&
      !((J.opt f "expression").bind J.ref?).any ((← get).libraries.contains)
    let names : List String := ((J.opt j "names").bind (·.getArr?.toOption)).map
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
    let as ← args.mapM expr
    let name ← if staticBase then
        match (J.ref? f).bind (lookupBy · (← get).staticNames) with
        | some name => pure name
        | none => unsupported "a base-qualified call without an imported function declaration"
      else expr f
    pure s!"{name}({", ".intercalate as})"
  | k => unsupported s!"a call of kind `{k}`"

end

/-- Is the node a tuple of several components, `(a, b)`, and not an inline
array (`SolJSONParser.isTuple`)? -/
def isTuple (j : Json) : Bool :=
  J.kind j == "TupleExpression" && !(J.opt j "isInlineArray").any (· == .bool true) &&
    ((J.opt j "components").bind (·.getArr?.toOption)).any (·.size > 1)

/-- Is the node a call by name, `f(a)`: of a function of the contract, where
a tuple is its value (`SolJSONParser.requireTupleValue`)? -/
def isNamedCall (j : Json) (helpers : List Int := []) (contracts : List Int := []) : Bool :=
  J.kind j == "FunctionCall" && (J.opt j "expression").any (fun f =>
    J.kind f == "Identifier" ||
    isBaseMember contracts f ||
    (J.kind f == "MemberAccess" && (J.ref? f).any helpers.contains))

/-- The receiver and the amount of `(bool ok, ) = R.call{value: V}("")`, the
one value call solkey reads, matched as `SolJSONParser.isValueCall` matches
it: two declarations, a `bool` and an empty one; the options exactly
`value`; the member `call`; one argument, the empty string. -/
def valueCall? (j : Json) : Option (Json × Json × Json) := do
  let [d, Json.null] := ((J.opt j "declarations").bind (·.getArr?.toOption)).map (·.toList) |>.getD []
    | none
  let call ← J.opt j "initialValue"
  let opts ← J.opt call "expression"
  let m ← J.opt opts "expression"
  guard (d != .null && J.tyStr d == "bool")
  guard (J.kind call == "FunctionCall" && J.kind opts == "FunctionCallOptions")
  let [Json.str "value"] := ((J.opt opts "names").bind (·.getArr?.toOption)).map (·.toList) |>.getD []
    | none
  guard (J.kind m == "MemberAccess" && (m.getObjValAs? String "memberName").toOption == some "call")
  let [a] := ((J.opt call "arguments").bind (·.getArr?.toOption)).map (·.toList) |>.getD []
    | none
  guard (J.kind a == "Literal" && (a.getObjValAs? String "kind").toOption == some "string" &&
    (a.getObjValAs? String "value").toOption == some "")
  let v ← ((J.opt opts "options").bind (·.getArr?.toOption)).bind (·[0]?)
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
  else unsupported "a tuple assigned from neither a tuple, nor a call of a function of this \
    contract, nor `(bool ok, ) = a.call{value: v}(\"\")`"

/-- A local's declaration, `T [storage|memory] x`. -/
def declText (d : Json) : PM String := do
  let T ← PM.lift (tyText (← get).structs (← PM.lift (J.get d "typeName")))
  let loc ← match J.opt d "storageLocation" with
    | some (.str "storage") => pure " storage"
    | some (.str "memory") => pure " memory"
    | _ => pure ""
  let name ← nameOf d
  if let some source := (d.getObjValAs? String "name").toOption then
    unless source.isEmpty do
      modify fun st => { st with specLocals := (source, name) :: st.specLocals }
  pure s!"{T}{loc} {name}"

/-- A source block, loop initializer or catch has a lexical local scope. -/
def withSpecScope {α : Type} (action : PM α) : PM α := do
  let names := (← get).specLocals
  let result ← action
  modify fun st => { st with specLocals := names }
  pure result

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
        (J.opt e "leftHandSide").any isTuple then
      -- `(a, , b) = v`
      return [s!"{← tuple (← PM.lift (J.get e "leftHandSide"))} = \
        {← tupleValue (← PM.lift (J.get e "rightHandSide"))}"]
    -- `x.push().f = c`: solc pushes, then stores the constant
    let ok := J.kind e == "Assignment" && (J.opt e "leftHandSide").any isPushedMember &&
      (J.opt e "rightHandSide").any fun r =>
        constTy r || (J.kind r == "Literal" && J.tyStr r == "bool")
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
      -- `(bool ok, ) = R.call{value: V}("")` is `bool ok = R.send(V)`, as solkey reads it;
      -- faithful only under `holdsC` (full gas, re-entry)
      return [s!"{← declText d} = {← operand r false}.send({← expr v})"]
    let ds ← PM.lift (J.arr j "declarations")
    if ds.length ≥ 2 then
      -- `(uint a, , bool b) = v`
      let ts ← ds.mapM fun d => if d == .null then pure "" else declText d
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
            pure (if (p.getObjValAs? String "name").toOption == some "" then t.trimRight else t)
        | none => pure []
      -- an unnamed return value is bound to a fresh local no statement reads:
      -- `sol{}` names what an external call returns
      let rets ← match J.opt ok "parameters" with
        | some ps => (← PM.lift (J.arr ps "parameters")).mapM fun p => do
            let t ← declText p
            if (p.getObjValAs? String "name").toOption != some "" then pure t else
              let st ← get
              set { st with fresh := st.fresh + 1 }
              pure s!"{t.trimRight} tryRet{st.fresh + 1}"
        | none => pure []
      let rets := if rets.isEmpty then "" else s!" returns ({", ".intercalate rets})"
      let okLocals := (← get).specLocals
      modify fun st => { st with specLocals := outerLocals }
      let cs ← catches.mapM fun cl => do
        withSpecScope do
          let e := ((cl.getObjValAs? String "errorName").toOption).getD ""
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
  | k => unsupported s!"the statement `{k}`"

/-- A loop's specification, the `/// @custom:key` clauses above it that the
fixture keeps (`loopSpec`, read from the source by the loop's `src` offset as
solkey's `LoopSpecCompiler` reads them), each on a line of its own.  A clause
in the specification language proper (`\forall`, `\old`) is not a program
expression, which the grammar reads. -/
partial def loopSpec (j : Json) : PM String := do
  let some (.arr cs) := J.opt j "loopSpec" | pure ""
  let mut out := ""
  for c in cs do
    let some t := c.getStr?.toOption | unsupported "a loop clause that is not text"
    if t.contains '\\' then unsupported s!"the loop clause `{t}`: the specification language"
    let t := resolveSpecConstants (← get).specConstants (← get).specConstBlocked t
    let t := resolveSpecEnums (← get).specEnums (← get).specBlocked t
    let st ← get
    let t ← PM.lift ((st.rewriteLoop st.specLocals t).mapError (.unsupported · (J.line j)))
    out := out ++ s!"/// @custom:key {t}\n"
  pure out

end

/-! ## A contract -/

/-- The NatSpec text of a node, `""` if none. -/
def docText (n : Json) : String :=
  ((J.opt n "documentation").bind fun d => (d.getObjValAs? String "text").toOption).getD ""

/-- One `@custom:key` clause: its directive and its text. -/
structure KeyClause where
  kind : String
  text : String
  deriving Inhabited

/-- A line's leading tag (`@` and a letter, then word characters, `:` or
`-`) and the rest of the line, after spaces and tabs. -/
def tagWord? (l : String) : Option (String × String) :=
  let t := l.dropWhile fun c => c == ' ' || c == '\t'
  match t.toList with
  | '@' :: c :: _ =>
    if c.isAlpha then
      let w := t.takeWhile fun c => c == '@' || c.isAlphanum || c == '_' || c == ':' || c == '-'
      some (w, t.drop w.length)
    else none
  | _ => none

/-- One clause's body: its directive word and the rest, whitespace collapsed. -/
def keyClause (body : String) : Except String KeyClause := do
  let ws := (body.split Char.isWhitespace).filter (· != "")
  let some w := ws.head? | throw "`@custom:key` needs a directive"
  let rest := " ".intercalate ws.tail
  unless ["box", "skip", "invariant", "requires", "ensures", "assignable"].contains w do
    throw s!"unknown `@custom:key` directive `{w}`"
  if ["invariant", "requires", "ensures"].contains w && rest.isEmpty then
    throw s!"`@custom:key {w}` needs an expression"
  if (w == "box" || w == "skip") && !rest.isEmpty then
    throw s!"`@custom:key {w}` takes no argument, got `{rest}`"
  pure { kind := w, text := rest }

/-- The `@custom:key` clauses of a NatSpec text, as solkey's `KeyNatspec`
reads them: a tag starts a line, and a clause runs to the next tag, so a tag
quoted inside a sentence is prose. -/
def keyClauses (doc : String) : Except String (List KeyClause) := do
  let mut out : Array KeyClause := #[]
  let mut cur : Option String := none
  for l in doc.splitOn "\n" do
    match tagWord? l with
    | some (w, rest) =>
      if let some b := cur then out := out.push (← keyClause b)
      cur := if w == "@custom:key" then some rest else none
    | none => cur := cur.map (· ++ "\n" ++ l)
  if let some b := cur then out := out.push (← keyClause b)
  pure out.toList

/-- Enum members visible by their canonical names; short names only for an
enum of this contract or the source unit. Other contracts' enums cannot leak. -/
def specEnumValues (units nodes enums : List Json) : List (String × Nat) :=
  enums.flatMap fun e =>
    let name := (e.getObjValAs? String "name").toOption.getD ""
    let canonical := (e.getObjValAs? String "canonicalName").toOption.getD name
    let visible := (units ++ nodes).any fun n => J.id? n == J.id? e
    let names := (canonical :: if visible then [name] else []).eraseDups
    let members := ((J.opt e "members").bind (·.getArr?.toOption)).getD #[]
    members.toList.zipIdx |>.flatMap fun (m, i) =>
      let member := (m.getObjValAs? String "name").toOption.getD ""
      names.map fun n => (s!"{n}.{member}", i)

/-- Ledger frame locations are outside Lean's storage-only assignable model.
Refuse their function before interpolating its clauses into the contract. -/
def ledgerAssignable (clause : KeyClause) : Bool :=
  clause.kind == "assignable" && Id.run do
    let tokens := (specTokens clause.text).filter fun token => !(token.toList.all Char.isWhitespace)
    return (tokens.zip tokens.tail).any fun (left, right) => left == "net" && right == "("

/-- The contract that lexically owns a declaration, if any. -/
def declarationOwner (units : List Json) (declaration : Json) : Option Int :=
  units.findSome? fun unit => do
    guard (J.kind unit == "ContractDefinition")
    let members ← (J.opt unit "nodes").bind (·.getArr?.toOption)
    guard (members.any fun member => J.id? member == J.id? declaration)
    J.id? unit

/-- Only literal-expression uint constants are substituted in specifications.
Other declarations still block their names, including inherited private ones. -/
def specConstantScope (units nodes : List Json) (owner : Option Int) :
    List (String × Nat) × List String := Id.run do
  let declarations := (units ++ nodes).filter (J.kind · == "VariableDeclaration")
  let values : List (Int × String × Nat) := declarations.filterMap fun declaration => do
    guard (J.opt declaration "constant" == some (.bool true))
    if J.opt declaration "visibility" == some (.str "private") then
      let defining := declarationOwner units declaration
      guard (defining.isSome && defining == owner)
    let typeNode ← J.opt declaration "typeName"
    guard (J.kind typeNode == "ElementaryTypeName")
    let typeName ← (typeNode.getObjValAs? String "name").toOption
    guard (["uint", "uint256"].contains typeName)
    let expression ← J.opt declaration "value"
    guard (constTy expression)
    let n ← (constVal expression).bind Q.int?
    guard (0 ≤ n && n < (2 : Int) ^ 256)
    let id ← J.id? declaration
    let name ← (declaration.getObjValAs? String "name").toOption
    pure (id, name, n.toNat)
  let ids := values.map (·.1)
  let blocked := declarations.filterMap fun declaration => do
    guard (!(J.id? declaration).any ids.contains)
    (declaration.getObjValAs? String "name").toOption
  return (values.map fun (_, name, n) => (name, n), blocked)

/-- Does a comment carry a specification proper (`KeyNatspec.isSpecified`)? -/
def isSpecified (cs : List KeyClause) : Bool :=
  cs.any fun c => ["invariant", "requires", "ensures"].contains c.kind

/-- solkey's obligation for the function `f` of a contract whose clauses are
`contract`, in `SolidityProblemSynthesizer`'s order: only a `public` or
`external` function has one, `skip` drops it, a specification replaces the
plain one, and `box` chooses its modality.  A clause solkey refuses is the
error. -/
def tagOf (contract : List KeyClause) (f : Json) : Except String Tag := do
  let vis := ((f.getObjValAs? String "visibility").toOption).getD ""
  -- a constructor has one whatever its visibility (`SolidityOutline.functionsOf`)
  let ctor := (f.getObjValAs? String "kind").toOption == some "constructor"
  unless ctor || vis == "public" || vis == "external" do return .internal
  let cs ← keyClauses (docText f)
  if cs.any (·.kind == "skip") then return .skip
  if isSpecified contract || isSpecified cs then return .specified
  if cs.any (·.kind == "box") then return .box
  return .diamond

/-- Every declaration of a function that must be renamed: one named like a
state variable or a Lean keyword gets `_` until it is fresh. -/
def renames (stateVars : List String) (f : Json) : List (Int × String) :=
  let decls := (J.nodes f).filter fun n =>
    J.kind n == "VariableDeclaration" &&
      (n.getObjValAs? Bool "stateVariable").toOption != some true
  -- A generated parameter name must not capture a quantified specification
  -- variable. Include every specification identifier, even in comments.
  let annotations := (J.nodes f).flatMap fun node =>
    docText node :: (((J.opt node "loopSpec").bind (·.getArr?.toOption)).getD #[]
      |>.toList.filterMap (·.getStr?.toOption))
  let specNames := annotations.flatMap fun text => (specTokens text).flatMap (·.splitOn ".")
  let taken := stateVars ++ specNames ++
    decls.filterMap fun d => (d.getObjValAs? String "name").toOption
  (decls.foldl (fun (acc : List String × List (Int × String)) d =>
    let (taken, out) := acc
    match (d.getObjValAs? String "name").toOption, J.id? d with
    | some n, some i => if n != "" && (stateVars.contains n || leanKeywords.contains n) then
      let rec fresh (k : Nat) (x : String) : String :=
        match k with
        | 0 => x
        | k + 1 => if taken.contains x then fresh k (x ++ "_") else x
      let name := fresh (taken.length + 1) (n ++ "_")
      (name :: taken, out ++ [(i, name)])
      else acc
    | _, _ => acc) (taken, [])).2

/-- Parameters and named returns initially visible inside a source body. -/
def specBodyBindings (f : Json) (names : List (Int × String)) : List (String × String) :=
  ["parameters", "returnParameters"].flatMap fun key =>
    (((J.opt f key).bind (J.opt · "parameters") |>.bind (·.getArr?.toOption)).getD #[]
      |>.toList).filterMap fun p => do
      let source ← (p.getObjValAs? String "name").toOption
      guard (!source.isEmpty)
      let id ← J.id? p
      pure (source, (lookupBy id names).getD source)

/-- The functions among `ids` that `f` calls by name, in order, each once. -/
def callees (ids : List Int) (f : Json) (freeFunctions : List Int := [])
    (aliases : List (Int × Int) := []) (contracts : List Int := []) : List Int :=
  (J.nodes f).foldl (init := []) fun acc n =>
    let r := if J.kind n == "FunctionCall" then
        (J.opt n "expression").bind fun e =>
          if J.kind e == "Identifier" then
            (J.ref? e).map fun id => (lookupBy id aliases).getD id
          else if !isSuperMember e && (isBaseMember contracts e ||
              (J.kind e == "MemberAccess" && (J.ref? e).any freeFunctions.contains)) then J.ref? e
          else none
      else none
    match r with
    | some r => if ids.contains r && !acc.contains r then acc ++ [r] else acc
    | none => acc

/-- The functions `f` reaches through `calls`, callees first and `f` last,
added to `done`; or a function on a cycle.  Each level adds a function to
`path`, so one more than the number of functions is enough `fuel`. -/
def reach (calls : Int → List Int) : Nat → List Int → List Int → Int → Except Int (List Int)
  | 0, _, _, f => throw f
  | fuel + 1, path, done, f =>
    if path.contains f then throw f
    else if done.contains f then pure done
    else do
      let done ← (calls f).foldlM (reach calls fuel (f :: path)) done
      pure (done ++ [f])

/-- Checked graph traversal: shared ancestors are visited once and a missing
declaration, cycle or exhausted bound is an error, never a partial closure. -/
def checkedReach (next : Int → Except String (List Int)) :
    Nat → List Int → List Int → Int → Except String (List Int)
  | 0, _, _, _ => throw "inheritance metadata traversal exceeded its bound"
  | fuel + 1, path, done, id =>
    if path.contains id then throw "cyclic inheritance or override metadata"
    else if done.contains id then pure done
    else do
      let parents ← next id
      let done ← parents.foldlM (checkedReach next fuel (id :: path)) done
      pure (done ++ [id])

def metadataIds (node : Json) (field : String) : Except String (List Int) := do
  match J.opt node field with
  | none => pure []
  | some value => (← value.getArr?).toList.mapM Json.getInt?

/-- First C3 implementation wins, including transitive overrides. -/
def overrideAliases (all implementations : List Json) (field : String) :
    Except String (List (Int × Int)) := do
  let next (id : Int) : Except String (List Int) := do
    let some declaration := all.find? (J.id? · == some id)
      | throw s!"override declaration #{id} is missing"
    metadataIds declaration field
  let mut result : List (Int × Int) := []
  for implementation in implementations do
    let some id := J.id? implementation | throw "override implementation has no identity"
    let ancestors ← checkedReach next (all.length + 1) [] [] id
    result := result ++ (ancestors.dropLast.map (·, id))
  pure result

/-- C3's deterministic merge, bounded by the number of contracts. -/
def mergeC3 : Nat → List (List Int) → Except String (List Int)
  | 0, sequences =>
    if sequences.all List.isEmpty then pure [] else throw "C3 merge exceeded its bound"
  | fuel + 1, sequences => do
    let sequences := sequences.filter (!·.isEmpty)
    if sequences.isEmpty then return []
    let some head := sequences.findSome? fun sequence =>
        sequence.head?.filter fun candidate => !(sequences.any fun other => other.tail.contains candidate)
      | throw "inheritance has no consistent C3 linearization"
    let rest := sequences.map fun sequence =>
      if sequence.head? == some head then sequence.tail else sequence
    pure (head :: (← mergeC3 fuel rest))

/-- A function as a `contract!` member, its body `ss`:
`function f(uint x) returns (uint lo, uint) { … }`. -/
def SolcFun.member (f : SolcFun) (ss : List String) : String :=
  let ps := ", ".intercalate (f.params.map fun (x, t) => s!"{t} {x}")
  let rs := if f.rets.isEmpty then "" else
    s!" returns ({", ".intercalate (f.rets.map fun (x, t) => if x.isEmpty then t else s!"{t} {x}")})"
  s!"{f.specMembers}function {f.name}({ps}){if f.payable then " payable" else ""}{f.modifierApps}{rs} \{ {String.join (ss.map (· ++ "; "))}}"

/-- The constructor as a `contract!` member, its body `ss`:
`constructor(uint a) payable { … }`. -/
def SolcFun.ctorMember (f : SolcFun) (ss : List String) : String :=
  let ps := ", ".intercalate (f.params.map fun (x, t) => s!"{t} {x}")
  s!"{f.specMembers}constructor({ps}){if f.payable then " payable" else ""}{f.modifierApps} \{ {String.join (ss.map (· ++ "; "))}}"

/-- Solc's complete, most-derived-first C3 order. The ancestry graph checks
that a trimmed or malformed fixture cannot silently omit an ancestor. -/
def contractLineage (units : List Json) (c : Json) : Except String (List Json) := do
  let contracts := units.filter (J.kind · == "ContractDefinition")
  let some own := J.id? c | throw "contract declaration has no identity"
  let find (id : Int) : Except String Json := do
    let some node := contracts.find? (J.id? · == some id)
      | throw s!"base contract #{id} is missing from this source unit"
    pure node
  let next (id : Int) : Except String (List Int) := do
    let node ← find id
    let bases ← match J.opt node "baseContracts" with
      | none => pure []
      | some value => pure (← value.getArr?).toList
    bases.mapM fun base => do
      let name ← (J.get base "baseName").mapError Gap.msg
      let some id := J.ref? name | throw "base contract reference has no declaration identity"
      pure id
  let direct ← next own
  let ids ← if direct.isEmpty then pure [own] else metadataIds c "linearizedBaseContracts"
  unless ids.head? == some own && ids.eraseDups.length == ids.length do
    throw "missing or malformed Solc C3 linearization; regenerate this fixture"
  let reached ← checkedReach next (contracts.length + 1) [] [] own
  unless ids.length == reached.length && reached.all ids.contains do
    throw "Solc C3 linearization does not contain the complete ancestry"
  let mut known : List (Int × List Int) := []
  for id in reached do
    let parents := (← next id).reverse
    let inherited ← parents.mapM fun parent => do
      let some order := lookupBy parent known | throw "C3 base order is missing"
      pure order
    let order ← mergeC3 (contracts.length + 1) (inherited ++ [parents])
    known := known ++ [(id, id :: order)]
  let some expected := lookupBy own known | throw "C3 root order is missing"
  unless ids == expected do throw "Solc C3 metadata disagrees with the inheritance order"
  ids.mapM find

/-- The contract `name` of the source unit `ast`, its structs renamed by `ren`. -/
def readContract (ast : Json) (name : String) (ren : List (String × String)) (testing : Bool := false)
    (rewriteSpec : String → List (String × String) → List (String × String) → String → Except String String :=
      fun _ params rets text => if params.isEmpty && rets.isEmpty then .ok text
        else .error "specification needs renamed locals: not imported")
    (rewriteLoop : List (String × String) → String → Except String String :=
      fun names text => if names.any (fun (a, b) => a != b) then
        .error "loop specification needs renamed locals: not imported" else .ok text) :
    Except String SolcContract := do
  let units := match ast.getObjVal? "nodes" with
    | .ok (.arr a) => a.toList
    | _ => []
  let some c := units.find? fun u =>
      J.kind u == "ContractDefinition" && (u.getObjValAs? String "name").toOption == some name
    | throw s!"no contract `{name}` in the AST"
  let lineage ← contractLineage units c
  let membersOf (node : Json) : List Json :=
    ((J.opt node "nodes").bind (·.getArr?.toOption)).getD #[] |>.toList
  let ownNodes := membersOf c
  for base in lineage.tail do
    let baseName := (base.getObjValAs? String "name").toOption.getD "?"
    if (membersOf base).any fun node =>
        J.kind node == "FunctionDefinition" && J.opt node "kind" == some (.str "constructor") then
      throw s!"base constructor of `{baseName}` is not modelled"
    let clauses ← (keyClauses (docText base)).mapError fun message =>
      s!"base contract `{baseName}`'s NatSpec: {message}"
    unless clauses.isEmpty do throw s!"inherited contract NatSpec of `{baseName}` is not modelled"
  let nodes := lineage.reverse.flatMap membersOf
  let c3Nodes := lineage.flatMap membersOf
  let baseContracts := lineage.filterMap J.id?
  let functionAliases ← if lineage.length == 1 then pure [] else
    overrideAliases c3Nodes (c3Nodes.filter (J.kind · == "FunctionDefinition")) "baseFunctions"
  let modifierAliases ← if lineage.length == 1 then pure [] else
    overrideAliases c3Nodes (c3Nodes.filter (J.kind · == "ModifierDefinition")) "baseModifiers"
  let cspec ← (keyClauses (docText c)).mapError fun m => s!"contract `{name}`'s NatSpec: {m}"
  if testing && cspec.any (fun c => ["requires", "ensures", "assignable"].contains c.kind) then
    throw "testing import: contract-level clauses must be invariants"
  let enumDefs := (J.nodes ast).filter (J.kind · == "EnumDefinition")
  let enumNames : Structs := enumDefs.flatMap fun e =>
    let n := (e.getObjValAs? String "name").toOption.getD ""
    let canonical := (e.getObjValAs? String "canonicalName").toOption.getD n
    ((J.id? e).toList.map fun i => (s!"#solc{i}", .ok "uint")) ++ [(canonical, .ok "uint")]
  let enumValues : List (Int × Nat) := enumDefs.flatMap fun e =>
    let vs := ((J.opt e "members").bind (·.getArr?.toOption)).getD #[]
    vs.toList.zipIdx |>.filterMap fun (v, i) => (J.id? v).map (·, i)
  let enumBounds : List (Int × Nat) := enumDefs.filterMap fun e => do
    let i ← J.id? e
    let vs ← (J.opt e "members").bind (·.getArr?.toOption)
    pure (i, vs.size - 1)
  let aliases := (J.nodes ast).filterMap fun d => do
    guard (J.kind d == "UserDefinedValueTypeDefinition")
    let i ← J.id? d
    let n ← (d.getObjValAs? String "name").toOption
    let t ← J.opt d "underlyingType"
    let t ← (tyText [] t).toOption
    guard (PrimTy.ofName? t).isSome
    pure (i, n, (d.getObjValAs? String "canonicalName").toOption.getD n, t)
  let valueTypes : List (Int × String) := aliases.map fun (i, _, _, t) => (i, t)
  let aliasNames : Structs := aliases.flatMap fun (i, _, qualified, t) =>
    [(s!"#solc{i}", .ok t), (qualified, .ok t)]
  let structDefs := (nodes.filter (J.kind · == "StructDefinition")) ++
    (units.filter (J.kind · == "StructDefinition"))
  let S := readStructs ren structDefs ++ enumNames ++ aliasNames
  let constants : List (Int × (String × Json)) := (J.nodes ast).filterMap fun v => do
    guard (J.kind v == "VariableDeclaration" && J.opt v "constant" == some (.bool true))
    let i ← J.id? v
    let value ← J.opt v "value"
    let typeNode ← J.opt v "typeName"
    let t ← (tyText S typeNode).toOption
    guard (PrimTy.ofName? t).isSome
    pure (i, t, value)
  let vars := nodes.filter fun n =>
    J.kind n == "VariableDeclaration" && (n.getObjValAs? Bool "stateVariable").toOption == some true
  let variableNames := vars.filterMap fun v => (v.getObjValAs? String "name").toOption
  unless variableNames.eraseDups.length == variableNames.length do
    throw "inherited state declarations share a name: distinct storage roots need renaming"
  let specValues := specEnumValues units nodes enumDefs
  let stateNames := vars.filterMap fun v => (v.getObjValAs? String "name").toOption
  let (constantValues, constantBlocked) := specConstantScope units nodes (J.id? c)
  let cspec := cspec.map fun c =>
    { c with text := resolveSpecEnums specValues stateNames (resolveSpecConstants constantValues constantBlocked c.text) }
  let invariants : List String := if testing then
    (cspec.filter (·.kind == "invariant")).map (fun c => s!"invariant {c.text};") else []
  let mut members : List String := invariants
  -- the variables kept: name, `sol` type, declaration
  let mut kept : List (String × String × Json) := []
  let mut dropped : List (Int × String × Gap) := []
  let mut droppedNames : List (String × Gap) := []
  for v in vars do
    let n := ((v.getObjValAs? String "name").toOption).getD ""
    let i := (J.id? v).getD 0
    let mutab := ((v.getObjValAs? String "mutability").toOption).getD "mutable"
    let fixed := (v.getObjValAs? Bool "constant").toOption == some true || mutab != "mutable"
    match (do
        if fixed then
          throw (.unsupported s!"`{n}` (line {J.line v}) is {if mutab == "mutable" then "constant" else mutab}: \
            a value fixed before any call, not a storage slot")
        let typeNode ← J.get v "typeName"
        if let some bad := (J.nodes typeNode).find? fun node =>
            J.kind node == "ElementaryTypeName" &&
              let t := (node.getObjValAs? String "name").toOption.getD ""
              !(PrimTy.ofName? t).isSome && !(narrowTy? t).isSome then
          throw (.unsupported s!"elementary state type `{(bad.getObjValAs? String "name").toOption.getD ""}` is not modelled")
        tyText S typeNode : Except Gap String) with
    | .ok t =>
      members := members ++ [s!"{t} {n};"]
      kept := kept ++ [(n, t, v)]
    | .error g =>
      dropped := dropped ++ [(i, n, g)]
      droppedNames := droppedNames ++ [(n, g)]
  let stateVars := vars.filterMap fun v => (v.getObjValAs? String "name").toOption
  -- every function, the constructor (`kind` `constructor`, named `""`) among them
  let ownFuns := ownNodes.filter (J.kind · == "FunctionDefinition")
  let ownIds := ownFuns.filterMap J.id?
  let inheritedFuns := nodes.filter fun node =>
    J.kind node == "FunctionDefinition" && !(J.id? node).any ownIds.contains
  let libraryNodes := units.filter fun unit => J.opt unit "contractKind" == some (.str "library")
  let libraries := libraryNodes.filterMap J.id?
  let freeHelpers := (units.filter (J.kind · == "FunctionDefinition") ++
    libraryNodes.flatMap (fun unit => ((J.opt unit "nodes").bind (·.getArr?.toOption)).getD #[]
      |>.toList.filter (J.kind · == "FunctionDefinition")))
    |>.filter fun f => !(J.id? f).any ownIds.contains
  let helperFuns := inheritedFuns ++ freeHelpers
  let helperIds := helperFuns.filterMap J.id?
  let freeFunctions := (freeHelpers.filterMap J.id? ++ libraryNodes.flatMap (fun unit =>
    ((J.opt unit "nodes").bind (·.getArr?.toOption)).getD #[] |>.toList.filterMap fun node =>
      if J.kind node == "FunctionDefinition" then J.id? node else none)).eraseDups
  let funs := ownFuns ++ helperFuns
  let kindOf (f : Json) : String := ((f.getObjValAs? String "kind").toOption).getD "function"
  let nameOfFun (f : Json) : String :=
    match (f.getObjValAs? String "kind").toOption with
    | some "function" | none => ((f.getObjValAs? String "name").toOption).getD ""
    | some k => k
  let funNames := ownFuns.map nameOfFun
  let internalName (f : Json) : String := Id.run do
    let n := nameOfFun f
    if (J.id? f).any helperIds.contains then
      let mut candidate := s!"solcFunction{(J.id? f).getD 0}"
      for _ in [:funNames.length + 1] do
        if !funNames.contains candidate then return candidate
        candidate := candidate ++ "_"
      return candidate
    if (funNames.filter (· == n)).length < 2 then return n
    let mut candidate := s!"{n}__solc{(J.id? f).getD 0}"
    for _ in [:funNames.length + 1] do
      if !funNames.contains candidate then return candidate
      candidate := candidate ++ "_"
    return candidate
  let staticNames : List (Int × String) := funs.filterMap fun f =>
    (J.id? f).map fun i => (i, internalName f)
  let funRenames ← staticNames.mapM fun (id, original) => do
    let target := (lookupBy id functionAliases).getD id
    let some resolved := lookupBy target staticNames
      | throw s!"override target #{target} of `{original}` is not imported"
    pure (id, resolved)
  let funParams : List (Int × List String) := funs.filterMap fun f => do
    let i ← J.id? f
    let ps ← (f.getObjVal? "parameters").toOption
    let ps ← (ps.getObjVal? "parameters").toOption
    let ps ← ps.getArr?.toOption
    pure (i, ps.toList.filterMap fun p => (p.getObjValAs? String "name").toOption)
  let modifierDefs := nodes.filter (J.kind · == "ModifierDefinition")
  let scopedIds := (funs ++ modifierDefs).filterMap J.id?
  let lexicalScopes ← (units.filter fun unit =>
      J.kind unit == "ContractDefinition" &&
        (membersOf unit).any fun member => (J.id? member).any scopedIds.contains).mapM fun unit => do
    let some id := J.id? unit | throw "defining contract has no identity"
    let scope ← contractLineage units unit
    pure (id, scope.reverse.flatMap membersOf)
  let scopeNodesOf (declaration : Json) : List Json :=
    (units.findSome? fun unit => do
      guard ((membersOf unit).any fun member => J.id? member == J.id? declaration)
      let id ← J.id? unit
      lookupBy id lexicalScopes) |>.getD []
  let modifierReads : List (Int × Except Gap String) := modifierDefs.filterMap fun m =>
    (J.id? m).map fun id => (id, do
      let scopeNodes := scopeNodesOf m
      let scopeValues := specEnumValues units scopeNodes enumDefs
      let (scopeConstants, scopeConstBlocked) := specConstantScope units scopeNodes (declarationOwner units m)
      let scopeNames := scopeNodes.filterMap fun node =>
        if J.kind node == "VariableDeclaration" then (node.getObjValAs? String "name").toOption else none
      let localNames := (J.nodes m).filterMap fun n =>
        if J.kind n == "VariableDeclaration" then (n.getObjValAs? String "name").toOption else none
      let names := renames stateVars m ++ funRenames
      let st : PState := { names, staticNames, baseContracts, dropped, structs := S, funParams, constants, enumValues, enumBounds, valueTypes, freeFunctions, libraries, specEnums := scopeValues, specBlocked := scopeNames ++ localNames, specConstants := scopeConstants, specConstBlocked := scopeConstBlocked ++ localNames, specLocals := specBodyBindings m names, rewriteLoop }
      let (text, _) ← (do
        unless (J.nodes m).any (J.kind · == "PlaceholderStatement") do
          unsupported "a modifier without a placeholder"
        let ps ← PM.lift (J.get m "parameters")
        let ps ← (← PM.lift (J.arr ps "parameters")).zipIdx.mapM fun ((p, index) : Json × Nat) => do
          let t ← PM.lift (tyText S (← PM.lift (J.get p "typeName")))
          if (narrowTy? t).isSome then
            unsupported s!"a modifier parameter of narrow type `{t}`"
          unless (PrimTy.ofName? t).isSome || t == "address payable" do
            unsupported s!"a modifier parameter of unsupported type `{t}`"
          let n ← nameOf p
          let n := if !n.isEmpty then n else Id.run do
            let taken := stateVars ++ (J.nodes m).filterMap fun node =>
              if J.kind node == "VariableDeclaration" then
                (node.getObjValAs? String "name").toOption else none
            let mut name := s!"solcModArg{id}_{index}"
            for _ in [:taken.length + 1] do
              if !taken.contains name then return name
              name := name ++ "_"
            return name
          pure s!"{t} {n}"
        let b ← block (← PM.lift (J.get m "body"))
        pure s!"modifier solcModifier{id}({", ".intercalate ps}) {b}").run st
      pure text)
  let modifierMembers := modifierReads.filterMap fun (_, text) => text.toOption
  let modifierInvocations (f : Json) : List Json :=
    ((J.opt f "modifiers").bind (·.getArr?.toOption)).getD #[] |>.toList
  let modifierId (m : Json) : Option Int := do
    let name ← J.opt m "modifierName"
    let id ← J.ref? name
    let text := (name.getObjValAs? String "name").toOption.getD ""
    if text.startsWith "super." then none
    else if text.contains '.' then some id
    else some ((lookupBy id modifierAliases).getD id)
  let read := funs.map fun f =>
    let fname := internalName f
    -- Lexical visibility belongs to the defining contract and its ancestors,
    -- rather than the most-derived contract that executes this helper.
    let scopeNodes := scopeNodesOf f
    let scopeValues := specEnumValues units scopeNodes enumDefs
    let (scopeConstants, scopeConstBlocked) := specConstantScope units scopeNodes (declarationOwner units f)
    let scopeNames := scopeNodes.filterMap fun n =>
      if J.kind n == "VariableDeclaration" then (n.getObjValAs? String "name").toOption else none
    let localNames := (J.nodes f).filterMap fun n =>
      if J.kind n == "VariableDeclaration" then (n.getObjValAs? String "name").toOption else none
    let rawSpec := (keyClauses (docText f)).toOption.getD []
    let resolvedSpec := rawSpec.map fun c =>
      { c with text := resolveSpecEnums scopeValues (scopeNames ++ localNames) (resolveSpecConstants scopeConstants (scopeConstBlocked ++ localNames) c.text) }
    -- Only parameters and named returns are in a function clause's scope.
    -- Renamed body locals cannot change the meaning of a pre/postcondition.
    let bindingsOf (key : String) :=
      ((J.opt f key).bind (J.opt · "parameters") |>.bind (·.getArr?.toOption)).getD #[] |>.toList
    let parameters := bindingsOf "parameters"
    let specRenamesOf (bindings : List Json) := bindings.filterMap fun p => do
      let id ← J.id? p
      let original ← (p.getObjValAs? String "name").toOption
      let renamed ← lookupBy id (renames stateVars f)
      pure (original, renamed)
    let fspecResult := resolvedSpec.mapM fun c => do
      let text ← rewriteSpec c.kind (specRenamesOf parameters)
        (specRenamesOf (bindingsOf "returnParameters")) c.text
      pure { c with text }
    let fspec := fspecResult.toOption.getD []
    -- what would change the function's meaning, or its constant's name
    let kind := kindOf f
    let refused : Option String :=
      if kind != "function" && kind != "freeFunction" && kind != "constructor" then some s!"a `{kind}` function"
      else if fname == "report" then some "named like the import's `report` table"
      else none
    let names := renames stateVars f ++ funRenames
    let st : PState := { names, staticNames, baseContracts, dropped, structs := S, funParams, constants, enumValues, enumBounds, valueTypes, freeFunctions, libraries, specEnums := scopeValues, specBlocked := scopeNames ++ localNames, specConstants := scopeConstants, specConstBlocked := scopeConstBlocked ++ localNames, specLocals := specBodyBindings f names, rewriteLoop }
    let apps : Except Gap String := do
      let apps ← (modifierInvocations f).mapM fun m => do
        let some id := modifierId m | throw (.unsupported "a modifier without a declaration identity" (J.line f))
        let some declared := lookupBy id modifierReads
          | throw (.unsupported "a modifier outside the imported contract" (J.line f))
        let _ ← declared
        let args := ((J.opt m "arguments").bind (·.getArr?.toOption)).getD #[]
        let (args, _) ← (args.toList.mapM expr).run st
        pure s!" solcModifier{id}({", ".intercalate args})"
      pure (String.join apps)
    let ps : Except Gap (List (String × String)) := (do
      let pl ← J.get f "parameters"
      (← J.arr pl "parameters").mapM fun p => do
        let ((t, x), _) ← (do
          let t ← PM.lift (tyText S (← PM.lift (J.get p "typeName")))
          let loc := match J.opt p "storageLocation" with
            | some (.str "memory") => " memory"
            | some (.str "storage") => " storage"
            | some (.str "calldata") => " calldata"
            | _ => ""
          pure (t ++ loc, ← nameOf p) : PM (String × String)).run st
        pure (x, t))
    let rs : Except Gap (List (String × String)) := do
      let some pl := J.opt f "returnParameters" | pure []
      (← J.arr pl "parameters").mapM fun p => do
        let ((t, x), _) ← (do
            let t ← PM.lift (tyText S (← PM.lift (J.get p "typeName")))
            let loc := match J.opt p "storageLocation" with
              | some (.str "memory") => " memory"
              | some (.str "storage") => " storage"
              | _ => ""
            pure (t ++ loc, ← nameOf p) : PM (String × String)).run st
        pure (x, t)
    let tag := tagOf cspec f
    let body : Except Gap (List (Nat × String)) := do
      if let .error m := tag then throw (.unsupported s!"its NatSpec: {m}" (J.line f))
      if testing && rawSpec.any ledgerAssignable then
        throw (.unsupported "ledger locations in assignable clauses are not modelled" (J.line f))
      if testing then
        if let .error reason := fspecResult then
          throw (.unsupported reason (J.line f))
      if testing then
        if let some (name, gap) := droppedNames.find? fun (name, _) =>
            !(parameters.any fun p => (p.getObjValAs? String "name").toOption == some name) &&
              resolvedSpec.any fun clause => specReadsName name (specTokens clause.text) then
          throw (.unsupported s!"its specification reads omitted state variable `{name}`: {gap.msg}" (J.line f))
      if testing && ((keyClauses (docText f)).toOption.getD []).any (·.kind == "invariant") then
        throw (.unsupported "function-level invariant: put invariants on the contract" (J.line f))
      if let some m := refused then throw (.unsupported m (J.line f))
      let _ ← apps
      let b ← J.get f "body"
      let (ss, _) ← ((← J.arr b "statements").flatMapM fun s => do
        pure ((← stmt s).map (J.line s, ·))).run st
      pure ss
    let sourceParams := ((J.opt f "parameters").bind (J.opt · "parameters")
      |>.bind (·.getArr?.toOption)).getD #[]
    let sourceTypes := sourceParams.toList.map fun p => sourceType (J.tyStr p)
    { name := fname, sourceName := nameOfFun f,
      sourceSignature := s!"{nameOfFun f}({",".intercalate sourceTypes})",
      modifierApps := apps.toOption.getD "",
      line := J.line f, tag := (tag.toOption).getD .malformed,
      params := (ps.toOption).getD [], rets := (rs.toOption).getD [],
      payable := (f.getObjValAs? String "stateMutability").toOption == some "payable",
      specMembers := if testing then String.join (fspec
        |>.filter (fun c => ["requires", "ensures", "invariant", "assignable"].contains c.kind)
        |>.map (fun c => s!"{c.kind} {c.text}; ")) else "",
      specClauses := if testing then fspec
        |>.filter (fun c => ["requires", "ensures", "invariant", "assignable"].contains c.kind)
        |>.map (fun c => (c.kind, c.text)) else [],
      body := do let _ ← ps; let _ ← rs; body : SolcFun }
  -- the initializers, each printed against the variables kept, as the
  -- right-hand side of an assignment the constructor runs first
  let initSt : PState := { names := funRenames, staticNames, baseContracts, dropped, structs := S, funParams, constants, enumValues, enumBounds, valueTypes, freeFunctions, libraries }
  let inits : Except Gap (List String) := kept.mapM fun (n, t, v) => do
    let some e := J.opt v "value" | pure s!"{t} {n};"
    match (expr e).run' initSt with
    | .ok x => pure s!"{t} {n} = {x};"
    | .error (.excluded m _) => throw (.excluded s!"the initializer of `{n}`: {m}" (J.line v))
    | .error (.unsupported m _) => throw (.unsupported s!"the initializer of `{n}`: {m}" (J.line v))
  -- the internal calls: a function is read with every function it reaches,
  -- and the ones called are the contract's members, callees first
  let ids := funs.filterMap J.id?
  -- an initializer's calls are the constructor's, declared or implicit
  let initCalls : List Int := (kept.filterMap fun (_, _, v) => (J.opt v "value").map (fun e => callees ids e freeFunctions functionAliases baseContracts))
    |>.flatten.eraseDups
  let ctorId : Option Int := (funs.find? (kindOf · == "constructor")).bind J.id?
  let callsOf : List (Int × List Int) := funs.filterMap fun f => (J.id? f).map fun i =>
    let modCalls := (modifierInvocations f).flatMap fun invocation =>
      ((modifierId invocation).bind fun id => modifierDefs.find? (J.id? · == some id))
        |>.toList.flatMap (fun m => callees ids m freeFunctions functionAliases baseContracts)
    (i, (callees ids f freeFunctions functionAliases baseContracts ++ modCalls ++ (if ctorId == some i then initCalls else [])).eraseDups)
  let calls (i : Int) : List Int := (lookupBy i callsOf).getD []
  let byId : List (Int × SolcFun) := (funs.zip read).filterMap fun (f, r) => (J.id? f).map (·, r)
  let nameAt (i : Int) : String := ((lookupBy i byId).map (·.name)).getD "?"
  let withCalls (i : Int) (r : SolcFun) : SolcFun :=
    let body : Except Gap (List (Nat × String)) := do
      let ss ← r.body
      match reach calls (ids.length + 1) [] [] i with
      | .error g => throw (.unsupported s!"the call of `{nameAt g}` is recursive: \
          a call is inlined, and the inlining would not end" r.line)
      | .ok order =>
        for c in order.dropLast do
          if let some { body := .error g, .. } := lookupBy c byId then
            throw (match g with
              | .excluded m _ => .excluded s!"it calls `{nameAt c}`, which is left out: {m}" r.line
              | .unsupported m _ => .unsupported s!"it calls `{nameAt c}`, which is left out: {m}" r.line)
        pure ss
    let cs := ((reach calls (ids.length + 1) [] [] i).toOption.getD []).dropLast
    { r with body, calls := cs.map nameAt }
  let closed : List (Int × SolcFun) := byId.map fun (i, r) => (i, withCalls i r)
  let order := ids.foldl (fun done i => (reach calls (ids.length + 1) [] done i).toOption.getD done) []
  let called := (ownIds.flatMap fun i =>
    ((reach calls (ids.length + 1) [] [] i).toOption.getD []).dropLast) ++
    initCalls.flatMap (fun i => (reach calls (ids.length + 1) [] [] i).toOption.getD [])
  let funMembers := order.filterMap fun i => do
    let r ← lookupBy i closed
    guard (ctorId != some i && (called.contains i ||
      (ownIds.contains i && (testing || !r.modifierApps.isEmpty))))
    let ss ← r.body.toOption
    pure (r.name, r.member (ss.map (·.2)))
  -- an initializer that does not print, or calls a function left out
  let initGap : Option Gap := match inits with
    | .error g => some g
    | .ok _ => initCalls.findSome? fun c => match lookupBy c closed with
      | some { body := .error g, .. } =>
        let m := s!"an initializer calls `{nameAt c}`, which is left out: {g.msg}"
        some (match g with | .excluded .. => .excluded m | .unsupported .. => .unsupported m)
      | _ => none
  let initMembers := match initGap, inits with
    | none, .ok ms => invariants ++ ms
    | _, _ => members
  let all := ((funs.zip read).filter fun (f, _) => (J.id? f).any ownIds.contains).map fun (f, r) =>
    (kindOf f == "constructor", ((J.id? f).map (withCalls · r)).getD r)
  let ctor := (all.find? (·.1)).map fun (_, r) =>
    { r with body := do
        let ss ← r.body
        if let some g := initGap then throw g
        pure ss }
  let funs := all.filterMap fun (c, r) => if c then none else some r
  pure { name, members, dropped := droppedNames, funs, funMembers, modifierMembers, ctor, initMembers, initGap }

end Solidity.Frontend

