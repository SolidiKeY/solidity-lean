import Solidity.Frontend.SolcJson.Admission
import Solidity.Frontend.SolcJson.Getters

/-!
# solc's JSON: a contract

A contract read off solc's JSON.

A piece of `Frontend/SolcJson.lean`, whose docstring describes the whole.
-/

namespace Solidity.Frontend

open Lean (Json)

open Semantics

/-! ## A contract -/

/-- The NatSpec text of a node, `""` if none. -/
def docText (n : Json) : String :=
  ((J.opt n "documentation").bind fun d => J.str? d "text").getD ""

/-- One `@custom:key` clause: its directive and its text. -/
structure KeyClause where
  kind : String
  text : String
  lexicalNames : List String := []
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
    let name := (J.str? e "name").getD ""
    let canonical := (J.str? e "canonicalName").getD name
    let visible := (units ++ nodes).any fun n => J.id? n == J.id? e
    let names := (canonical :: if visible then [name] else []).eraseDups
    let members := J.arrD e "members"
    members.toList.zipIdx |>.flatMap fun (m, i) =>
      let member := (J.str? m "name").getD ""
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
    let members ← J.arr? unit "nodes"
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
    let typeName ← J.str? typeNode "name"
    guard (["uint", "uint256"].contains typeName)
    let expression ← J.opt declaration "value"
    guard (constTy expression)
    let n ← (constVal expression).bind Q.int?
    guard (0 ≤ n && n < (2 : Int) ^ 256)
    let id ← J.id? declaration
    let name ← J.str? declaration "name"
    pure (id, name, n.toNat)
  let ids := values.map (·.1)
  let blocked := declarations.filterMap fun declaration => do
    guard (!(J.id? declaration).any ids.contains)
    J.str? declaration "name"
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
  let vis := (J.str? f "visibility").getD ""
  -- a constructor has one whatever its visibility (`SolidityOutline.functionsOf`)
  let ctor := J.str? f "kind" == some "constructor"
  unless ctor || vis == "public" || vis == "external" do return .internal
  -- `receive` and `fallback` have no name a transaction calls: no obligation
  if J.str? f "kind" == some "receive" || J.str? f "kind" == some "fallback" then return .internal
  let cs ← keyClauses (docText f)
  if cs.any (·.kind == "skip") then return .skip
  if isSpecified contract || isSpecified cs then return .specified
  if cs.any (·.kind == "box") then return .box
  return .diamond

/-- Every local declaration that needs a model name: unnamed input parameters
get a fresh identity-based name; state/keyword clashes get `_`. Unnamed
returns retain the existing return-frame naming convention. -/
def renames (stateVars : List String) (f : Json) : List (Int × String) :=
  let decls := (J.nodes f).filter fun n =>
    J.kind n == "VariableDeclaration" &&
      (n.getObjValAs? Bool "stateVariable").toOption != some true
  -- A generated parameter name must not capture a quantified specification
  -- variable. Include every specification identifier, even in comments.
  let annotations := (J.nodes f).flatMap fun node =>
    docText node :: (J.arrD node "loopSpec"
      |>.toList.filterMap (·.getStr?.toOption))
  let specNames := annotations.flatMap fun text => (specTokens text).flatMap (·.splitOn ".")
  let taken := stateVars ++ specNames ++
    decls.filterMap fun d => J.str? d "name"
  let inputs := ((J.opt f "parameters").bind (J.arr? · "parameters")).getD #[]
    |>.toList.filterMap J.id?
  (decls.foldl (fun (acc : List String × List (Int × String)) d =>
    let (taken, out) := acc
    match J.str? d "name", J.id? d with
    | some n, some i => if (n == "" && inputs.contains i) ||
        (n != "" && (stateVars.contains n || leanKeywords.contains n ||
          (decls.filter (fun other => J.str? other "name" == some n)).length > 1)) then
      let rec fresh (k : Nat) (x : String) : String :=
        match k with
        | 0 => x
        | k + 1 => if taken.contains x then fresh k (x ++ "_") else x
      let name := fresh (taken.length + 1) (if n.isEmpty then s!"solcArg{i}" else n ++ "_")
      (name :: taken, out ++ [(i, name)])
      else acc
    | _, _ => acc) (taken, [])).2

/-- Parameters and named returns initially visible inside a source body. -/
def specBodyBindings (f : Json) (names : List (Int × String)) : List (String × String) :=
  ["parameters", "returnParameters"].flatMap fun key =>
    (((J.opt f key).bind (J.arr? · "parameters")).getD #[]
      |>.toList).filterMap fun p => do
      let source ← J.str? p "name"
      guard (!source.isEmpty)
      let id ← J.id? p
      pure (source, (lookupBy id names).getD source)

/-- A callee's expressions that name the function called: itself, or both
branches of a conditional callee `(c ? f : g)` (`condCallee?`). -/
partial def calleeArms (e : Json) : List Json :=
  match J.kind e with
  | "TupleExpression" => match J.arr? e "components" with
    | some #[c] => calleeArms c
    | _ => [e]
  | "Conditional" =>
    ((J.opt e "trueExpression").toList ++ (J.opt e "falseExpression").toList).flatMap calleeArms
  | _ => [e]

/-- The functions among `ids` that `f` calls by name, in order, each once. -/
partial def executableNodes (declarations : List Json) (j : Json) : List Json :=
  if J.kind j == "MemberAccess" &&
      ((J.opt j "expression").any fun receiver =>
        match declarationMetadata declarations receiver ((J.str? j "memberName").getD "") with
        | .ok (some _) => true
        | _ => false) then [j]
  else match j with
  | .arr values => values.toList.flatMap (executableNodes declarations)
  | .obj fields =>
    let children := fields.toList.flatMap fun (_, value) => executableNodes declarations value
    if (J.str? j "nodeType").isSome then j :: children else children
  | _ => []

def unresolvedValueCalls (declarations : List Json) (root : Json) : List Json :=
  (executableNodes declarations root).filter fun node =>
    J.kind node == "FunctionCall" && J.str? node "kind" == some "functionCall" &&
      ((J.opt node "expression").toList.flatMap calleeArms).any fun callee =>
        let id := J.ref? callee
        ((id.bind fun id => declarations.find? (J.id? · == some id)).any fun decl =>
          J.kind decl == "VariableDeclaration" && (J.tyStr decl).startsWith "function ") ||
        (isValueCallee callee && id.isNone)

namespace FiniteDispatch

/-- Dispatch components retain the source ABI kind. Word and byte widths
are bounded in the representation; a word's width is eight times `width + 1`.
References and nominal types deliberately have no admitted case yet. -/
inductive Ty where
  | bool
  | word (signed : Bool) (width : Fin 32)
  | address
  | bytes (width : Fin 32)
  | function (external : Bool) (parameters returns : List Ty)
  deriving BEq, Repr

/-- The native dispatch key, matching `FunDecl.sigTy?`/`canonFnTy` for the
admitted components. It is used only with the retained source type below. -/
partial def Ty.native : Ty → String
  | .bool => "bool"
  | .word signed width =>
    let base := if signed then "int" else "uint"
    if width.val == 31 then base else s!"{base}{8 * (width.val + 1)}"
  | .address => "uint"
  | .bytes width => s!"bytes{width.val + 1}"
  | .function external parameters returns =>
    fnTyStr (parameters.map Ty.native) (returns.map Ty.native) external

/-- Parse only the scalar/function portion that the native dispatcher can
represent. Source ABI kinds are checked before a native-key comparison. The
fuel is also consumed by nested function types. -/
def parseType : Nat → String → Option Ty
  | 0, _ => none
  | fuel + 1, source => do
    -- solc's type strings spell these reserved qualifiers as separate words.
    -- Nominal names are never recognized by the scalar cases below.
    let source := (((source.replace " pure" "").replace " view" "").replace " payable" "").replace " internal" ""
    let source := String.mk (source.toList.filter (!Char.isWhitespace ·))
    if source == "bool" then return .bool
    if source == "address" then return .address
    if source == "uint" || source == "uint256" then return .word false ⟨31, by decide⟩
    if source == "int" || source == "int256" then return .word true ⟨31, by decide⟩
    if let some (parameters, returns, external) := fnParts? source then
      return .function external (← parameters.mapM (parseType fuel)) (← returns.mapM (parseType fuel))
    if let some (signed, digits) :=
        (if source.startsWith "uint" then some (false, source.drop 4)
         else if source.startsWith "int" then some (true, source.drop 3) else none) then
      let width ← digits.toNat?
      guard (8 ≤ width && width ≤ 256 && width % 8 == 0 && toString width == digits)
      let slot := width / 8 - 1
      if h : slot < 32 then return .word signed ⟨slot, h⟩ else none
    else if source.startsWith "bytes" then
      let width ← (source.drop 5).toNat?
      guard (1 ≤ width && width ≤ 32 && toString width == source.drop 5)
      if h : width - 1 < 32 then return .bytes ⟨width - 1, h⟩ else none
    else none

/-- A declaration-indexed source function, before generated selector helpers
exist. The source and native signatures are kept together: equality of their
erased native keys is never sufficient for admission. -/
structure Candidate where
  id : Int
  sourceName : String
  kind : String
  modelName : String
  visibility : String
  /-- Synthesized getters are external entries, never internal values. -/
  getter : Bool := false
  reference : Bool
  source : Option Ty
  native : Option Ty
  deriving Repr

private def parameters (declaration : Json) (key : String) : Option (List Json) := do
  let list ← J.opt declaration key
  return (← J.arr? list "parameters").toList

private def signature (fuel : Nat) (declaration : Json)
    (component : Json → Option Ty) : Option Ty := do
  let ps ← (← parameters declaration "parameters").mapM component
  let rs ← (← parameters declaration "returnParameters").mapM component
  guard (ps.length + rs.length ≤ fuel)
  return .function false ps rs

/-- Build native signatures from the same type spelling the body reader
emits, preserving exact source signatures separately. Reference parameters
make `native = none`, as in `FunDecl.sigTy?`. Nominal scalar erasures can have
a native key but no source type, so a matching call is refused. -/
def candidate (structs : Structs) (id : Int) (modelName : String) (declaration : Json) : Candidate :=
  let fuel := declaration.compress.length + 1
  { id, modelName, sourceName := (J.str? declaration "name").getD "",
    kind := (J.str? declaration "kind").getD "function",
    visibility := (J.str? declaration "visibility").getD "",
    reference := ((parameters declaration "parameters").getD [] ++
      (parameters declaration "returnParameters").getD []).any fun p =>
        let ty := J.tyStr p
        ty.startsWith "struct " || ty.startsWith "mapping(" ||
          ty.startsWith "bytes " || ty == "bytes" || ty == "string" || ty.startsWith "string " ||
          (!(ty.startsWith "function ") && ty.contains '['),
    source := signature fuel declaration (fun p => parseType fuel (J.tyStr p)),
    native := signature fuel declaration (fun p => do
      let typeNode ← J.opt p "typeName"
      let spelling ← (tyText structs typeNode).toOption
      parseType fuel spelling) }

/-- Actual synthesized getter parameters/results retain primitive source
kinds. A getter is usable only after its plan, identity and header scope all
succeed. An unknown/unsupported plan remains a candidate with unknown shape,
so an external dispatch cannot silently drop it. -/
def getterCandidate (id : Int) (f : SolcFun) : Candidate :=
  let valid := f.body.isOk && f.sourceDecl.any fun identity =>
    identity.declaration == some id && (match identity.callable with
      | .getter _ => true
      | _ => false)
  let signature : Option Ty := if valid then do
      let fuel := f.params.length + f.rets.length + 1
      let ps ← f.params.mapM fun (_, type) => parseType fuel type
      let rs ← f.rets.mapM fun (_, type) => parseType fuel type
      pure (.function false ps rs)
    else none
  { id, sourceName := f.sourceName, kind := "getter", modelName := f.name,
    visibility := "external", getter := true, reference := false,
    source := signature, native := signature }

private def asExternal (external : Bool) : Ty → Option Ty
  | .function _ ps rs => some (.function external ps rs)
  | _ => none

/-- Finite, conservative dependencies. A failure retains the original call
node for the ordinary fail-closed admission diagnostic. -/
structure Result where
  targets : List Int := []
  unresolved : List Json := []
  external : Bool := false
  deriving Inhabited

def Result.append (a b : Result) : Result :=
  { targets := (a.targets ++ b.targets).eraseDups,
    unresolved := a.unresolved ++ b.unresolved,
    external := a.external || b.external }

/-- All native-compatible source candidates are checked, including functions
which native `fnReachable` or emission order might later leave out. This is a
safe overapproximation, not a source-text points-to guess. Aliased source IDs
also retain their most-derived target. Generated metadata helpers cannot enter:
source functions and actual synthesized getter plans form `candidates`.
Getter declaration IDs enter the ordinary dependency graph with their header
scope, never by evaluating a mutable state initializer.

The native key may erase `address` to `uint`; a source-kind mismatch is refused.
External private/internal candidates and generated inherited/overload selector
names are refused until their source selector identities are modelled. -/
def inspectCall (declarations : List Json) (candidates : List Candidate)
    (aliases : List (Int × Int)) (call : Json) : Result := Id.run do
  let mut result : Result := {}
  for callee in (J.opt call "expression").toList.flatMap calleeArms do
    let id := J.ref? callee
    let declaration := id.bind fun id => declarations.find? (J.id? · == some id)
    let dynamic := (declaration.any fun d => J.kind d == "VariableDeclaration" &&
        (J.tyStr d).startsWith "function ") || (isValueCallee callee && id.isNone)
    unless dynamic do continue
    let some expected := parseType (callee.compress.length + 1) (J.tyStr callee) |
      return { result with unresolved := result.unresolved ++ [call] }
    let .function external _ returns := expected |
      return { result with unresolved := result.unresolved ++ [call] }
    if external && 1 < returns.length then
      return { result with unresolved := result.unresolved ++ [call] }
    result := { result with external := result.external || external }
    for target in candidates do
      -- SourceFunction.internalValue excludes getters from native internal
      -- dispatch. External dispatch uses their retained getter identities.
      if target.getter && !external then continue
      -- A known reference parameter is absent from native sigTy?. Any other
      -- signature we cannot reconstruct is unknown, not an ignorable target.
      if target.native.isNone && !target.reference then
        return { result with unresolved := result.unresolved ++ [call] }
      let native := target.native.bind (asExternal external)
      if native.map Ty.native != some expected.native then continue
      -- receive/fallback are C.funs entries in native dispatch, but Solidity
      -- cannot name them as function values. Never silently omit them.
      if !(["function", "freeFunction"].contains target.kind) && !(external && target.getter) then
        return { result with unresolved := result.unresolved ++ [call] }
      if target.source.bind (asExternal external) != some expected then
        return { result with unresolved := result.unresolved ++ [call] }
      if external && (!(["public", "external"].contains target.visibility) ||
          (!target.getter && target.modelName != target.sourceName)) then
        return { result with unresolved := result.unresolved ++ [call] }
      let alias := (lookupBy target.id aliases).getD target.id
      let some resolved := candidates.find? (·.id == alias) |
        return { result with unresolved := result.unresolved ++ [call] }
      if (resolved.native.bind (asExternal external)).map Ty.native != some expected.native ||
          resolved.source.bind (asExternal external) != some expected then
        return { result with unresolved := result.unresolved ++ [call] }
      if external && (!(["public", "external"].contains resolved.visibility) ||
          (!resolved.getter && resolved.modelName != resolved.sourceName)) then
        return { result with unresolved := result.unresolved ++ [call] }
      result := { result with targets := (result.targets ++ [target.id, alias]).eraseDups }
  return result

/-- This visits only dynamically called expressions identified by the body
reader. Ordinary calls and metadata references keep their existing identity
resolution and do not acquire unrelated execution dependencies. -/
def inspect (declarations : List Json) (candidates : List Candidate)
    (aliases : List (Int × Int)) (root : Json) : Result :=
  (unresolvedValueCalls declarations root).foldl (fun result call =>
    result.append (inspectCall declarations candidates aliases call)) {}

end FiniteDispatch

def nativePayment (root : Json) : Bool := (J.nodes root).any fun node =>
  (valueCall? node).isSome || (J.kind node == "MemberAccess" && nativeMember node &&
    ["send", "transfer"].contains ((J.str? node "memberName").getD ""))

def callees (ids : List Int) (f : Json) (freeFunctions : List Int := [])
    (aliases : List (Int × Int) := []) (contracts : List Int := [])
    (supers : List (Int × Int) := []) (getterIds : List Int := []) : List Int :=
  (J.nodes f).foldl (init := []) fun acc n =>
    let rs := if J.kind n == "FunctionCall" then
        ((J.opt n "expression").toList.flatMap calleeArms).filterMap fun e =>
          if J.kind e == "Identifier" then
            ((J.ref? e).filter (!getterIds.contains ·)).map fun id => (lookupBy id aliases).getD id
          else if isSuperMember e then (J.ref? e).bind (lookupBy · supers)
          else if isBaseMember contracts e then J.ref? e
          else if isExternalMember e && (J.ref? e).any ids.contains then
            (J.ref? e).map fun id => (lookupBy id aliases).getD id
          else if J.kind e == "MemberAccess" && (J.ref? e).any freeFunctions.contains then J.ref? e
          else none
      else (J.operatorFunction? n).toList
    rs.foldl (init := acc) fun acc r => if ids.contains r && !acc.contains r then acc ++ [r] else acc

/-- Whether `f` holds a call whose callee may write the caller's state, as
`docs/options.md`'s O7 reads it: a `try` of a callee not declared `view` or
`pure` (those solc calls by `STATICCALL`, which cannot write any state), or
a low-level `call`/`delegatecall` (a value call among them). -/
def writingCall (f : Json) : Bool :=
  (J.nodes f).any fun n =>
    (J.kind n == "TryStatement" &&
      !(((J.opt n "externalCall").bind (J.opt · "expression")).any fun e =>
        let ws := (J.tyStr e).splitOn " "
        ws.contains "pure" || ws.contains "view")) ||
    (J.kind n == "FunctionCall" && (J.opt n "expression").any fun e =>
      isExternalMember e &&
        !((J.tyStr e).splitOn " ").any (fun w => w == "pure" || w == "view")) ||
    (J.kind n == "MemberAccess" &&
      ["call", "delegatecall"].contains ((J.str? n "memberName").getD ""))

/-- The functions `f` reaches through `calls`, callees first and `f` last,
added to `done`: a call back into the path (a recursive call) adds nothing,
so each function of a cycle comes after every function it calls outside
the cycle, which is the order the elaborator reads them in (a recursive
function may call those it is mutually recursive with wherever they stand,
`isRecursive`).  Each level adds a function to `path`, so one more than the
number of functions is enough `fuel`; running out is the error. -/
def reach (calls : Int → List Int) : Nat → List Int → List Int → Int → Except Int (List Int)
  | 0, _, _, f => throw f
  | fuel + 1, path, done, f =>
    if path.contains f then pure done
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
  let ps := ", ".intercalate (f.params.map fun (x, t) => s!"{t} {identText x}")
  let rs := if f.rets.isEmpty then "" else
    s!" returns ({", ".intercalate (f.rets.map fun (x, t) => if x.isEmpty then t else s!"{t} {identText x}")})"
  s!"{f.specMembers}function {identText f.name}({ps}){if f.payable then " payable" else ""}{f.modifierApps}{rs} \{ {String.join (ss.map (· ++ "; "))}}"

/-- The constructor as a `contract!` member, its body `ss`:
`constructor(uint a) payable { … }`. -/
def SolcFun.ctorMember (f : SolcFun) (ss : List String) : String :=
  let ps := ", ".intercalate (f.params.map fun (x, t) => s!"{t} {identText x}")
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

/-- Closed scalar co-results need no new runtime frame: their only storage
result uses the existing shared storage-return call. No effects are folded. -/
def storageTuplePlan? (S : Structs) (f : Json) : Option StorageTuplePlan := do
  guard ([some "internal", some "private"].contains (J.str? f "visibility"))
  guard (J.arrD f "modifiers" |>.isEmpty)
  guard (J.opt f "virtual" != some (.bool true))
  guard (docText f |>.isEmpty)
  let returns ← J.opt f "returnParameters" >>= (J.arr? · "parameters")
  let returns := returns.toList
  guard (returns.length > 1 && returns.all (fun p => J.str? p "name" == some ""))
  let indexed := returns.zipIdx.filter fun (p, _) => J.str? p "storageLocation" == some "storage"
  let [(_, index)] := indexed | none
  let body ← J.opt f "body"
  let statements ← J.arr? body "statements"
  let terminal ← statements.toList.getLast?
  guard (J.kind terminal == "Return")
  guard (((J.nodes body).filter (J.kind · == "Return")).length == 1)
  let value ← J.opt terminal "expression"
  guard (J.kind value == "TupleExpression")
  let components ← J.arr? value "components"
  guard (components.size == returns.length)
  let rows ← returns.zipIdx.mapM fun (p, i) => do
    let type ← J.opt p "typeName"
    let spelling ← (tyText S type).toOption
    if i == index then return (spelling ++ " storage", "")
    guard (J.kind type == "ElementaryTypeName")
    guard (J.str? p "storageLocation" == some "default")
    let literal ← components[i]?
    guard (J.kind literal == "Literal")
    let text ← J.str? literal "value"
    if spelling == "bool" then
      guard (J.str? literal "kind" == some "bool" && ["true", "false"].contains text)
      return (spelling, text)
    guard (J.str? literal "kind" == some "number")
    guard ((narrowTy? spelling).isSome || ["uint", "uint256", "int", "int256"].contains spelling)
    let integer ← (constVal literal).bind (·.int?)
    guard (integer ≥ 0)
    let n := integer.toNat
    let (primitive, width) ← (narrowTy? spelling).orElse fun _ =>
      (PrimTy.ofName? spelling).map (·, 256)
    guard (primitive != .bool)
    guard (n < 2 ^ (if primitive == .int then width - 1 else width))
    return (spelling, sourceCast spelling (toString n))
  pure { index, types := rows.map (·.1), literals := rows.map (·.2) }

/-- Render declaration headers and optional construction assignments once.
The deployment table sees only earlier folded literal immutable values. -/
def renderInitializers (kept : List (String × String × Json)) (st : PState)
    (staticConstants immutables : List (Int × (String × Json)))
    (fixedBefore : Json → List Int) (superNamesOf : Json → List (Int × String))
    (phased : Bool) : Except Gap (List (Json × String × Option String)) :=
  kept.mapM fun (n, t, v) => do
    let declaration := s!"{t} {identText n};"
    let some e := J.opt v "value" | pure (v, declaration, none)
    let initialized := fixedBefore v
    let constants := staticConstants ++ immutables.map fun (id, ty, value) =>
      (id, ty, if initialized.contains id then value else defaultLiteral ty)
    match (expr e).run' { st with constants, superNames := superNamesOf v } with
    | .ok rhs => pure (v, (if phased then declaration else s!"{t} {identText n} = {rhs};"),
        some s!"{identText n} = {rhs}")
    | .error (.excluded m _) => throw (.excluded s!"the initializer of `{n}`: {m}" (J.line v))
    | .error (.unsupported m _) => throw (.unsupported s!"the initializer of `{n}`: {m}" (J.line v))

/-- The contract `name` of the source unit `ast`, its structs renamed by `ren`. -/
def readContract (ast : Json) (name : String) (ren : List (String × String)) (testing : Bool := false)
    (rewriteSpec : String → List (String × String) → List (String × String) → String → Except String String :=
      fun _ params rets text => if params.isEmpty && rets.isEmpty then .ok text
        else .error "specification needs renamed locals: not imported")
    (rewriteLoop : List (String × String) → String → Except String String :=
      fun names text => if names.any (fun (a, b) => a != b) then
        .error "loop specification needs renamed locals: not imported" else .ok text)
    (scanSource : Source.AdmissionRequest → Source.ScopeScan := fun _ => default)
    (scanLoop : List String → List String → String → Source.ScopeScan := fun _ _ _ => default)
    (viaIR : Bool := false) (compilerCode : List (Int × (String × String)) := []) :
    Except String SolcContract := do
  let units := match ast.getObjVal? "nodes" with
    | .ok (.arr a) => a.toList
    | _ => []
  let declarations := (J.nodes ast).filter fun node => (J.id? node).isSome
  let some c := units.find? fun u =>
      J.kind u == "ContractDefinition" && J.str? u "name" == some name
    | throw s!"no contract `{name}` in the AST"
  let lineage ← contractLineage units c
  let phasedInits := viaIR && lineage.length > 1
  let membersOf (node : Json) : List Json :=
    J.arrD node "nodes" |>.toList
  let ownNodes := membersOf c
  let nodes := lineage.reverse.flatMap membersOf
  let c3Nodes := lineage.flatMap membersOf
  let ownReceive := ownNodes.find? fun node => J.kind node == "FunctionDefinition" &&
    J.str? node "kind" == some "receive"
  let paymentIssues (root : Json) : List Source.Diagnostic :=
    if !nativePayment root then [] else
      let unsupported := match ownReceive with
        | some receive => !(J.arrD receive "modifiers").isEmpty
        | none => c3Nodes.any fun node => J.kind node == "FunctionDefinition" &&
            ["receive", "fallback"].contains ((J.str? node "kind").getD "")
      if unsupported then [{
        kind := .missingImplementation
        name := `solidity.selfPayment
        reason := "self-payment needs inherited receive, fallback or modifier dispatch"
        line := J.line root
        feature := some .emptyDataValueCall }] else []
  let baseContracts := lineage.filterMap J.id?
  let functionAliases ← if lineage.length == 1 then pure [] else
    overrideAliases c3Nodes (c3Nodes.filter fun node =>
      J.kind node == "FunctionDefinition" ||
        (J.kind node == "VariableDeclaration" && J.str? node "visibility" == some "public" &&
          J.opt node "stateVariable" == some (.bool true))) "baseFunctions"
  let modifierAliases ← if lineage.length == 1 then pure [] else
    overrideAliases c3Nodes (c3Nodes.filter (J.kind · == "ModifierDefinition")) "baseModifiers"
  let cspec ← (keyClauses (docText c)).mapError fun m => s!"contract `{name}`'s NatSpec: {m}"
  -- A base's contract clauses are inherited: the most-derived contract's
  -- specification is its bases' (most base first) and its own, each clause
  -- resolved in its own contract's scope.
  let enumDefs := (J.nodes ast).filter (J.kind · == "EnumDefinition")
  for declaration in enumDefs do
    let values ← (J.arr declaration "members").mapError Gap.msg
    let names ← (values.mapM (J.str · "name")).mapError Gap.msg
    let ids ← (values.mapM fun value => do
      let some id := J.id? value | throw "enum value lacks declaration identity"
      unless J.kind value == "EnumValue" && id ≥ 0 do throw "malformed enum value identity"
      pure id)
    unless !values.isEmpty && values.length ≤ 256 && names.all (!·.isEmpty) &&
        names.eraseDups.length == names.length && ids.eraseDups.length == ids.length do
      throw "malformed enum member table"

  let resolveIn (owner : Json) (cs : List KeyClause) : Except String (List KeyClause) := do
    let scope := (← contractLineage units owner).reverse.flatMap membersOf
    let stateNames := scope.filterMap fun v =>
      if J.kind v == "VariableDeclaration" then J.str? v "name" else none
    let (constantValues, constantBlocked) := specConstantScope units scope (J.id? owner)
    let values := specEnumValues units scope enumDefs
    cs.mapM fun c => do
      let text := resolveSpecEnums values stateNames (resolveSpecConstants constantValues constantBlocked c.text)
      pure { c with text := ← rewriteSpec c.kind [] [] text, lexicalNames := stateNames }
  let baseSpec ← lineage.tail.reverse.flatMapM fun base => do
    let baseName := (J.str? base "name").getD "?"
    let clauses ← (keyClauses (docText base)).mapError fun message =>
      s!"base contract `{baseName}`'s NatSpec: {message}"
    resolveIn base clauses
  let cspec := baseSpec ++ (← resolveIn c cspec)
  if testing && cspec.any (fun c => ["requires", "ensures", "assignable"].contains c.kind) then
    throw "testing import: contract-level clauses must be invariants"
  let enumNames : Structs := enumDefs.flatMap fun e =>
    let n := (J.str? e "name").getD ""
    let canonical := (J.str? e "canonicalName").getD n
    ((J.id? e).toList.map fun i => (s!"#solc{i}", .ok "uint8")) ++ [(canonical, .ok "uint8")]
  let enumValues : List (Int × Nat) := enumDefs.flatMap fun e =>
    let vs := J.arrD e "members"
    vs.toList.zipIdx |>.filterMap fun (v, i) => (J.id? v).map (·, i)
  let enumBounds : List (Int × Nat) := enumDefs.filterMap fun e => do
    let i ← J.id? e
    let vs ← J.arr? e "members"
    pure (i, vs.size - 1)
  let aliases := (J.nodes ast).filterMap fun d => do
    guard (J.kind d == "UserDefinedValueTypeDefinition")
    let i ← J.id? d
    let n ← J.str? d "name"
    let t ← J.opt d "underlyingType"
    let t ← (tyText [] t).toOption
    guard (valueTypeSupported t)
    pure (i, n, (J.str? d "canonicalName").getD n, t)
  let valueTypes : List (Int × String) := aliases.map fun (i, _, _, t) => (i, t)
  let aliasNames : Structs := aliases.flatMap fun (i, _, qualified, t) =>
    [(s!"#solc{i}", .ok t), (qualified, .ok t)]
  let ownStructDefs := (nodes.filter (J.kind · == "StructDefinition")) ++
    (units.filter (J.kind · == "StructDefinition"))
  -- Follow only referenced foreign struct identities, including their member
  -- types. Unrelated declarations do not enter the visible type table.
  let allStructs := (J.nodes ast).filter (J.kind · == "StructDefinition")
  let structDefs := Id.run do
    let mut selected := ownStructDefs
    for _ in [:allStructs.length] do
      let refs := (nodes ++ selected).flatMap fun node =>
        (J.nodes node).filterMap fun t =>
          if J.kind t == "UserDefinedTypeName" then
            (J.ref? t).orElse fun _ => (J.opt t "pathNode").bind J.ref?
          else none
      let added := allStructs.filter fun d =>
        !(selected.any (J.id? · == J.id? d)) && (J.id? d).any refs.contains
      if added.isEmpty then break
      selected := selected ++ added
    return selected
  -- Struct fields retain enum ABI width through the existing uint8 carrier.
  -- Native enum declarations separately retain nominal conversion ranges by
  -- identity. Do not reinterpret arbitrary user-defined types as integers.
  let structEnums := ((nodes ++ units).filter (J.kind · == "EnumDefinition")).filterMap fun e => do
    let id ← J.id? e
    guard (structDefs.any fun definition => (J.nodes definition).any fun node =>
      J.kind node == "UserDefinedTypeName" &&
        ((J.ref? node).orElse fun _ => (J.opt node "pathNode").bind J.ref?) == some id)
    let values ← J.arr? e "members"
    let names ← values.toList.mapM (J.str? · "name")
    guard (!names.isEmpty && names.length ≤ 256 && names.eraseDups.length == names.length &&
      names.all (!·.isEmpty))
    let taken := (J.nodes ast).filterMap (J.str? · "name")
    let printed := Id.run do
      let mut printed := s!"solcStructEnum{id}"
      for _ in [:taken.length + 1] do
        if !taken.contains printed then return printed
        printed := printed ++ "_"
      return printed
    pure (e, id, printed, names)
  let (SS, ownStructs) := readStructs ren structDefs (structEnums.map (·.2.1))
  let S := SS ++ enumNames ++ aliasNames
  let constants : List (Int × (String × Json)) := (J.nodes ast).filterMap fun v => do
    guard (J.kind v == "VariableDeclaration" && J.opt v "constant" == some (.bool true))
    let i ← J.id? v
    let value ← J.opt v "value"
    let typeNode ← J.opt v "typeName"
    let t ← (tyText S typeNode).toOption
    guard ((PrimTy.ofName? t).isSome || (narrowTy? t).isSome || (bytesTy? t).isSome || dynBytesTy t)
    pure (i, t, value)
  let vars := nodes.filter fun n =>
    J.kind n == "VariableDeclaration" && (n.getObjValAs? Bool "stateVariable").toOption == some true
  -- Never erase a transaction-local declaration into an ordinary storage root.
  -- This is a header check: unused declarations, generated getters and inherited
  -- roots are unsafe too, even if no selected body mentions the variable.
  if vars.any (fun v => J.str? v "storageLocation" == some "transient") then
    throw "solidity.transientState: transient declarations require transaction-local execution; this contract is not supported yet"
  -- Inline only an unwritten immutable with a known literal/default value.
  -- Other immutables retain a deployment root: even an unread initializer
  -- may mutate another root, allocate, call, fail or read the environment.
  let written := writtenIds ast
  let immutables : List (Int × (String × Json)) := vars.filterMap fun v => do
    guard (!phasedInits && (J.str? v "mutability") == some "immutable")
    let i ← J.id? v
    guard !(written.contains i)
    let t ← (tyText S (← J.opt v "typeName")).toOption
    guard ((PrimTy.ofName? t).isSome || (narrowTy? t).isSome)
    match J.opt v "value" with
    | some value => do guard ((constVal value).isSome || J.kind value == "Literal"); pure (i, t, value)
    | none => pure (i, t, defaultLiteral t)
  let staticConstants := constants
  let constants := staticConstants ++ immutables
  let fixedIds := immutables.map (·.1)
  let fixedBefore (v : Json) : List Int :=
    (vars.takeWhile (· != v)).filterMap J.id?
  -- a base's `private` variable of a name a later one declares again is a
  -- root of its own: renamed by its declaration's identity, as a local is
  -- (`x` of `PrivateRoot`, beside the derived `x`, is `x_PrivateRoot`), and
  -- every identifier reads it by that identity (`PState.names`)
  let variableNames := vars.filterMap fun v => J.str? v "name"
  let ownerName (v : Json) : String :=
    ((lineage.find? fun k => (membersOf k).any (J.id? · == J.id? v)).bind (J.str? · "name")).getD "base"
  let stateRenames : List (Int × String) := Id.run do
    let mut taken := variableNames
    let mut out := []
    for (v, k) in vars.zipIdx do
      let some n := J.str? v "name" | continue
      let some i := J.id? v | continue
      unless (vars.drop (k + 1)).any (J.str? · "name" == some n) do continue
      let mut x := s!"{n}_{ownerName v}"
      for _ in [:taken.length + 1] do
        if !taken.contains x then break
        x := x ++ "_"
      taken := x :: taken
      out := out ++ [(i, x)]
    return out
  -- a specification reads a variable by its name, which would now name the
  -- last declaration: refused where one names a renamed variable
  let renamedNames := (vars.filter fun v => (J.id? v).any fun i => (lookupBy i stateRenames).isSome)
    |>.filterMap (J.str? · "name")
  let specTexts := lineage.map docText ++ nodes.flatMap fun m => (J.nodes m).flatMap fun node =>
    docText node :: (J.arrD node "loopSpec" |>.toList.filterMap (·.getStr?.toOption))
  if specTexts.any fun t => (specTokens t).any fun w => renamedNames.contains ((w.splitOn ".").headD w) then
    throw "inherited state declarations share a name a specification reads: \
      distinct storage roots, the specification reads them by name"
  let invariants : List String := if testing then
    (cspec.filter (·.kind == "invariant")).map (fun c => s!"invariant {c.text};") else []
  -- the enums, as `contract!` members, for the conversions `E(x)` to check
  -- their argument against
  let enumMembers : List String := (nodes.filter (J.kind · == "EnumDefinition")).filterMap fun e => do
    let n ← J.str? e "name"
    let ms := (J.arrD e "members").toList.filterMap (J.str? · "name")
    pure s!"enum {identText n} \{ {", ".intercalate (ms.map identText)} }"
  -- the contract's own structs, declared: a struct whose members do not print
  -- leaves out what uses it, as an unreadable struct does
  let structEnumNames : Structs := structEnums.map fun (_, id, _, _) =>
    (s!"#solc{id}", .ok "uint8")
  let structEnumMembers := structEnums.map fun (_, _, printed, names) =>
    s!"enum {identText printed} \{ {", ".intercalate (names.map identText)} }"
  let enumMembers := enumMembers ++ structEnumMembers
  let enumNativeNames : List (Int × String) := (structEnums.map fun (_, id, printed, _) => (id, printed)) ++
    ((nodes.filter (J.kind · == "EnumDefinition")).filterMap fun e => do
      pure (← J.id? e, ← J.str? e "name"))
  let structMembers := ownStructs.filterMap fun o =>
    (ownStructMembers (structEnumNames ++ S) [o]).toOption.bind (·.head?)
  -- The native ABI decoder has no nominal enum-cardinality type. Refuse
  -- enum/composite decode targets rather than widening them to uint8 values.
  let enumDecodeTypes := Id.run do
    let mut selected := enumDefs.filterMap J.id?
    for _ in [:structDefs.length] do
      let added := structDefs.filterMap fun definition => do
        let id ← J.id? definition
        guard (!selected.contains id)
        guard ((J.nodes definition).any fun node =>
          J.kind node == "UserDefinedTypeName" &&
            ((J.ref? node).orElse fun _ => (J.opt node "pathNode").bind J.ref?).any selected.contains)
        pure id
      if added.isEmpty then break
      selected := selected ++ added
    return selected
  -- the custom errors, the contract's and the file's, as `contract!`
  -- members: a `revert E(…)` folds its selector from the declared types
  let errorMembers : List String := ((nodes ++ units).filter (J.kind · == "ErrorDefinition")).filterMap
    fun e => do
      let n ← J.str? e "name"
      let ps ← (J.opt e "parameters").bind fun ps => (J.arrD ps "parameters").toList.mapM fun p =>
        ((J.get p "typeName").toOption.bind fun t => (tyText S t).toOption)
      pure s!"error {identText n}({", ".intercalate ps});"
  let mut members : List String := invariants ++ enumMembers ++ structMembers ++
    errorMembers.eraseDups
  -- the variables kept: name, `sol` type, declaration
  let mut kept : List (String × String × Json) := []
  let mut dropped : List (Int × String × Gap) := []
  let mut droppedNames : List (String × Gap) := []
  for v in vars do
    let i := (J.id? v).getD 0
    let n := (lookupBy i stateRenames).getD ((J.str? v "name").getD "")
    let mutab := (J.str? v "mutability").getD "mutable"
    let fixed := (v.getObjValAs? Bool "constant").toOption == some true ||
      (mutab != "mutable" && !(mutab == "immutable" && !fixedIds.contains i))
    match (do
        if fixedIds.contains i then
          throw (.unsupported s!"`{n}` (line {J.line v}) is immutable and never written: \
            its value is inlined, not a storage slot")
        if fixed then
          throw (.unsupported s!"`{n}` (line {J.line v}) is {if mutab == "mutable" then "constant" else mutab}: \
            a value fixed before any call, not a storage slot")
        let typeNode ← J.get v "typeName"
        if let some bad := (J.nodes typeNode).find? fun node =>
            J.kind node == "ElementaryTypeName" &&
              let t := (J.str? node "name").getD ""
              !(PrimTy.ofName? t).isSome && !(narrowTy? t).isSome && !(bytesTy? t).isSome &&
              !dynBytesTy t then
          throw (.unsupported s!"elementary state type `{(J.str? bad "name").getD ""}` is not modelled")
        tyText S typeNode : Except Gap String) with
    | .ok t =>
      members := members ++ [s!"{t} {identText n};"]
      kept := kept ++ [(n, t, v)]
    | .error g =>
      dropped := dropped ++ [(i, n, g)]
      droppedNames := droppedNames ++ [(n, g)]
  let stateVars := vars.filterMap (J.str? · "name") ++ stateRenames.map (·.2)
  -- every function, the constructor (`kind` `constructor`, named `""`) among them
  let ownFuns := ownNodes.filter (J.kind · == "FunctionDefinition")
  let ownIds := ownFuns.filterMap J.id?
  let inheritedFuns := nodes.filter fun node =>
    J.kind node == "FunctionDefinition" && !(J.id? node).any ownIds.contains
  -- A testing import exposes the inherited ABI entry, with its existing
  -- declaration identity and shared body. Overridden and non-public helpers
  -- stay dependencies rather than duplicate externally callable entries.
  let entryIds := ownIds ++ (if testing then inheritedFuns.filterMap fun f => do
    guard (J.str? f "kind" == some "function")
    guard (["public", "external"].contains ((J.str? f "visibility").getD ""))
    let id ← J.id? f
    guard ((lookupBy id functionAliases).getD id == id)
    pure id
    else [])
  let libraryNodes := units.filter fun unit => J.opt unit "contractKind" == some (.str "library")
  let libraries := libraryNodes.filterMap J.id?
  let freeHelpers := (units.filter (J.kind · == "FunctionDefinition") ++
    libraryNodes.flatMap (fun unit => J.arrD unit "nodes"
      |>.toList.filter (J.kind · == "FunctionDefinition")))
    |>.filter fun f => !(J.id? f).any ownIds.contains
  let helperFuns := inheritedFuns ++ freeHelpers
  let helperIds := helperFuns.filterMap J.id?
  let freeFunctions := (freeHelpers.filterMap J.id? ++ libraryNodes.flatMap (fun unit =>
    J.arrD unit "nodes" |>.toList.filterMap fun node =>
      if J.kind node == "FunctionDefinition" then J.id? node else none)).eraseDups
  let funs := ownFuns ++ helperFuns
  let kindOf (f : Json) : String := (J.str? f "kind").getD "function"
  let nameOfFun (f : Json) : String :=
    match J.str? f "kind" with
    | some "function" | none => (J.str? f "name").getD ""
    | some k => k
  let funNames := ownFuns.map nameOfFun
  let generatedTaken := declarations.filterMap (J.str? · "name") ++ stateRenames.map (·.2) ++
    ownStructs.map (·.2) ++ ren.map (·.2) ++
    (funs ++ nodes.filter (J.kind · == "ModifierDefinition")).flatMap fun d =>
      (renames stateVars d).map (·.2)
  let internalName (f : Json) : String := Id.run do
    let n := nameOfFun f
    if (J.id? f).any helperIds.contains then
      return freshSourceName generatedTaken s!"solcFunction{(J.id? f).getD 0}"
    if (funNames.filter (· == n)).length < 2 then return n
    return freshSourceName generatedTaken s!"{n}__solc{(J.id? f).getD 0}"
  -- Resolve function-value dependencies before admitting or reading bodies.
  -- Selector metadata helpers are generated later and are not source candidates.
  let dispatchCandidates := funs.filterMap fun f => do
    guard (kindOf f != "constructor")
    let id ← J.id? f
    pure (FiniteDispatch.candidate S id (internalName f) f)
  let dispatchMissingIds := funs.any fun f =>
    kindOf f != "constructor" && (J.id? f).isNone
  let staticNames : List (Int × String) := funs.filterMap fun f =>
    (J.id? f).map fun i => (i, internalName f)
  -- A getter is a separate callable beside its storage root. Its declaration
  -- identity belongs only to member resolution, never to bare local/state reads.
  let getterVariables := vars.filter fun v => J.str? v "visibility" == some "public"
  let getterNames : List (Int × String) := Id.run do
    let mut taken := generatedTaken ++ staticNames.map (·.2)
    let mut out := []
    for v in getterVariables do
      let some id := J.id? v | continue
      let name := freshSourceName taken s!"solcGetter{id}"
      taken := name :: taken
      out := out ++ [(id, name)]
    return out
  let entryNames := staticNames ++ getterNames
  -- `super.f` in a declaration of contract `D` names, in the most-derived
  -- contract's C3 order, the first contract after `D` implementing `f` with
  -- the referenced declaration's parameter types (solc's `superFunction`).
  -- Every body is inlined once per most-derived contract, so this is static.
  let paramTypes (d : Json) : List String :=
    ((J.opt d "parameters").bind (J.arr? · "parameters")).getD #[] |>.toList.map J.tyStr
  let superTarget (owner ref : Int) : Option Int := do
    let decl ← c3Nodes.find? (J.id? · == some ref)
    let fname ← J.str? decl "name"
    let after := (lineage.dropWhile (J.id? · != some owner)).drop 1
    after.findSome? fun k => (membersOf k).findSome? fun m =>
      if J.kind m == "FunctionDefinition" && J.str? m "name" == some fname &&
          (J.str? m "kind").getD "function" == "function" &&
          (J.opt m "body").any (· != .null) && paramTypes m == paramTypes decl then J.id? m
      else none
  let supersOf (d : Json) : List (Int × Int) := Id.run do
    let some owner := declarationOwner units d | return []
    (J.nodes d).filterMap fun n => do
      guard (isSuperMember n)
      let r ← J.ref? n
      pure (r, ← superTarget owner r)
  let superNamesOf (d : Json) : List (Int × String) :=
    (supersOf d).filterMap fun (r, t) => (lookupBy t staticNames).map (r, ·)
  let funRenames ← staticNames.mapM fun (id, original) => do
    let target := (lookupBy id functionAliases).getD id
    let some resolved := lookupBy target entryNames
      | throw s!"override target #{target} of `{original}` is not imported"
    pure (id, resolved)
  -- the renamed state variables, read by their identity like a function
  let funRenames := funRenames ++ stateRenames
  let externalNames ← entryNames.mapM fun (id, original) => do
    let target := (lookupBy id functionAliases).getD id
    let some resolved := lookupBy target entryNames
      | throw s!"external override target #{target} of `{original}` is not imported"
    pure (id, resolved)
  let getterReads : List (Int × SolcFun × List String) := getterVariables.filterMap fun declarationNode => do
    let id ← J.id? declarationNode
    let name ← lookupBy id getterNames
    let scope : Source.ScopeScan := scanSource {
      entry := declarationNode
      evaluatedRoots := []
      declarationRoots := [declarationNode]
      constantIds := constants.map Prod.fst }
    let plan : Except Gap GetterPlan := do
      scope.ensure
      let raw := Json.mkObj [("nodeType", .str "Identifier"),
        ("name", .str ((J.str? declarationNode "name").getD "")),
        ("referencedDeclaration", Lean.toJson id)]
      let (root, rootState) ← (expr raw).run {
        declarations
        names := stateRenames
        dropped
        constants
        structs := S
        enumValues
        enumBounds
        enumNativeNames
        enumDecodeTypes
        compilerCode
        valueTypes }
      unless rootState.pre.isEmpty do
        throw (.unsupported "a public getter root requires deferred initialization" (J.line declarationNode))
      publicGetterPlan S declarations (generatedTaken ++ entryNames.map (·.2)) declarationNode root
    let identity := plan.bind (publicGetterIdentity declarationNode)
    let body := do
      let p ← plan
      let _ ← identity
      let result := if p.values.length == 1 then p.values.head! else
        s!"({", ".intercalate p.values})"
      pure ((p.guards ++ [s!"return {result}"]).map (J.line declarationNode, ·))
    let f : SolcFun := {
      name
      sourceName := (J.str? declarationNode "name").getD ""
      sourceDecl := identity.toOption
      sourceSignature := (identity.toOption.bind (·.signature)).getD ""
      sourceScope := scope
      line := J.line declarationNode
      tag := .internal
      params := (plan.toOption.map (·.params)).getD []
      rets := (plan.toOption.map (·.rets)).getD []
      body
      writingCall := false }
    pure (id, f, (plan.toOption.map (·.sourceParams)).getD [])
  -- Native extDispatch includes source getters. Their actual synthesized
  -- signatures must enter the same typed candidate/dependency closure;
  -- VariableDeclaration headers are not executable initializer roots.
  let dispatchCandidates := dispatchCandidates ++ getterReads.map fun (id, getter, _) =>
    FiniteDispatch.getterCandidate id getter
  let dispatchMissingIds := dispatchMissingIds || getterVariables.any (fun v => (J.id? v).isNone)
  let dispatchOf (root : Json) : FiniteDispatch.Result :=
    if dispatchMissingIds then { unresolved := unresolvedValueCalls declarations root }
    else FiniteDispatch.inspect declarations dispatchCandidates functionAliases root
  let getterGaps := getterReads.filterMap fun (id, f, _) =>
    match f.body with | .error gap => some (id, gap) | .ok _ => none
  let getterGaps := getterGaps ++ functionAliases.filterMap fun (id, target) =>
    (lookupBy target getterGaps).map (id, ·)
  let selectorHelperIds := (J.nodes ast).filterMap fun node => do
    guard (J.kind node == "MemberAccess" && J.str? node "memberName" == some "selector")
    let target ← J.opt node "expression"
    guard (J.kind target == "MemberAccess")
    let receiver ← J.opt target "expression"
    guard (!(J.kind receiver == "Identifier" && J.ref? receiver == some (-28)))
    guard (!((J.ref? receiver).bind fun id => declarations.find? (J.id? · == some id)).any
      (J.kind · == "ContractDefinition"))
    J.ref? target
  let selectorHelpers : List (Int × String) := Id.run do
    let localAliases := (funs ++ nodes.filter (J.kind · == "ModifierDefinition")).flatMap fun d =>
      (renames stateVars d).map (·.2)
    let mut taken := generatedTaken ++ externalNames.map (·.2) ++ funRenames.map (·.2) ++ localAliases
    let mut out := []
    for d in declarations do
      if !(["FunctionDefinition", "VariableDeclaration"].contains (J.kind d)) ||
          (J.str? d "functionSelector").isNone then continue
      let some id := J.id? d | continue
      if !selectorHelperIds.contains id then continue
      let mut name := s!"solcMetadataSelector{id}"
      for _ in [:taken.length + 1] do
        if !taken.contains name then break
        name := name ++ "_"
      taken := name :: taken
      out := out ++ [(id, name)]
    return out
  let selectorMembers := selectorHelpers.filterMap fun (id, name) => do
    let d ← declarations.find? (J.id? · == some id)
    let value ← (declarationSelector d "functionSelector" 4).toOption
    pure (name, s!"function {name}(address solcReceiver) returns (bytes4) \{ return {value.val}; }")
  let funParams : List (Int × List String) := funs.filterMap fun f => do
    let i ← J.id? f
    let ps ← (f.getObjVal? "parameters").toOption
    let ps ← (ps.getObjVal? "parameters").toOption
    let ps ← ps.getArr?.toOption
    pure (i, ps.toList.filterMap fun p => J.str? p "name")
  let funParams := funParams ++ getterReads.map fun (id, _, names) => (id, names)
  -- a constructor's `B(5)` is a base constructor's arguments, not a modifier
  let modifierInvocations (f : Json) : List Json :=
    J.arrD f "modifiers" |>.toList.filter (J.str? · "kind" != some "baseConstructorSpecifier")
  let modifierId (m : Json) : Option Int := do
    let name ← J.opt m "modifierName"
    let id ← J.ref? name
    let text := (J.str? name "name").getD ""
    if text.startsWith "super." then none
    else if text.contains '.' then some id
    else some ((lookupBy id modifierAliases).getD id)
  let localModifierDefs := nodes.filter (J.kind · == "ModifierDefinition")
  let invokedModifiers := funs.flatMap fun f => (modifierInvocations f).filterMap modifierId
  let modifierDefs := localModifierDefs ++ (J.nodes ast).filter fun d =>
    J.kind d == "ModifierDefinition" &&
      !(localModifierDefs.any (J.id? · == J.id? d)) && (J.id? d).any invokedModifiers.contains
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
  -- A declaration's specification scope: lexical visibility belongs to the
  -- defining contract and its ancestors, rather than the most-derived
  -- contract that executes it.
  let storageTuples := if lineage.length != 1 then [] else funs.filterMap fun f => do
    let id ← J.id? f
    let plan ← storageTuplePlan? S f
    let references := (J.nodes ast).filter fun node =>
      ["Identifier", "MemberAccess"].contains (J.kind node) && J.ref? node == some id
    let allowed := (J.nodes ast).filterMap fun node => do
      guard (J.kind node == "VariableDeclarationStatement")
      let value ← J.opt node "initialValue"
      guard (J.kind value == "FunctionCall")
      let head ← J.opt value "expression"
      guard (J.kind head == "Identifier" && J.ref? head == some id)
      let targets ← J.arr? node "declarations"
      guard (targets.size == plan.types.length)
      pure head
    guard (references.length == allowed.length)
    pure (id, plan)
  let specState (d : Json) (names : List (Int × String)) : PState :=
    let scopeNodes := scopeNodesOf d
    let (specConstants, scopeConstBlocked) :=
      specConstantScope units scopeNodes (declarationOwner units d)
    let localNames := J.varDeclNames (J.nodes d)
    { declarations, storageTuples, compilerCode,
      returnStorageIndex := ((J.id? d).bind (lookupBy · storageTuples)).map (·.index),
      selectorHelpers, externalNames, getterGaps, names, staticNames, baseContracts, superNames := superNamesOf d, dropped, structs := S,
      funParams, constants, enumValues, enumBounds, enumNativeNames, enumDecodeTypes, valueTypes, freeFunctions, libraries,
      specEnums := specEnumValues units scopeNodes enumDefs,
      specBlocked := J.varDeclNames scopeNodes ++ localNames, specConstants,
      sourceStateNames := J.varDeclNames scopeNodes, sourceModelNames := stateVars, scanLoop,
      specConstBlocked := scopeConstBlocked ++ localNames, specLocals := specBodyBindings d names,
      rewriteLoop }
  let modifierReadResults : List (Int × Except Gap (String × Source.ScopeScan)) := modifierDefs.filterMap fun m =>
    (J.id? m).map fun id => (id, do
      let st := specState m (renames stateVars m ++ funRenames)
      let (text, finalState) ← (do
        unless (J.nodes m).any (J.kind · == "PlaceholderStatement") do
          unsupported "a modifier without a placeholder"
        let ps ← PM.lift (J.get m "parameters")
        let ps ← (← PM.lift (J.arr ps "parameters")).zipIdx.mapM fun ((p, index) : Json × Nat) => do
          let t ← PM.lift (tyText S (← PM.lift (J.get p "typeName")))
          -- a reference parameter at its location, as a function's
          let loc := match J.opt p "storageLocation" with
            | some (.str "memory") => " memory"
            | some (.str "storage") => " storage"
            | some (.str "calldata") => " calldata"
            | _ => ""
          unless (PrimTy.ofName? t).isSome || (narrowTy? t).isSome || (bytesTy? t).isSome ||
              t == "address payable" ||
              loc == " memory" || loc == " storage" do
            unsupported s!"a modifier parameter of unsupported type `{t}{loc}`"
          let t := t ++ loc
          let n ← nameOf p
          let n := if !n.isEmpty then n else Id.run do
            let taken := stateVars ++ J.varDeclNames (J.nodes m)
            let mut name := s!"solcModArg{id}_{index}"
            for _ in [:taken.length + 1] do
              if !taken.contains name then return name
              name := name ++ "_"
            return name
          pure s!"{t} {identText n}"
        let b ← block (← PM.lift (J.get m "body"))
        pure s!"modifier solcModifier{id}({", ".intercalate ps}) {b}").run st
      pure (text, finalState.sourceScope))
  let modifierReads := modifierReadResults.map fun (id, result) => (id, result.map (·.1))
  let modifierScopes := modifierReadResults.map fun (id, result) =>
    (id, (result.toOption.map (·.2)).getD default)
  let modifierMembers := modifierReads.filterMap fun (_, text) => text.toOption
  let read := funs.map fun f =>
    let fname := internalName f
    let st := specState f (renames stateVars f ++ funRenames)
    let rawSpec := (keyClauses (docText f)).toOption.getD []
    let resolvedSpec := rawSpec.map fun c =>
      let text := resolveSpecConstants st.specConstants st.specConstBlocked c.text
      { c with text := resolveSpecEnums st.specEnums st.specBlocked text }
    -- Only parameters and named returns are in a function clause's scope.
    -- Renamed body locals cannot change the meaning of a pre/postcondition.
    let bindingsOf (key : String) :=
      ((J.opt f key).bind (J.arr? · "parameters")).getD #[] |>.toList
    let parameters := bindingsOf "parameters"
    let specRenamesOf (bindings : List Json) := bindings.filterMap fun p => do
      let id ← J.id? p
      let original ← J.str? p "name"
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
      -- `receive` and `fallback` are functions of their kind's name: an
      -- obligation each, and no other function can call them by name
      if !["function", "freeFunction", "constructor", "receive", "fallback"].contains kind then
        some s!"a `{kind}` function"
      else if fname == "report" then some "named like the import's `report` table"
      else none
    let apps : Except Gap String := do
      let apps ← (modifierInvocations f).mapM fun m => do
        let some id := modifierId m | throw (.unsupported "a modifier without a declaration identity" (J.line f))
        let some declared := lookupBy id modifierReads
          | throw (.unsupported "a modifier outside the imported contract" (J.line f))
        let _ ← declared
        let args := J.arrD m "arguments"
        let (args, _) ← (args.toList.mapM expr).run st
        pure s!" solcModifier{id}({", ".intercalate args})"
      pure (String.join apps)
    let ps : Except Gap (List (String × String)) := (do
      let pl ← J.get f "parameters"
      (← J.arr pl "parameters").mapM fun p => do
        let type ← J.get p "typeName"
        let abiFacing := kind == "constructor" ||
          [some "public", some "external"].contains (J.str? f "visibility")
        let enumComposite := (J.nodes type).any fun node =>
          ((J.ref? node).orElse fun _ => (J.opt node "pathNode").bind J.ref?).any enumDecodeTypes.contains
        let directEnum := (J.ref? type).any fun id => (lookupBy id enumBounds).isSome
        let enumArray := J.kind type == "ArrayTypeName" &&
          [some "memory", some "calldata"].contains (J.str? p "storageLocation") &&
          ((J.opt type "baseType").bind J.ref?).any fun id => (lookupBy id enumBounds).isSome
        if abiFacing && enumComposite && !directEnum && !enumArray then
          throw (.unsupported "an ABI composite parameter requires recursive enum cardinality checks" (J.line p))
        let ((t, x), _) ← (do
          let t ← PM.lift (tyText S type)
          let loc := match J.opt p "storageLocation" with
            | some (.str "memory") => " memory"
            | some (.str "storage") => " storage"
            | some (.str "calldata") => " calldata"
            | _ => ""
          pure (t ++ loc, ← nameOf p) : PM (String × String)).run st
        pure (x, t))
    let rs : Except Gap (List (String × String)) := do
      let some pl := J.opt f "returnParameters" | pure []
      let sourceReturns ← J.arr pl "parameters"
      let sourceReturns := match (J.id? f).bind (lookupBy · storageTuples) with
        | some plan => (sourceReturns[plan.index]?).toList
        | none => sourceReturns
      sourceReturns.mapM fun p => do
        let ((t, x), _) ← (do
            let t ← PM.lift (tyText S (← PM.lift (J.get p "typeName")))
            let loc := match J.opt p "storageLocation" with
              | some (.str "memory") => " memory"
              | some (.str "storage") => " storage"
              | _ => ""
            pure (t ++ loc, ← nameOf p) : PM (String × String)).run st
        pure (x, t)
    let tag := tagOf cspec f
    let modifierRoots := (modifierInvocations f).flatMap fun invocation =>
      ((modifierId invocation).bind fun id => modifierDefs.find? (J.id? · == some id)).toList
    let lexicalStateNames := J.varDeclNames (scopeNodesOf f)
    let functionClauses := fspec.filterMap fun clause =>
      if ["requires", "ensures", "invariant", "assignable"].contains clause.kind then
        let bindings := parameters ++ if clause.kind == "ensures" then bindingsOf "returnParameters" else []
        let bound := lexicalStateNames ++ J.varDeclNames bindings ++ (specRenamesOf bindings).map (·.2)
        some (bound, s!"{clause.kind} {clause.text};")
      else none
    let contractClauses := cspec.filterMap fun clause =>
      if ["requires", "ensures", "invariant", "assignable"].contains clause.kind then
        some (clause.lexicalNames, s!"{clause.kind} {clause.text};") else none
    let sourceScope := scanSource {
      entry := f
      evaluatedRoots := f :: modifierRoots
      declarationRoots := [c]
      constantIds := constants.map Prod.fst
      specifications := if testing then contractClauses ++ functionClauses else []
      modelBindings := stateVars ++ J.varDeclNames (parameters ++ bindingsOf "returnParameters") ++
        (specRenamesOf (parameters ++ bindingsOf "returnParameters")).map (·.2)
      unresolvedDispatch := (f :: modifierRoots).flatMap fun root => (dispatchOf root).unresolved
      diagnostics := paymentIssues f ++ (modifierInvocations f).flatMap (fun invocation =>
        ((modifierId invocation).bind fun id => modifierDefs.find? (J.id? · == some id)).toList.flatMap paymentIssues) }
    let sourceScope := (modifierRoots.foldl (fun scan root =>
      scan.append (((J.id? root).bind (lookupBy · modifierScopes)).getD default)) sourceScope).normalize
    let selection := if (J.id? f).any (fun id => (lookupBy id functionAliases).getD id == id)
      then SourceSelection.selected else .retained
    let identity := sourceFunction declarations f selection ((J.id? f).any freeFunctions.contains)
    let bodyRead : Except Gap (List (Nat × String) × Source.ScopeScan) := do
      sourceScope.ensure
      let _ ← identity
      if let .error m := tag then throw (.unsupported s!"its NatSpec: {m}" (J.line f))
      if testing && rawSpec.any ledgerAssignable then
        throw (.unsupported "ledger locations in assignable clauses are not modelled" (J.line f))
      if testing then
        if let .error reason := fspecResult then
          throw (.unsupported reason (J.line f))
      if testing then
        if let some (name, gap) := droppedNames.find? fun (name, _) =>
            !(parameters.any fun p => J.str? p "name" == some name) &&
              resolvedSpec.any fun clause => specReadsName name (specTokens clause.text) then
          throw (.unsupported s!"its specification reads omitted state variable `{name}`: {gap.msg}" (J.line f))
      if testing && ((keyClauses (docText f)).toOption.getD []).any (·.kind == "invariant") then
        throw (.unsupported "function-level invariant: put invariants on the contract" (J.line f))
      if let some m := refused then throw (.unsupported m (J.line f))
      let _ ← apps
      let b ← J.get f "body"
      let (ss, finalState) ← ((← J.arr b "statements").flatMapM fun s => do
        pure ((← stmt s).map (J.line s, ·))).run st
      pure (ss, finalState.sourceScope)
    let sourceScope := (sourceScope.append ((bodyRead.toOption.map (·.2)).getD default)).normalize
    let body : Except Gap (List (Nat × String)) := do
      sourceScope.ensure
      pure (← bodyRead).1
    let sourceParams := ((J.opt f "parameters").bind (J.arr? · "parameters")).getD #[]
    let sourceTypes := sourceParams.toList.map fun p => sourceType (J.tyStr p)
    { name := fname, sourceName := nameOfFun f,
      sourceDecl := identity.toOption, sourceScope,
      sourceSignature := s!"{nameOfFun f}({",".intercalate sourceTypes})",
      modifierApps := apps.toOption.getD "",
      line := J.line f, tag := (tag.toOption).getD .malformed,
      params := (ps.toOption).getD [], rets := (rs.toOption).getD [],
      payable := J.str? f "stateMutability" == some "payable",
      writingCall := writingCall f || (dispatchOf f).external || (modifierInvocations f).any fun m =>
        ((modifierId m).bind fun id => modifierDefs.find? (J.id? · == some id)).all fun root =>
          writingCall root || (dispatchOf root).external,
      paramRanges := ((ps.toOption).getD []).zip sourceParams.toList |>.filterMap fun ((x, t), p) => do
        if let some n := ((J.opt p "typeName").bind J.ref?).bind (lookupBy · enumBounds) then
          return (x, 0, n)
        -- a `bytesN` is a `uint` of `8N` bits (`valueRows?`)
        let (q, n) ← (narrowTy? t).orElse fun _ =>
          (bytesTy? t).map fun n => (.uint, 8 * n)
        guard (n < 256)
        if q == .int then pure (x, -(2 ^ (n - 1) : Int), 2 ^ (n - 1) - 1) else pure (x, 0, 2 ^ n - 1),
      -- a memory array of a narrow integer or an enum: each element in its range
      elemRanges := ((ps.toOption).getD []).zip sourceParams.toList |>.filterMap fun ((x, _), p) => do
        let t ← J.opt p "typeName"
        -- `bytes`/`string`: a `bytes1[]`, each element below `2^8`
        let mem := J.str? p "storageLocation" == some "memory" ||
          J.str? p "storageLocation" == some "calldata"
        if J.kind t == "ElementaryTypeName" && mem &&
            dynBytesTy ((J.str? t "name").getD "") then
          return (x, 0, 255, none)
        guard (J.kind t == "ArrayTypeName" && mem)
        let b ← J.opt t "baseType"
        let len : Option Nat := (J.opt t "length").bind fun l =>
          (solcArrayLength? t).orElse fun _ => (J.str? l "value").bind String.toNat?
        guard ((J.opt t "length").isNone || len.isSome)
        if let some n := (J.ref? b).bind (lookupBy · enumBounds) then
          return (x, 0, n, len)
        let (q, n) ← (narrowTy? ((J.str? b "name").getD "")).orElse fun _ =>
          (bytesTy? ((J.str? b "name").getD "")).map fun n => (.uint, 8 * n)
        guard (n < 256)
        if q == .int then pure (x, -(2 ^ (n - 1) : Int), 2 ^ (n - 1) - 1, len)
        else pure (x, 0, 2 ^ n - 1, len),
      specMembers := if testing then String.join (fspec
        |>.filter (fun c => ["requires", "ensures", "invariant", "assignable"].contains c.kind)
        |>.map (fun c => s!"{c.kind} {c.text}; ")) else "",
      specClauses := if testing then fspec
        |>.filter (fun c => ["requires", "ensures", "invariant", "assignable"].contains c.kind)
        |>.map (fun c => (c.kind, c.text)) else [],
      body := do let _ ← ps; let _ ← rs; body : SolcFun }
  -- the initializers, each printed against the variables kept, as the
  -- right-hand side of an assignment the constructor runs first
  let initSt : PState := { declarations, compilerCode, enumNativeNames, enumDecodeTypes, selectorHelpers, externalNames, getterGaps, names := funRenames, staticNames, baseContracts, dropped, structs := S, funParams, constants, enumValues, enumBounds, valueTypes, freeFunctions, libraries }
  let omittedInitializers := vars.filter fun v =>
    J.opt v "constant" != some (.bool true) &&
      !(J.id? v).any fixedIds.contains && (J.opt v "value").isSome &&
      !(kept.any fun (_, _, declaration) => declaration == v)
  let deploymentRoots := kept.map (·.2.2) ++ omittedInitializers
  let initScope := scanSource {
    entry := c, evaluatedRoots := deploymentRoots, declarationRoots := [c]
    constantIds := constants.map Prod.fst
    unresolvedDispatch := deploymentRoots.flatMap fun node => (dispatchOf node).unresolved
    diagnostics := deploymentRoots.flatMap paymentIssues }
  -- Each initializer is rendered once; viaIR inheritance places its
  -- assignment in its owner's construction phase instead of the field header.
  let initRows : Except Gap (List (Json × String × Option String)) := do
    initScope.ensure
    if let some v := omittedInitializers.head? then
      throw (.unsupported s!"the initializer of `{(J.str? v "name").getD "?"}` cannot be omitted: \
        its state declaration has no supported deployment root" (J.line v))
    renderInitializers kept initSt staticConstants immutables fixedBefore superNamesOf phasedInits
  let inits := initRows.map fun rows => rows.map (·.2.1)
  -- the internal calls: a function is read with every function it reaches,
  -- and the ones called are the contract's members, callees first
  let ids := funs.filterMap J.id? ++ getterReads.map (·.1)
  -- an initializer's calls are the constructor's, declared or implicit
  let initCalls : List Int := ((kept.filterMap fun (_, _, v) => (J.opt v "value").map (fun e => callees ids e freeFunctions functionAliases baseContracts (supersOf v) (getterNames.map (·.1))))
    |>.flatten) ++ (kept.flatMap fun (_, _, node) => (dispatchOf node).targets) ++
    (if kept.any (nativePayment ∘ (·.2.2)) then ownReceive.toList.filterMap J.id? else []) |>.eraseDups
  let ctorId : Option Int := (funs.find? (kindOf · == "constructor")).bind J.id?
  let receiveId := (ownNodes.find? fun n =>
    J.kind n == "FunctionDefinition" && kindOf n == "receive").bind J.id?
  let pays := nativePayment
  let callsOf : List (Int × List Int) := funs.filterMap fun f => (J.id? f).map fun i =>
    let modCalls := (modifierInvocations f).flatMap fun invocation =>
      ((modifierId invocation).bind fun id => modifierDefs.find? (J.id? · == some id))
        |>.toList.flatMap (fun m =>
          callees ids m freeFunctions functionAliases baseContracts (supersOf m) (getterNames.map (·.1)) ++ (dispatchOf m).targets)
    let receives := if pays f || (modifierInvocations f).any (fun invocation =>
      ((modifierId invocation).bind fun id => modifierDefs.find? (J.id? · == some id)).any pays)
      then receiveId.toList else []
    (i, (callees ids f freeFunctions functionAliases baseContracts (supersOf f) (getterNames.map (·.1)) ++
      (dispatchOf f).targets ++ modCalls ++
      receives ++ (if ctorId == some i then initCalls else [])).eraseDups)
  let callsOf := callsOf ++ getterReads.map fun (id, _, _) => (id, [])
  -- function values (`fnDispatch`): a function named as a value comes before
  -- the function naming it, and before every function that calls through a
  -- value (a variable of a function type), whose dispatch inlines it
  let varIds : List Int := (J.nodes c).filterMap fun n =>
    if J.kind n == "VariableDeclaration" then J.id? n else none
  let heads (f : Json) : List Int := (executableNodes declarations f).filterMap fun n =>
    if J.kind n == "FunctionCall" then (J.opt n "expression").bind J.ref? else none
  -- `this.g` named as an external value too (`extDispatch` runs `g` when
  -- declared before the caller)
  let refs (f : Json) : List Int := (executableNodes declarations f).filterMap fun n =>
    if J.kind n == "Identifier" || J.kind n == "MemberAccess" then do
      let id ← (J.ref? n).filter ids.contains
      -- A bare public variable is storage, not its external getter value.
      guard (!(getterNames.any (·.1 == id)) || isExternalMember n)
      pure id
    else none
  -- named more often than called: named as a value
  let valuesOf (f : Json) : List Int :=
    let hs := heads f
    let rs := refs f
    rs.eraseDups.filter fun r => rs.count r > hs.count r
  let callsValue (f : Json) : Bool := (J.nodes f).any fun n =>
    J.kind n == "FunctionCall" && J.str? n "kind" == some "functionCall" &&
      (J.opt n "expression").any fun e =>
        (J.kind e == "Identifier" && (J.ref? e).any varIds.contains) || isValueCallee e
  -- once per function: its values, and whether it calls through one
  let valueRows : List (Int × List Int × Bool) := funs.filterMap fun f =>
    (J.id? f).map fun i => (i, valuesOf f, callsValue f)
  let taken : List Int := (valueRows.flatMap (·.2.1)).eraseDups
  let callsOf : List (Int × List Int) := callsOf.map fun (i, cs) =>
    match lookupBy i valueRows with
    | some (vs, cv) => (i, (cs ++ vs ++ (if cv then taken.filter (· != i) else [])).eraseDups)
    | none => (i, cs)
  let calls (i : Int) : List Int := (lookupBy i callsOf).getD []
  -- A shared runtime callee may already contain folded immutable reads.
  -- Refuse a call needing a not-yet-initialized immutable rather than clone
  -- its body or substitute the final value during deployment.
  let initForwardGap : Option Gap := if fixedIds.isEmpty then none else
    kept.findSome? fun (_, _, v) => do
      let _ ← J.opt v "value"
      let future := fixedIds.filter fun id => !(fixedBefore v).contains id
      if future.isEmpty then none else do
        let targets := callees ids v freeFunctions functionAliases baseContracts (supersOf v)
          (getterNames.map (·.1)) ++ (dispatchOf v).targets
        let reached := targets.flatMap fun id =>
          (reach calls (ids.length + 1) [] [] id).toOption.getD []
        let bad ← reached.findSome? fun id =>
          if (getterNames.any (·.1 == id)) && future.contains id then some id else do
            let f ← funs.find? (J.id? · == some id)
            let modifiers := (modifierInvocations f).filterMap fun app =>
              (modifierId app).bind fun key => modifierDefs.find? (J.id? · == some key)
            ((f :: modifiers).flatMap J.nodes).findSome? fun node => do
              guard (["Identifier", "MemberAccess"].contains (J.kind node))
              let ref ← J.ref? node
              guard (future.contains ref)
              pure ref
        pure (.unsupported s!"the initializer of `{(J.str? v "name").getD "?"}` reaches immutable \
          declaration #{bad} before initialization through a shared runtime callee" (J.line v))
  let byId : List (Int × SolcFun) := ((funs.zip read).filterMap fun (f, r) => (J.id? f).map (·, r)) ++
    getterReads.map fun (id, f, _) => (id, f)
  let nameAt (i : Int) : String := ((lookupBy i byId).map (·.name)).getD "?"
  let withCalls (i : Int) (r : SolcFun) : SolcFun :=
    let cs := ((reach calls (ids.length + 1) [] [] i).toOption.getD []).dropLast
    let sourceScope := (cs.foldl (fun scan id =>
      match lookupBy id byId with
      | some f => scan.append f.sourceScope
      | none => scan) r.sourceScope).normalize
    let body : Except Gap (List (Nat × String)) := do
      sourceScope.ensure
      let ss ← r.body
      match reach calls (ids.length + 1) [] [] i with
      | .error g => throw (.unsupported s!"the calls from `{nameAt g}` are nested past the \
          number of functions" r.line)
      | .ok order =>
        for c in order.dropLast do
          if let some { body := .error g, .. } := lookupBy c byId then
            throw (match g with
              | .excluded m _ => .excluded s!"it calls `{nameAt c}`, which is left out: {m}" r.line
              | .unsupported m _ => .unsupported s!"it calls `{nameAt c}`, which is left out: {m}" r.line)
        pure ss
    let writes := r.writingCall || cs.any fun c => (lookupBy c byId).all (·.writingCall)
    { r with body, sourceScope, calls := cs.map nameAt, writingCall := writes }
  let closed : List (Int × SolcFun) := byId.map fun (i, r) => (i, withCalls i r)
  let initScope := (initCalls.foldl (fun scan id =>
    scan.append (((lookupBy id closed).map (·.sourceScope)).getD default)) initScope).normalize
  let order := ids.foldl (fun done i => (reach calls (ids.length + 1) [] done i).toOption.getD done) []
  -- Base constructors, as solc's legacy creation code runs them
  -- (`ContractCompiler::appendInitAndConstructorCode`): every initializer,
  -- most base first (`initMembers`' declarations); then the most-derived
  -- constructor, which evaluates the next base constructor's arguments and
  -- runs it first, and so on down the C3 order.  So: every argument, derived
  -- to base, bound to its base constructor's parameter as a local, then the
  -- bodies, base to derived, all in the one constructor member. viaIR
  -- instead interleaves initializers below; both retain shared callee bodies.
  let ctorNodeOf (k : Json) : Option Json := (membersOf k).find? fun n =>
    J.kind n == "FunctionDefinition" && J.str? n "kind" == some "constructor"
  let baseCtors : List (Json × Json) := lineage.tail.filterMap fun k => (ctorNodeOf k).map (k, ·)
  let ownCtor := ctorNodeOf c
  let paramsOf (f : Json) : List Json :=
    ((J.opt f "parameters").bind (J.arr? · "parameters")).getD #[] |>.toList
  let localNames (f : Json) : List String := J.varDeclNames (J.nodes f)
  let ownCtorNames : List (Int × String) := (ownCtor.map (renames stateVars)).getD []
  -- every constructor's locals renamed apart: they share one body
  let ctorNames : List (Int × List (Int × String)) := Id.run do
    let mut chosen : List String := (ownCtor.map localNames).getD [] ++ ownCtorNames.map (·.2)
    let mut out := (ownCtor.bind J.id?).toList.map (·, ownCtorNames)
    for (_, f) in baseCtors do
      let others := (baseCtors.filter fun (_, g) => J.id? g != J.id? f).flatMap (localNames ·.2)
      let ns := renames (stateVars ++ chosen ++ others) f
      -- an unnamed parameter's argument is still evaluated
      let unnamed := (paramsOf f).zipIdx.filterMap fun (p, i) => do
        guard ((J.str? p "name").getD "" == "")
        pure ((← J.id? p), s!"solcCtorArg{(J.id? f).getD 0}_{i}")
      let ns := ns ++ unnamed
      chosen := chosen ++ localNames f ++ ns.map (·.2)
      out := out ++ (J.id? f).toList.map (·, ns)
    return out
  let ctorState (f : Json) : PState :=
    specState f ((((J.id? f).bind (lookupBy · ctorNames)).getD []) ++ funRenames)
  -- the arguments of `k`'s constructor, as solc takes them: from the first
  -- contract in the C3 order (most derived first) that gives them, in its
  -- constructor's header (`B(a)`, in that constructor's scope) or in its
  -- inheritance specifier (`is B(5)`); with the node that holds them
  let ctorArgs (k : Json) : Option (PState × List Json × Json) :=
    lineage.findSome? fun p =>
      let viaHeader := (ctorNodeOf p).bind fun pc => (J.arrD pc "modifiers").toList.findSome? fun m => do
        guard (J.str? m "kind" == some "baseConstructorSpecifier")
        guard ((J.opt m "modifierName").bind J.ref? == J.id? k)
        pure (ctorState pc, ((J.arr? m "arguments").map (·.toList)).getD [], m)
      viaHeader <|> (J.arrD p "baseContracts").toList.findSome? fun b => do
        guard ((J.opt b "baseName").bind J.ref? == J.id? k)
        let args ← J.arr? b "arguments"
        pure (initSt, args.toList, b)
  let compositeCalls : List Int := (baseCtors.flatMap fun (k, f) =>
      callees ids f freeFunctions functionAliases baseContracts (supersOf f) (getterNames.map (·.1)) ++ (dispatchOf f).targets ++
        (modifierInvocations f).flatMap (fun invocation =>
          ((modifierId invocation).bind fun id => modifierDefs.find? (J.id? · == some id)).toList.flatMap
            (fun m => callees ids m freeFunctions functionAliases baseContracts (supersOf m) (getterNames.map (·.1)) ++
              (dispatchOf m).targets)) ++
        (((ctorArgs k).map fun (_, _, node) =>
          callees ids node freeFunctions functionAliases baseContracts [] (getterNames.map (·.1)) ++ (dispatchOf node).targets).getD [])).eraseDups
  let compositeReach : List Int := (compositeCalls.flatMap fun i =>
    (reach calls (ids.length + 1) [] [] i).toOption.getD []).eraseDups
  let compositeRoots := (baseCtors.map (·.2) ++ ownCtor.toList) ++
    (baseCtors.flatMap fun (k, _) => ((ctorArgs k).map (·.2.2)).toList) ++
    ((baseCtors.map (·.2) ++ ownCtor.toList).flatMap fun f =>
      (modifierInvocations f).flatMap fun invocation =>
        ((modifierId invocation).bind fun id => modifierDefs.find? (J.id? · == some id)).toList)
  let compositeScope := (compositeReach.foldl (fun scan id =>
      match lookupBy id byId with
      | some f => scan.append f.sourceScope
      | none => scan) (initScope.append (scanSource {
        entry := c, evaluatedRoots := compositeRoots, declarationRoots := [c]
        constantIds := constants.map Prod.fst
        unresolvedDispatch := compositeRoots.flatMap fun root => (dispatchOf root).unresolved
        diagnostics := compositeRoots.flatMap paymentIssues }))).normalize
  let compositeScope := (compositeRoots.foldl (fun scan root =>
    scan.append (((J.id? root).bind (lookupBy · modifierScopes)).getD default)) compositeScope).normalize
  -- a constructor body with modifiers, or a base one with a `return`, as a
  -- member of its own (`solcCtorBody<id>`) that the composite calls with its
  -- parameters: its modifiers wrap its body alone, after the base
  -- constructors ran, and a `return` ends it alone, as in solc
  let bodyMember? (f : Json) : Bool :=
    !(modifierInvocations f).isEmpty ||
      (ownCtor.bind J.id? != J.id? f && (J.nodes f).any (J.kind · == "Return"))
  let ctorBodyNames : List (Int × String) := Id.run do
    let mut taken := generatedTaken ++ externalNames.map (·.2) ++ selectorHelpers.map (·.2) ++
      ctorNames.flatMap (fun (_, names) => names.map (·.2))
    let mut out := []
    for f in baseCtors.reverse.map (·.2) ++ ownCtor.toList do
      if !bodyMember? f then continue
      let some id := J.id? f | continue
      let name := freshSourceName taken s!"solcCtorBody{id}"
      taken := name :: taken
      out := out ++ [(id, name)]
    return out
  let compositeBody : Except Gap (List (Nat × String) × List (String × String) × Source.ScopeScan) := do
    compositeScope.ensure
    for i in compositeCalls do
      match reach calls (ids.length + 1) [] [] i with
      | .error g => throw (.unsupported s!"the call of `{nameAt g}` is recursive: \
          a call is inlined, and the inlining would not end" (J.line c))
      | .ok order =>
        for x in order do
          if let some { body := .error g, .. } := lookupBy x byId then
            throw (match g with
              | .excluded m _ => .excluded s!"a base constructor calls `{nameAt x}`, which is left out: {m}"
              | .unsupported m _ =>
                .unsupported s!"a base constructor calls `{nameAt x}`, which is left out: {m}")
    let mut carry : Nat × Nat := (0, 0)
    let mut out : List (Nat × String) := []
    let mut loopScope : Source.ScopeScan := default
    let mut helpers : List (String × String) := []
    -- the arguments, derived to base
    for (k, f) in baseCtors do
      let baseName := (J.str? k "name").getD "?"
      unless ((keyClauses (docText f)).toOption.getD []).isEmpty do
        throw (.unsupported s!"base constructor `{baseName}`'s specification" (J.line f))
      let ps := paramsOf f
      if ps.isEmpty then continue
      let some (st, args, _) := ctorArgs k
        | throw (.unsupported s!"no arguments for base constructor `{baseName}`: \
            the contract is abstract" (J.line f))
      unless args.length == ps.length do
        throw (.unsupported s!"the arguments of base constructor `{baseName}`" (J.line f))
      let names := ((J.id? f).bind (lookupBy · ctorNames)).getD []
      for (p, a) in ps.zip args do
        let (ss, st') ← (do
            let t ← PM.lift (tyText S (← PM.lift (J.get p "typeName")))
            let loc := match J.opt p "storageLocation" with
              | some (.str "memory") => " memory"
              | some (.str "storage") => " storage"
              | _ => ""
            let e ← expr a
            let pre := (← get).pre
            modify fun st => { st with pre := #[] }
            let n := ((J.id? p).bind (lookupBy · names)).getD ((J.str? p "name").getD "")
            pure (pre.toList ++ [s!"{t}{loc} {identText n} = {e}"]) : PM (List String)).run
          { st with fresh := carry.1, discards := carry.2 }
        carry := (st'.fresh, st'.discards)
        out := out ++ ss.map (J.line f, ·)
    -- viaIR evaluates constructor arguments first, then interleaves each
    -- owner's initializers with its constructor body, base to derived.
    for owner in lineage.reverse do
      if phasedInits then
        for (declaration, _, assignment) in ← initRows do
          if (membersOf owner).any (J.id? · == J.id? declaration) then
            if let some statement := assignment then
              out := out ++ [(J.line declaration, statement)]
      let some f := ctorNodeOf owner | continue
      let b ← J.get f "body"
      let st0 := { ctorState f with fresh := carry.1, discards := carry.2 }
      let (ss, st') ← ((← J.arr b "statements").flatMapM fun s => do
          pure ((← stmt s).map (J.line s, ·))).run st0
      loopScope := loopScope.append st'.sourceScope
      carry := (st'.fresh, st'.discards)
      if !bodyMember? f then
        out := out ++ ss
        continue
      -- its parameters, as the composite names them
      let names := ((J.id? f).bind (lookupBy · ctorNames)).getD []
      let ps ← (paramsOf f).mapM fun p => do
        let ((t, _), _) ← (do
            let t ← PM.lift (tyText S (← PM.lift (J.get p "typeName")))
            let loc := match J.opt p "storageLocation" with
              | some (.str "memory") => " memory"
              | some (.str "storage") => " storage"
              | _ => ""
            pure (t ++ loc, ()) : PM (String × Unit)).run st0
        pure (((J.id? p).bind (lookupBy · names)).getD ((J.str? p "name").getD ""), t)
      let (apps, _) ← ((modifierInvocations f).mapM fun m => do
          let some id := modifierId m
            | throw (.unsupported "a modifier without a declaration identity" (J.line f))
          let some declared := lookupBy id modifierReads
            | throw (.unsupported "a modifier outside the imported contract" (J.line f))
          let _ ← PM.lift declared
          let args ← (J.arrD m "arguments").toList.mapM expr
          pure s!" solcModifier{id}({", ".intercalate args})" : PM (List String)).run st0
      let some n := (J.id? f).bind (lookupBy · ctorBodyNames)
        | throw (.unsupported "a constructor body helper without declaration identity" (J.line f))
      let psText := ", ".intercalate (ps.map fun (x, t) => s!"{t} {identText x}")
      helpers := helpers ++ [(n, s!"function {n}({psText}){String.join apps} \{ \
        {String.join (ss.map (·.2 ++ "; "))}}")]
      out := out ++ [(J.line f, s!"{n}({", ".intercalate (ps.map (identText ∘ Prod.fst))})")]
    pure (out, helpers, loopScope)
  let called := (entryIds.flatMap fun i =>
    ((reach calls (ids.length + 1) [] [] i).toOption.getD []).dropLast) ++
    initCalls.flatMap (fun i => (reach calls (ids.length + 1) [] [] i).toOption.getD []) ++
    (if baseCtors.isEmpty && !phasedInits then [] else compositeReach)
  let funMembers := order.filterMap fun i => do
    let r ← lookupBy i closed
    guard (ctorId != some i && (called.contains i || (getterNames.any (·.1 == i)) ||
      (entryIds.contains i && (testing || !r.modifierApps.isEmpty))))
    let ss ← r.body.toOption
    pure (r.name, r.member (ss.map (·.2)))
  -- the constructor bodies the composite calls, after every function
  let ctorHelpers := if baseCtors.isEmpty && !phasedInits then [] else
    ((compositeBody.toOption.map (·.2.1)).getD [])
  let funMembers := selectorMembers ++ funMembers ++ ctorHelpers
  -- an initializer that does not print, or calls a function left out
  let initGap : Option Gap := match inits with
    | .error g => some g
    | .ok _ => initForwardGap.orElse fun _ => initCalls.findSome? fun c => match lookupBy c closed with
      | some { body := .error g, .. } =>
        let m := s!"an initializer calls `{nameAt c}`, which is left out: {g.msg}"
        some (match g with | .excluded .. => .excluded m | .unsupported .. => .unsupported m)
      | _ => none
  let initMembers := match initGap, inits with
    | none, .ok ms => invariants ++ enumMembers ++ structMembers ++ errorMembers.eraseDups ++ ms
    | _, _ => members
  let all := ((funs.zip read).filter fun (f, _) => (J.id? f).any entryIds.contains).map fun (f, r) =>
    (kindOf f == "constructor", ((J.id? f).map (withCalls · r)).getD r)
  let ctor := (all.find? (·.1)).map fun (_, r) =>
    { r with
      sourceScope := (r.sourceScope.append initScope).normalize
      writingCall := r.writingCall || kept.any (fun (_, _, node) => (dispatchOf node).external)
      body := do
        let ss ← r.body
        if let some g := initGap then throw g
        pure ss }
  let ctor := if baseCtors.isEmpty && !phasedInits then ctor else
    let own : SolcFun := ctor.getD
      { name := "constructor", sourceName := "constructor", sourceSignature := "constructor()",
        line := J.line c, tag := if isSpecified cspec then .specified else .diamond,
        params := [], body := do if let some g := initGap then throw g else pure [],
        writingCall := false }
    let sourceScope := (own.sourceScope.append compositeScope |>.append
      ((compositeBody.toOption.map (·.2.2)).getD default)).normalize
    some { own with
      sourceScope,
      body := do sourceScope.ensure; let _ ← own.body; pure (← compositeBody).1,
      -- its own modifiers wrap its body's member alone (`bodyMember?`)
      modifierApps := "",
      calls := (own.calls ++ compositeReach.map nameAt ++ ctorHelpers.map (·.1) ++
        (initCalls.flatMap fun i => (reach calls (ids.length + 1) [] [] i).toOption.getD []).map nameAt).eraseDups,
      writingCall := own.writingCall ||
        kept.any (fun (_, _, node) => writingCall node || (dispatchOf node).external) ||
        initCalls.any (fun id => (lookupBy id closed).all (·.writingCall)) || compositeRoots.any (fun root => (dispatchOf root).external) ||
        baseCtors.any (writingCall ·.2) ||
        compositeReach.any fun x => (lookupBy x byId).all (·.writingCall) }
  -- An implicit constructor must retain an initializer refusal in the report.
  -- A warning alone would let a replay deploy the default-only contract.
  let ctor := match ctor, initGap with
    | none, some gap => some {
        name := "constructor", sourceName := "constructor", sourceSignature := "constructor()",
        line := J.line c, tag := .diamond, params := [], sourceScope := initScope, body := .error gap }
    | _, _ => ctor
  let funs := all.filterMap fun (c, r) => if c then none else some r
  let internalFuns := selectorHelpers.map (·.2) ++ ctorHelpers.map (·.1)
  let sourceDecls := byId.filterMap fun (_, f) => f.sourceDecl.map (f.name, ·)
  let sourceDecls := sourceDecls ++ internalFuns.map fun name =>
    (name, ({ callable := .implementation } : SourceFunction))
  pure {
    name
    members
    dropped := droppedNames
    funs
    funMembers
    internalFuns
    sourceDecls
    modifierMembers
    ctor
    initMembers
    initGap }

end Solidity.Frontend
