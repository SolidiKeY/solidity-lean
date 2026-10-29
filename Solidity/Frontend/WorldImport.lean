import Solidity.Frontend.Import
import Solidity.Semantics.ContractWorldCertificates

/-!
# Source creation factories in the typed contract world

This frontend accepts a narrow, declaration-resolved source fragment: a
stateless, noninheriting factory method with no parameters or modifiers whose
whole body is either a direct creation return, or a creation try with bare
catch and literal Boolean returns. Constructor arguments and the value option
are literals. Every other shape fails explicitly. Target constructors are
imported by the existing frontend and must actually elaborate.

The generated namespace contains the imported source contracts, its typed
two-contract catalog, deployment of the implicit factory constructor, and run.
The fixture's content hash is checked before reading any source declaration.
This is not a general lowering of world effects inside arbitrary statements.
-/

namespace Solidity.Frontend

open Lean Elab Command
open Solidity.ContractWorld

namespace WorldCreation

structure Factory where
  owner : String
  target : String
  args : List String
  value : Nat
  payable : Bool
  branches : Option (Bool × Bool)
  ctorRequired : Bool
  payments : List Nat

def literal (j : Json) : Except String String := do
  unless J.kind j == "Literal" do throw "solidity.worldFactory.arguments: literal arguments required"
  if (J.str? j "subdenomination").any (· != "") then
    throw "solidity.worldFactory.arguments: denominated literals need a separate lowering"
  let value := (J.str? j "value").getD ""
  if J.str? j "kind" == some "bool" && ["true", "false"].contains value then return value
  unless J.str? j "kind" == some "number" && value.toNat?.isSome do
    throw "solidity.worldFactory.arguments: only decimal integer and Boolean literals"
  return value

private def declarationRef (j : Json) : Option Int :=
  J.ref? j <|> ((J.opt j "pathNode").bind J.ref?)

private def boolReturn (block : Json) : Except String Bool := do
  let [statement] := (J.arrD block "statements").toList
    | throw "solidity.worldFactory.catch: each branch must contain one Boolean return"
  unless J.kind statement == "Return" do
    throw "solidity.worldFactory.catch: each branch must contain one Boolean return"
  let some expression := J.opt statement "expression"
    | throw "solidity.worldFactory.catch: missing return value"
  let text ← literal expression
  if text == "true" then return true
  if text == "false" then return false
  throw "solidity.worldFactory.catch: a Boolean return is required"

/-- Only direct, bounded address casts of a decimal literal are admitted as
payment destinations by the closed-constructor source fragment. -/
private def paymentAddress : Nat → Json → Except String Nat
  | 0, _ => .error "solidity.worldFactory.constructor: address-cast nesting is unsupported"
  | fuel + 1, j => do
    if J.kind j == "Literal" then
      let text ← literal j
      let some n := text.toNat? | throw "solidity.worldFactory.constructor: numeric address required"
      unless n < 2 ^ 160 do throw "solidity.worldFactory.constructor: address must fit 160 bits"
      return n
    unless J.kind j == "FunctionCall" && J.str? j "kind" == some "typeConversion" do
      throw "solidity.worldFactory.constructor: literal address casts required for payments"
    let some callee := J.opt j "expression" | throw "solidity.worldFactory.constructor: missing address cast"
    let some ty := J.opt callee "typeName" | throw "solidity.worldFactory.constructor: address casts only"
    unless J.kind callee == "ElementaryTypeNameExpression" &&
        J.str? ty "name" == some "address" do
      throw "solidity.worldFactory.constructor: address casts only"
    let [argument] := (J.arrD j "arguments").toList
      | throw "solidity.worldFactory.constructor: one address-cast argument required"
    paymentAddress fuel argument

/-- Inspect a declaration for unsupported nested world effects. Ordinary
external calls cannot be replaced by the single-contract response table.
Transfers are admitted only with explicit no-code recipient premises. Transient
declarations use the imported contract certificate and ordinary typed roots;
callers select an outer transaction boundary for a complete composition. -/
private def inspectClosed (declarations : List Json) (node : Json) : Except String (List Nat) := do
  let mut payments : List Nat := []
  for n in J.nodes node do
    if J.kind n == "TryStatement" then
      throw "solidity.worldFactory.constructor: nested external try requires world-aware statements"
    if J.kind n == "NewExpression" then
      if (J.opt n "typeName").any (J.kind · == "UserDefinedTypeName") then
        throw "solidity.worldFactory.constructor: nested contract creation is not lowered"
    if J.kind n == "MemberAccess" && J.str? n "memberName" == some "balance" then
      throw "solidity.worldFactory.constructor: balance observations need the global world expression interface"
    if J.kind n != "FunctionCall" then continue
    let some callee := J.opt n "expression" | throw "solidity.worldFactory.constructor: missing callee"
    let typeId := ((J.opt callee "typeDescriptions").bind (J.str? · "typeIdentifier")).getD ""
    if ((J.tyStr callee).splitOn "external").length != 1 || typeId.startsWith "t_function_external" then
      throw "solidity.worldFactory.constructor: external contract/library calls need world-aware statements"
    if typeId.startsWith "t_function_internal" then
      let some ref := J.ref? callee
        | throw "solidity.worldFactory.constructor: function-valued calls are not lowered"
      unless declarations.any (fun d => J.kind d == "FunctionDefinition" && J.id? d == some ref) do
        throw "solidity.worldFactory.constructor: function-valued calls are not lowered"
    if J.str? n "kind" == some "functionCall" then
      match J.ref? callee with
      | some ref =>
        if 0 ≤ ref && !(declarations.any (fun d => J.kind d == "FunctionDefinition" && J.id? d == some ref)) then
          throw "solidity.worldFactory.constructor: indirect/non-function calls need separate lowering"
      | none =>
        let builtinMember := J.kind callee == "MemberAccess" &&
          [some "transfer", some "send", some "push", some "pop", some "encode", some "encodePacked",
            some "encodeWithSelector", some "encodeWithSignature", some "encodeCall", some "concat"].contains
              (J.str? callee "memberName")
        let memoryNew := J.kind callee == "NewExpression" &&
          (J.opt callee "typeName").any (J.kind · == "ArrayTypeName")
        unless builtinMember || memoryNew do
          throw "solidity.worldFactory.constructor: unresolved/function-valued calls are not lowered"
    if J.kind callee == "MemberAccess" &&
        [some "send", some "transfer"].contains (J.str? callee "memberName") then
      let some receiver := J.opt callee "expression"
        | throw "solidity.worldFactory.constructor: missing payment receiver"
      payments := (← paymentAddress 8 receiver) :: payments
  return payments

/-- A bounded worklist follows compiler declaration identities through base
contracts and internal/free callees. Every scanned declaration and reference
consumes the fixed source-sized budget; no runtime search is trusted. -/
private def closedPayments (ast target : Json) : Except String (List Nat) := do
  let declarations := (J.nodes ast).filter (fun n =>
    ["ContractDefinition", "FunctionDefinition"].contains (J.kind n))
  let budget := declarations.length + (declarations.map (fun n =>
    ((J.nodes n).filterMap J.ref?).length)).foldl (· + ·) 0 + 1
  let rec go : Nat → List Int → List Json → List Nat → Except String (List Nat)
    | 0, _, pending, payments =>
      if pending.isEmpty then .ok payments.eraseDups else
        .error "solidity.worldFactory.constructor: declaration inspection budget exhausted"
    | fuel + 1, seen, pending, payments => do
      match pending with
      | [] => return payments.eraseDups
      | node :: rest =>
        let some id := J.id? node | throw "solidity.worldFactory.constructor: missing declaration identity"
        if seen.contains id then go fuel seen rest payments else do
          let ownPayments ← inspectClosed declarations node
          let refs := (J.nodes node).filterMap J.ref?
          let next := refs.filterMap (fun id =>
            declarations.find? (fun d => J.id? d == some id))
          go fuel (id :: seen) (next ++ rest) (ownPayments ++ payments)
  go budget [] [target] []

/-- Extract only complete recognized factory bodies, never erase statements. -/
def read (ast : Json) (ownerName method : String) : Except String Factory := do
  let units := (J.arrD ast "nodes").toList
  let [owner] := units.filter (fun n => J.kind n == "ContractDefinition" &&
      J.str? n "name" == some ownerName)
    | throw "solidity.worldFactory.owner: expected one source contract"
  unless J.str? owner "contractKind" == some "contract" &&
      J.opt owner "abstract" == some (.bool false) && (J.arrD owner "baseContracts").isEmpty do
    throw "solidity.worldFactory.owner: only noninheriting concrete factories"
  let nodes := (J.arrD owner "nodes").toList
  if nodes.any (fun n => J.kind n == "VariableDeclaration" &&
      (J.str? n "storageLocation" == some "transient" || J.opt n "transient" == some (.bool true))) then
    throw "solidity.worldFactory.owner: transient state needs the shared world transaction interface"
  if nodes.any (fun n => J.kind n == "VariableDeclaration" ||
      (J.kind n == "FunctionDefinition" && J.str? n "kind" == some "constructor")) then
    throw "solidity.worldFactory.owner: factory must be stateless with its implicit constructor"
  let [f] := nodes.filter (fun n => J.kind n == "FunctionDefinition" && J.str? n "name" == some method)
    | throw "solidity.worldFactory.method: missing or overloaded method"
  unless [some "public", some "external"].contains (J.str? f "visibility") &&
      (J.arrD f "modifiers").isEmpty do
    throw "solidity.worldFactory.method: unmodified public/external method required"
  let some parameters := J.opt f "parameters" | throw "solidity.worldFactory.method: missing parameters"
  unless (J.arrD parameters "parameters").isEmpty do
    throw "solidity.worldFactory.arguments: factory parameters are not lowered yet"
  let some body := J.opt f "body" | throw "solidity.worldFactory.body: no body"
  let [statement] := (J.arrD body "statements").toList
    | throw "solidity.worldFactory.body: expected exactly one creation return or creation try"
  let (creation, branches) ← if J.kind statement == "Return" then do
      let some e := J.opt statement "expression" | throw "solidity.worldFactory.body: no return expression"
      pure (e, none)
    else if J.kind statement == "TryStatement" then do
      let some e := J.opt statement "externalCall" | throw "solidity.worldFactory.catch: no creation"
      let [success, caught] := (J.arrD statement "clauses").toList
        | throw "solidity.worldFactory.catch: exactly success and bare catch required"
      unless (J.str? caught "errorName").getD "" == "" &&
          ((J.opt caught "parameters").map (J.arrD · "parameters") |>.getD #[]).isEmpty do
        throw "solidity.worldFactory.catch: typed/data catches need separate lowering"
      let some okBlock := J.opt success "block" | throw "solidity.worldFactory.catch: no success block"
      let some errBlock := J.opt caught "block" | throw "solidity.worldFactory.catch: no catch block"
      pure (e, some (← boolReturn okBlock, ← boolReturn errBlock))
    else throw "solidity.worldFactory.body: expected creation return or creation try"
  unless J.kind creation == "FunctionCall" && (J.arrD creation "names").isEmpty do
    throw "solidity.worldFactory.creation: positional creation call required"
  let args ← (J.arrD creation "arguments").toList.mapM literal
  let some callee := J.opt creation "expression" | throw "solidity.worldFactory.creation: no callee"
  let (newExpression, value) ← if J.kind callee == "FunctionCallOptions" then do
      let names := (J.arrD callee "names").toList.filterMap (·.getStr?.toOption)
      let [option] := (J.arrD callee "options").toList
        | throw "solidity.worldFactory.options: only one value option is supported"
      unless names == ["value"] do
        throw "solidity.worldFactory.options: salt and gas are outside this lowering"
      let text ← literal option
      let some n := text.toNat? | throw "solidity.worldFactory.options: numeric value required"
      let some e := J.opt callee "expression" | throw "solidity.worldFactory.creation: no new expression"
      pure (e, n)
    else pure (callee, 0)
  unless J.kind newExpression == "NewExpression" do
    throw "solidity.worldFactory.creation: ordinary new C(args) required"
  let some targetType := J.opt newExpression "typeName" | throw "solidity.worldFactory.target: no type"
  let some targetId := declarationRef targetType | throw "solidity.worldFactory.target: unresolved declaration"
  let [target] := units.filter (fun n => J.kind n == "ContractDefinition" && J.id? n == some targetId)
    | throw "solidity.worldFactory.target: target must be in this source unit"
  let targetName := (J.str? target "name").getD ""
  unless J.str? target "contractKind" == some "contract" &&
      J.opt target "abstract" == some (.bool false) && targetName != ownerName do
    throw "solidity.worldFactory.target: distinct concrete target required"
  let some returns := J.opt f "returnParameters" | throw "solidity.worldFactory.result: missing returns"
  let [result] := (J.arrD returns "parameters").toList
    | throw "solidity.worldFactory.result: exactly one return value required"
  let some resultType := J.opt result "typeName" | throw "solidity.worldFactory.result: no return type"
  match branches with
  | none => unless declarationRef resultType == some targetId do
      throw "solidity.worldFactory.result: direct creation must return its target type"
  | some _ => unless J.str? resultType "name" == some "bool" do
      throw "solidity.worldFactory.result: creation try must return bool"
  let targetRead ← readContract ast targetName [] true
  let implicitSafe := (J.arrD target "baseContracts").isEmpty &&
    !((J.arrD target "nodes").toList.any (fun n => J.kind n == "VariableDeclaration" && (J.opt n "value").isSome))
  unless targetRead.dropped.isEmpty && targetRead.initGap.isNone &&
      (targetRead.ctor.isSome || implicitSafe) do
    throw "solidity.worldFactory.target: complete imported constructor/initializers required"
  let payments ← closedPayments ast target
  return ⟨ownerName, targetName, args, value, J.str? f "stateMutability" == some "payable", branches, targetRead.ctor.isSome, payments⟩

end WorldCreation

syntax (name := solcWorldFactory) "solc_world_factory " str " hash " num
  " contract " str " function " str " as " ident : command

/-- Lower a complete supported source factory into checked world operations. -/
@[command_elab solcWorldFactory]
def elabSolcWorldFactory : CommandElab := fun stx => do
  let path : TSyntax `str := ⟨stx[1]⟩
  let fixtureHash : TSyntax `num := ⟨stx[3]⟩
  let file := System.FilePath.mk (← getFileName)
  let bytes ← IO.FS.readBinFile ((file.parent.getD ".") / path.getString)
  unless (fnv1a64 bytes).toNat == fixtureHash.getNat do
    throwError "solidity.worldFactory.hash: fixture content differs from the named hash"
  let some text := String.fromUTF8? bytes | throwError "solidity.worldFactory.fixture: expected UTF-8"
  let json ← ofExcept (Json.parse text)
  let ast ← ofExcept (json.getObjVal? "ast")
  let factory ← ofExcept (WorldCreation.read ast (stx[5].isStrLit?.getD "") (stx[7].isStrLit?.getD ""))
  let output := stx[9].getId
  let fullOutput := (← getCurrNamespace) ++ output
  let sourceName (s : String) : Lean.Name := fullOutput ++ `Source ++ Lean.Name.mkSimple s
  let target := mkIdent (sourceName factory.target)
  let owner := mkIdent (sourceName factory.owner)
  elabCommand (← `(solc_import $path hash $fixtureHash as $target testing))
  elabCommand (← `(solc_import $path hash $fixtureHash as $owner testing))
  let targetFull := sourceName factory.target
  let rows ← liftTermElabM <| unsafe evalConst (List ImportRow) (targetFull ++ `report)
  unless !factory.ctorRequired || rows.any (fun r => r.name == "constructor" && r.status == .elaborated) do
    throwError "solidity.worldFactory.constructor: imported constructor did not elaborate"
  let namespaceText := output.toString
  let targetText := s!"{fullOutput}.Source.«{factory.target}»"
  let ownerText := s!"{fullOutput}.Source.«{factory.owner}»"
  let command (text : String) : CommandElabM Unit := do
    let parsed ← ofExcept (Parser.runParserCategory (← getEnv) `command text)
    elabCommand (atRef stx parsed)
  command s!"inductive {namespaceText}.Code where\n | factory | target\n deriving DecidableEq"
  command s!"def {namespaceText}.contracts : {namespaceText}.Code → Solidity.Contract\n | .factory => {ownerText}\n | .target => {targetText}"
  command s!"def {namespaceText}.constructor : Solidity.Prog ({namespaceText}.contracts .target) [] [] := sol[{targetText}]\{ constructor({", ".intercalate factory.args}); }"
  command s!"def {namespaceText}.deploy (w : Solidity.ContractWorld.World {namespaceText}.contracts) (self : Solidity.ContractWorld.Address) (ctx : Solidity.ContractWorld.Context) := w.create {namespaceText}.Code.factory self Solidity.Prog.nil ctx"
  let paymentsSafe := if factory.payments.isEmpty then "true" else
    " && ".intercalate (factory.payments.map (fun n =>
      s!"(w.accounts ⟨⟨{n}, by decide +kernel⟩, by decide +kernel⟩).isNone"))
  command s!"def {namespaceText}.assumptions (w : Solidity.ContractWorld.World {namespaceText}.contracts) (ctx : Solidity.ContractWorld.Context) : Bool := !w.isLibrary .factory && !w.isLibrary .target && ctx.ext.isEmpty && ({paymentsSafe})"
  let resultType := if factory.branches.isSome then "Bool" else s!"Solidity.ContractWorld.Handle {namespaceText}.Code.target"
  let finish := match factory.branches with
    | none => s!"next.create .target fresh {namespaceText}.constructor \{ sender := self.address, mode := .ordinary ⟨{factory.value}, by decide +kernel⟩, ext := ctx.ext }"
    | some (ok, err) => s!"next.tryCreate (.ok ()) .target (fun _ => fresh) (fun _ => {namespaceText}.constructor) (fun _ => \{ sender := self.address, mode := .ordinary ⟨{factory.value}, by decide +kernel⟩, ext := ctx.ext }) (fun w _ => .ok (w, {ok})) (fun w _ => .ok (w, {err}))"
  command s!"def {namespaceText}.run (w : Solidity.ContractWorld.World {namespaceText}.contracts) (self : Solidity.ContractWorld.Handle {namespaceText}.Code.factory) (ctx : Solidity.ContractWorld.Context) (fresh : Solidity.ContractWorld.Address) (_admitted : {namespaceText}.assumptions w ctx = true) : Solidity.TRes (Solidity.ContractWorld.World {namespaceText}.contracts × {resultType}) := do\n if w.isLibrary .factory || ctx.isStatic then .error .revert else do\n  w.paidRun self ctx {factory.payable} (fun next => {finish})"

  let creation := match factory.branches with
    | none => s!".create .target fresh {namespaceText}.constructor \{ sender := self.address, mode := .ordinary ⟨{factory.value}, by decide +kernel⟩, ext := ctx.ext }"
    | some _ => s!".tryCreate (.ok ()) .target (fun _ => fresh) (fun _ => {namespaceText}.constructor) (fun _ => \{ sender := self.address, mode := .ordinary ⟨{factory.value}, by decide +kernel⟩, ext := ctx.ext })"
  let tailProof := match factory.branches with
    | none => "Solidity.ContractWorld.Operation.create_certificate"
    | some _ => "Solidity.ContractWorld.Operation.tryCreate_certificate"
  command s!"def {namespaceText}.operation (self : Solidity.ContractWorld.Handle {namespaceText}.Code.factory) (ctx : Solidity.ContractWorld.Context) (fresh : Solidity.ContractWorld.Address) : Solidity.ContractWorld.Operation {namespaceText}.contracts := .seq (.guard (!ctx.isStatic)) (.seq (.call .factory self (Solidity.ContractWorld.Entry.unit .nil {factory.payable}) ctx) ({creation}))"
  command s!"theorem {namespaceText}.run_certificate (w : Solidity.ContractWorld.World {namespaceText}.contracts) (self : Solidity.ContractWorld.Handle {namespaceText}.Code.factory) (ctx : Solidity.ContractWorld.Context) (fresh : Solidity.ContractWorld.Address) (admitted : {namespaceText}.assumptions w ctx = true) : Solidity.ContractWorld.forgetResult ({namespaceText}.run w self ctx fresh admitted) = ({namespaceText}.operation self ctx fresh).run w := by\n apply Solidity.ContractWorld.World.guardedPaidRun_certificate\n intro next\n exact {tailProof} .."
  command s!"theorem {namespaceText}.run_reachable \{funding roles allowed} \{w next : Solidity.ContractWorld.World {namespaceText}.contracts} \{result : {resultType}} (self : Solidity.ContractWorld.Handle {namespaceText}.Code.factory) (ctx : Solidity.ContractWorld.Context) (fresh : Solidity.ContractWorld.Address) (admitted : {namespaceText}.assumptions w ctx = true) (before : Solidity.ContractWorld.Reachable funding roles allowed w) (permitted : allowed w ({namespaceText}.operation self ctx fresh)) (success : {namespaceText}.run w self ctx fresh admitted = .ok (next, result)) : Solidity.ContractWorld.Reachable funding roles allowed next := Solidity.ContractWorld.Reachable.of_certificate before permitted ({namespaceText}.run_certificate w self ctx fresh admitted) success"

/-- Metadata of the exact source linked-mutation fragment. -/
structure WorldLinked where
  owner : String
  library : String
  method : String
  libraryMethod : String
  payable : Bool
  root : String
  field : String
  literal : String

/-- Recognize a complete direct linked storage-field mutation, resolving both
the library function and the caller's root by compiler declaration IDs. -/
def WorldLinked.read (ast : Json) (ownerName method : String) : Except String WorldLinked := do
  let units := (J.arrD ast "nodes").toList
  let [owner] := units.filter (fun n => J.kind n == "ContractDefinition" &&
      J.str? n "name" == some ownerName)
    | throw "solidity.worldLibrary.owner: expected one source contract"
  unless J.str? owner "contractKind" == some "contract" &&
      J.opt owner "abstract" == some (.bool false) && (J.arrD owner "baseContracts").isEmpty do
    throw "solidity.worldLibrary.owner: noninheriting concrete caller required"
  let nodes := (J.arrD owner "nodes").toList
  if nodes.any (fun n => J.kind n == "VariableDeclaration" &&
      (J.str? n "storageLocation" == some "transient" || J.opt n "transient" == some (.bool true))) then
    throw "solidity.worldLibrary.owner: transient state needs the shared world transaction interface"
  if nodes.any (fun n => (J.kind n == "VariableDeclaration" && (J.opt n "value").isSome) ||
      (J.kind n == "FunctionDefinition" && J.str? n "kind" == some "constructor")) then
    throw "solidity.worldLibrary.owner: default-initialized storage and implicit constructor required"
  let [f] := nodes.filter (fun n => J.kind n == "FunctionDefinition" && J.str? n "name" == some method)
    | throw "solidity.worldLibrary.method: missing or overloaded method"
  unless [some "public", some "external"].contains (J.str? f "visibility") &&
      (J.arrD f "modifiers").isEmpty do
    throw "solidity.worldLibrary.method: unmodified public/external method required"
  for key in ["parameters", "returnParameters"] do
    let some ps := J.opt f key | throw "solidity.worldLibrary.method: missing signature"
    unless (J.arrD ps "parameters").isEmpty do
      throw "solidity.worldLibrary.method: no caller parameters or returns supported yet"
  let some body := J.opt f "body" | throw "solidity.worldLibrary.body: missing body"
  let [statement] := (J.arrD body "statements").toList
    | throw "solidity.worldLibrary.body: exactly one direct library call required"
  unless J.kind statement == "ExpressionStatement" do
    throw "solidity.worldLibrary.body: exactly one direct library call required"
  let some call := J.opt statement "expression" | throw "solidity.worldLibrary.body: missing call"
  unless J.kind call == "FunctionCall" && (J.arrD call "names").isEmpty do
    throw "solidity.worldLibrary.call: positional direct call required"
  let [argument] := (J.arrD call "arguments").toList
    | throw "solidity.worldLibrary.arguments: exactly one caller storage root required"
  let some rootId := J.ref? argument | throw "solidity.worldLibrary.arguments: unresolved storage root"
  unless J.kind argument == "Identifier" &&
      nodes.any (fun n => J.kind n == "VariableDeclaration" &&
        J.opt n "stateVariable" == some (.bool true) && J.id? n == some rootId) do
    throw "solidity.worldLibrary.arguments: resolved caller storage root required"
  let some callee := J.opt call "expression" | throw "solidity.worldLibrary.call: no callee"
  unless J.kind callee == "MemberAccess" do
    throw "solidity.worldLibrary.call: qualified library call required"
  let some ref := J.ref? callee | throw "solidity.worldLibrary.call: unresolved callee"
  let [(lib, lf)] := units.flatMap (fun lib =>
      if J.str? lib "contractKind" == some "library" then
        (J.arrD lib "nodes").toList.filterMap (fun n =>
          if J.kind n == "FunctionDefinition" && J.id? n == some ref then some (lib, n) else none)
      else [])
    | throw "solidity.worldLibrary.call: public/external source library declaration required"
  let some receiver := J.opt callee "expression"
    | throw "solidity.worldLibrary.call: missing library qualifier"
  unless J.kind receiver == "Identifier" && J.ref? receiver == J.id? lib do
    throw "solidity.worldLibrary.call: resolved direct library qualifier required"
  unless [some "public", some "external"].contains (J.str? lf "visibility") &&
      (J.arrD lf "modifiers").isEmpty do
    throw "solidity.worldLibrary.call: public/external unmodified library entry required"
  let some ps := J.opt lf "parameters" | throw "solidity.worldLibrary.parameters: missing signature"
  let [parameter] := (J.arrD ps "parameters").toList
    | throw "solidity.worldLibrary.parameters: one storage-reference parameter required"
  unless J.str? parameter "storageLocation" == some "storage" do
    throw "solidity.worldLibrary.parameters: one storage-reference parameter required"
  let some rets := J.opt lf "returnParameters" | throw "solidity.worldLibrary.parameters: missing returns"
  unless (J.arrD rets "parameters").isEmpty do
    throw "solidity.worldLibrary.parameters: library returns need separate lowering"
  let some lb := J.opt lf "body" | throw "solidity.worldLibrary.body: missing library body"
  let [ls] := (J.arrD lb "statements").toList
    | throw "solidity.worldLibrary.body: exactly one direct storage-field assignment required"
  unless J.kind ls == "ExpressionStatement" do
    throw "solidity.worldLibrary.body: exactly one direct storage-field assignment required"
  let some assignment := J.opt ls "expression" | throw "solidity.worldLibrary.body: missing assignment"
  unless J.kind assignment == "Assignment" && J.str? assignment "operator" == some "=" do
    throw "solidity.worldLibrary.body: direct assignment required"
  let some lhs := J.opt assignment "leftHandSide" | throw "solidity.worldLibrary.body: missing left side"
  let some base := J.opt lhs "expression" | throw "solidity.worldLibrary.body: missing storage reference"
  let some parameterId := J.id? parameter | throw "solidity.worldLibrary.parameters: unresolved parameter"
  unless J.kind lhs == "MemberAccess" && J.kind base == "Identifier" &&
      J.ref? base == some parameterId do
    throw "solidity.worldLibrary.body: field of the resolved storage parameter required"
  let some rhs := J.opt assignment "rightHandSide" | throw "solidity.worldLibrary.body: missing right side"
  let literal ← WorldCreation.literal rhs
  let some root := J.str? argument "name" | throw "solidity.worldLibrary.arguments: unnamed root"
  let some field := J.str? lhs "memberName" | throw "solidity.worldLibrary.body: unnamed field"
  let libraryName := (J.str? lib "name").getD ""
  for name in [ownerName, libraryName] do
    let read ← readContract ast name [] true
    unless read.dropped.isEmpty && read.initGap.isNone do
      throw "solidity.worldLibrary.storage: complete imported storage required"
  return ⟨ownerName, libraryName, method, (J.str? lf "name").getD "",
    J.str? f "stateMutability" == some "payable", root, field, literal⟩

syntax (name := solcWorldLibrary) "solc_world_library " str " hash " num
  " contract " str " function " str " as " ident : command

/-- Lower the recognized source linked storage mutation into a checked world call. -/
@[command_elab solcWorldLibrary]
def elabSolcWorldLibrary : CommandElab := fun stx => do
  let path : TSyntax `str := ⟨stx[1]⟩
  let fixtureHash : TSyntax `num := ⟨stx[3]⟩
  let file := System.FilePath.mk (← getFileName)
  let bytes ← IO.FS.readBinFile ((file.parent.getD ".") / path.getString)
  unless (fnv1a64 bytes).toNat == fixtureHash.getNat do
    throwError "solidity.worldLibrary.hash: fixture content differs from the named hash"
  let some text := String.fromUTF8? bytes | throwError "solidity.worldLibrary.fixture: expected UTF-8"
  let json ← ofExcept (Json.parse text)
  let ast ← ofExcept (json.getObjVal? "ast")
  let linked ← ofExcept (WorldLinked.read ast (stx[5].isStrLit?.getD "") (stx[7].isStrLit?.getD ""))
  let output := stx[9].getId
  let fullOutput := (← getCurrNamespace) ++ output
  let sourceName (s : String) : Lean.Name := fullOutput ++ `Source ++ Lean.Name.mkSimple s
  let owner := mkIdent (sourceName linked.owner)
  let library := mkIdent (sourceName linked.library)
  elabCommand (← `(solc_import $path hash $fixtureHash as $owner testing))
  elabCommand (← `(solc_import $path hash $fixtureHash as $library testing))
  let namespaceText := output.toString
  let ownerText := s!"{fullOutput}.Source.«{linked.owner}»"
  let libraryText := s!"{fullOutput}.Source.«{linked.library}»"
  let command (text : String) : CommandElabM Unit := do
    let parsed ← ofExcept (Parser.runParserCategory (← getEnv) `command text)
    elabCommand (atRef stx parsed)
  command s!"inductive {namespaceText}.Code where\n | caller | library\n deriving DecidableEq"
  command s!"def {namespaceText}.contracts : {namespaceText}.Code → Solidity.Contract\n | .caller => {ownerText}\n | .library => {libraryText}"
  command s!"def {namespaceText}.linkedBody : Solidity.Prog ({namespaceText}.contracts .caller) [] [] := sol[{ownerText}]\{ {identText linked.root}.{identText linked.field} = {linked.literal}; }"
  command s!"def {namespaceText}.roles : {namespaceText}.Code → Solidity.ContractWorld.Role\n | .caller => .contractCode\n | .library => .libraryCode"
  command s!"def {namespaceText}.deployCaller (w : Solidity.ContractWorld.World {namespaceText}.contracts) (self : Solidity.ContractWorld.Address) (ctx : Solidity.ContractWorld.Context) := w.create {namespaceText}.Code.caller self Solidity.Prog.nil ctx"
  command s!"def {namespaceText}.deployLibrary (w : Solidity.ContractWorld.World {namespaceText}.contracts) (self : Solidity.ContractWorld.Address) (ctx : Solidity.ContractWorld.Context) := w.deployLibrary {namespaceText}.Code.library self ctx"
  command s!"def {namespaceText}.run (w : Solidity.ContractWorld.World {namespaceText}.contracts) (self : Solidity.ContractWorld.Handle {namespaceText}.Code.caller) (ctx : Solidity.ContractWorld.Context) (linkedAddress : Solidity.ContractWorld.Address) : Solidity.TRes (Solidity.ContractWorld.World {namespaceText}.contracts × Unit) := do\n w.paidRun self ctx {linked.payable} (fun next => next.libraryCall self ⟨.library, linkedAddress, Solidity.ContractWorld.Entry.unit {namespaceText}.linkedBody⟩ ctx)"

  command s!"def {namespaceText}.operation (self : Solidity.ContractWorld.Handle {namespaceText}.Code.caller) (ctx : Solidity.ContractWorld.Context) (linkedAddress : Solidity.ContractWorld.Address) : Solidity.ContractWorld.Operation {namespaceText}.contracts := .seq (.call .caller self (Solidity.ContractWorld.Entry.unit .nil {linked.payable}) ctx) (.libraryCall .caller self ⟨.library, linkedAddress, Solidity.ContractWorld.Entry.unit {namespaceText}.linkedBody⟩ ctx)"
  command s!"theorem {namespaceText}.run_certificate (w : Solidity.ContractWorld.World {namespaceText}.contracts) (self : Solidity.ContractWorld.Handle {namespaceText}.Code.caller) (ctx : Solidity.ContractWorld.Context) (linkedAddress : Solidity.ContractWorld.Address) (ordinary : w.isLibrary .caller = false) : Solidity.ContractWorld.forgetResult ({namespaceText}.run w self ctx linkedAddress) = ({namespaceText}.operation self ctx linkedAddress).run w := by\n apply Solidity.ContractWorld.World.paidRun_certificate _ _ _ _ _ _ ordinary\n intro next\n exact Solidity.ContractWorld.Operation.libraryCall_certificate .."
  command s!"theorem {namespaceText}.run_reachable \{funding roles allowed} \{w next : Solidity.ContractWorld.World {namespaceText}.contracts} (self : Solidity.ContractWorld.Handle {namespaceText}.Code.caller) (ctx : Solidity.ContractWorld.Context) (linkedAddress : Solidity.ContractWorld.Address) (ordinary : w.isLibrary .caller = false) (before : Solidity.ContractWorld.Reachable funding roles allowed w) (permitted : allowed w ({namespaceText}.operation self ctx linkedAddress)) (success : {namespaceText}.run w self ctx linkedAddress = .ok (next, ())) : Solidity.ContractWorld.Reachable funding roles allowed next := Solidity.ContractWorld.Reachable.of_certificate before permitted ({namespaceText}.run_certificate w self ctx linkedAddress ordinary) success"

end Solidity.Frontend
