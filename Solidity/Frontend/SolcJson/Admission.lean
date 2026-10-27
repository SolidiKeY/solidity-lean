import Solidity.Frontend.SolcJson.Body

/-!
# Admission of solc source

The bounded walker classifies known AST forms and follows declaration headers
by identity. Only the reader's resolved execution roots execute; an arbitrary
function reference never imports its body. JSON is the external compiler
format, not another representation of an intrinsic statement.
-/

namespace Solidity.Frontend.Admission
open Lean (Json)
open Solidity.Language
open Source

private def atNode (j : Json) (fs : List Feature) : List Use :=
  fs.map fun f => ⟨f, J.line j⟩

private def builtin (j : Json) : Bool :=
  (J.ref? j).any (· < 0)

private def builtinNamed (j : Json) (name : String) : Bool :=
  J.kind j == "Identifier" && builtin j && J.str? j "name" == some name

private def magicMember (j : Json) : List Feature :=
  let base := (J.opt j "expression").getD .null
  let member := (J.str? j "memberName").getD ""
  if builtinNamed base "block" then
    match member with
    | "timestamp" => [.blockTimestamp]
    | "coinbase" => [.blockCoinbase]
    | "difficulty" => [.blockDifficulty]
    | "prevrandao" => [.blockPrevrandao]
    | "number" => [.blockNumber]
    | "gaslimit" => [.blockGaslimit]
    | "chainid" => [.blockChainid]
    | "basefee" => [.blockBasefee]
    | "blobbasefee" => [.blockBlobbasefee]
    | "slotnum" => [.blockSlotnum]
    | _ => []
  else if builtinNamed base "msg" then
    match member with
    | "sender" => [.msgSender]
    | "value" => [.msgValue]
    | "data" | "sig" => [.rawCalldata]
    | _ => []
  else if builtinNamed base "tx" then
    match member with
    | "origin" => [.txOrigin]
    | "gasprice" => [.txGasprice]
    | _ => []
  else if builtinNamed base "abi" then
    match member with
    | "encode" => [.abiEncode]
    | "encodePacked" => [.abiEncodePacked]
    | "encodeWithSelector" => [.abiEncodeWithSelector]
    | "encodeWithSignature" => [.abiEncodeWithSignature]
    | "encodeCall" => [.abiEncodeCall]
    | "decode" => [.abiDecode]
    | _ => []
  else if nativeMember j && (J.tyStr base).startsWith "address" then
    match member with
    | "balance" => [.addressBalance]
    | "call" => [.lowLevelCall]
    | "code" => [.addressCode]
    | "codehash" => [.addressCodehash]
    | "delegatecall" => [.delegatecall]
    | "staticcall" => [.lowLevelStaticcall]
    | "send" | "transfer" => [.sendTransfer]
    | _ => []
  else if (J.tyStr base).startsWith "type(contract " then
    match member with
    | "creationCode" => [.creationCode]
    | "runtimeCode" => [.runtimeCode]
    | "name" => [.typeName]
    | "interfaceId" => [.interfaceId]
    | _ => []
  else if (J.tyStr base).startsWith "function " then
    match member with
    | "selector" => [.functionSelector]
    | "address" => [.functionAddress]
    | _ => []
  else []

private def builtinFeatures (j : Json) : List Feature :=
  if !builtin j then [] else
  match J.str? j "name" with
  | some "assert" => [.assertBuiltin]
  | some "require" => [.requireBuiltin]
  | some "revert" => [.revertBuiltin]
  | some "addmod" => [.addmodBuiltin]
  | some "mulmod" => [.mulmodBuiltin]
  | some "keccak256" => [.keccakBuiltin]
  | some "sha256" => [.sha256Builtin]
  | some "ripemd160" => [.ripemd160Builtin]
  | some "ecrecover" => [.ecrecoverBuiltin]
  | some "erc7201" => [.erc7201Builtin]
  | some "gasleft" => [.gasleft]
  | some "blockhash" => [.blockhashBuiltin]
  | some "blobhash" => [.blobhashBuiltin]
  | some "selfdestruct" => [.selfdestruct]
  | some "type" => [.metaTypeExpression]
  | some "this" => [.thisAddress]
  | _ => []

private def pragmaFeatures (j : Json) : List Feature :=
  match (J.arrD j "literals").toList.head?.bind (·.getStr?.toOption) with
  | some "solidity" => [.pragmaVersion]
  | some "abicoder" => [.pragmaAbicoder]
  | _ => [.pragmaOther]

/-- Every known node kind is explicit; metadata objects without nodeType
are traversed but do not count as syntax nodes. -/
private def nodeFeatures (j : Json) : Option (List Feature) :=
  match J.kind j with
  | "" => some []
  | "PragmaDirective" => some (pragmaFeatures j)
  | "Identifier" => some ([.identifiers, .names] ++ builtinFeatures j)
  | "MemberAccess" => some ([.memberAccess] ++ magicMember j)
  | "Literal" => some (match J.str? j "kind" with
      | some "number" => if J.tyStr j == "address" then [.addressLiterals]
        else [.numericLiterals, .exactConstants]
      | some "bool" => [.booleanLiterals]
      | some "string" => [.stringLiterals]
      | some "unicodeString" => [.unicodeLiterals]
      | some "hexString" => [.hexLiterals]
      | _ => [])
  | "FunctionDefinition" => some ([.functions, .visibility, .stateMutability] ++
      match J.str? j "kind" with
      | some "constructor" => [.constructors]
      | some "receive" => [.receiveFunction]
      | some "fallback" => [.fallbackFunction] ++
        if ((J.opt j "parameters").bind (J.arr? · "parameters")).any (! ·.isEmpty) ||
          ((J.opt j "returnParameters").bind (J.arr? · "parameters")).any (! ·.isEmpty)
        then [.rawCalldata, .rawReturndata] else []
      | _ => [])
  | "VariableDeclaration" => some ([.variableDeclarations] ++
      (if J.opt j "stateVariable" == some (.bool true) then
        [.stateVariables] ++ (if J.str? j "visibility" == some "public" then [.publicGetters] else [])
       else []) ++
      (if J.opt j "constant" == some (.bool true) then [.constants] else []) ++
      (if J.str? j "mutability" == some "immutable" then [.immutables] else []) ++
      match J.str? j "storageLocation" with
      | some "storage" => [.storageLocation]
      | some "memory" => [.memoryLocation]
      | some "calldata" => [.calldataLocation]
      | _ => [])
  | "ElementaryTypeName" => some (
      let name := (J.str? j "name").getD ""
      if name == "bool" then [.boolType]
      else if name.startsWith "uint" || name.startsWith "int" then [.integerTypes]
      else if name.startsWith "address" then [.addressTypes]
      else if name == "bytes" then [.dynamicBytesType]
      else if name.startsWith "bytes" then [.fixedBytesTypes]
      else if name == "string" then [.stringType]
      else if name.startsWith "fixed" || name.startsWith "ufixed" then [.fixedPoint]
      else [])
  | "ArrayTypeName" => some [if (J.opt j "length").isSome then .fixedArrays else .dynamicArrays]
  | "UnaryOperation" => some [match J.str? j "operator" with
      | some "++" | some "--" => .increments
      | some "delete" => .deleteExpression
      | _ => .unaryArithmetic]
  | "BinaryOperation" => some [match J.str? j "operator" with
      | some "&" | some "|" | some "^" => .bitwise
      | some "<<" | some ">>" => .shifts
      | some ">>>" => .unsignedRightShift
      | some "&&" | some "||" => .shortCircuit
      | some "==" | some "!=" | some "<" | some ">" | some "<=" | some ">=" => .comparisons
      | _ => .arithmetic]
  | "FunctionCallOptions" => some ([.callOptions] ++
      ((J.arrD j "names").toList.filterMap fun n =>
        match n.getStr?.toOption with
        | some "gas" => some .gasOption
        | some "salt" => some .create2Salt
        | some "value" => some .valueOption
        | _ => none))
  | "SourceUnit" => some [.sourceUnits, .comments, .typeValidation]
  | "ImportDirective" => some [.imports]
  | "ContractDefinition" => some [match J.str? j "contractKind" with
      | some "interface" => .interfaces
      | some "library" => .libraries
      | _ => .contracts]
  | "StorageLayoutSpecifier" => some [.storageLayout]
  | "InheritanceSpecifier" => some [.inheritance]
  | "UsingForDirective" => some [.usingFor]
  | "StructDefinition" => some [.structDeclarations]
  | "EnumDefinition" => some [.enumDeclarations]
  | "EnumValue" => some []
  | "UserDefinedValueTypeDefinition" => some [.valueTypeDeclarations]
  | "ParameterList" => some []
  | "OverrideSpecifier" => some [.overrideDeclarations]
  | "ModifierDefinition" => some [.modifiers]
  | "ModifierInvocation" => some [.modifiers]
  | "EventDefinition" => some [.eventDeclarations]
  | "ErrorDefinition" => some [.errorDeclarations]
  | "StructuredDocumentation" => some [.comments]
  | "IdentifierPath" => some [.identifiers, .names]
  | "ElementaryTypeNameExpression" => some [.explicitConversions]
  | "UserDefinedTypeName" => some ([.names] ++
      if (J.tyStr j).startsWith "struct " then [.structTypes]
      else if (J.tyStr j).startsWith "enum " then [.enumTypes] else [.valueTypes])
  | "Mapping" => some [.mappings]
  | "FunctionTypeName" => some [if J.str? j "visibility" == some "external"
      then .externalFunctionTypes else .internalFunctionTypes]
  | "TupleExpression" => some [if J.opt j "isInlineArray" == some (.bool true) then .inlineArrays else .tupleExpressions]
  | "IndexAccess" => some [.indexAccess]
  | "IndexRangeAccess" => some [.rangeAccess]
  | "Conditional" => some [.conditional]
  | "Assignment" => some [if J.str? j "operator" == some "=" then .assignment else .compoundAssignment]
  | "NewExpression" => some [if (J.opt j "typeName").any (J.kind · == "ArrayTypeName")
      then .newMemory else .newContract]
  | "FunctionCall" => some ([.functionCalls] ++
      (match J.str? j "kind" with
      | some "typeConversion" => [.explicitConversions]
      | some "structConstructorCall" => [.structConstruction]
      | _ => [.internalCalls]) ++
      if !(J.arrD j "names").isEmpty then [.namedArguments] else [])
  | "Block" => some [.blocks]
  | "UncheckedBlock" => some [.uncheckedBlock, .uncheckedArithmetic]
  | "PlaceholderStatement" => some [.modifierPlaceholder]
  | "VariableDeclarationStatement" => some [.variableDeclarations]
  | "ExpressionStatement" => some [.expressionStatements]
  | "IfStatement" => some [.ifStatement]
  | "WhileStatement" => some [.whileStatement]
  | "ForStatement" => some [.forStatement]
  | "DoWhileStatement" => some [.doWhileStatement]
  | "Break" => some [.breakStatement]
  | "Continue" => some [.continueStatement]
  | "Return" => some [.returnStatement]
  | "Throw" => some [.removedAliases]
  | "EmitStatement" => some [.emitStatement]
  | "RevertStatement" => some [.revertStatement]
  | "TryStatement" => some [.tryStatement]
  | "TryCatchClause" => some [.catchClauses]
  | _ => none
private def diagnostic (j : Json) (kind : DiagnosticKind) (name : Lean.Name)
    (reason : String) (feature : Option Feature := none) : Diagnostic :=
  { kind, name, reason, feature, line := J.line j }

/-- References follow headers. Only explicitly supplied execution roots run. -/
def header (constantIds : List Int) (j : Json) : Json :=
  match j with
  | .obj fields => Json.mkObj ((fields.toList.filter fun (key, _) =>
      if J.kind j == "FunctionDefinition" || J.kind j == "ModifierDefinition" then
        !["body", "modifiers"].contains key
      else if J.kind j == "ContractDefinition" || J.kind j == "SourceUnit" then key != "nodes"
      else if J.kind j == "VariableDeclaration" then
        key != "value" || (J.id? j).any constantIds.contains
      else true).map fun (key, value) =>
        if J.kind j == "ContractDefinition" && key == "baseContracts" then
          (key, .arr ((value.getArr?.toOption.getD #[]).map fun base =>
            match base with
            | .obj fields => Json.mkObj (fields.toList.filter (·.1 != "arguments"))
            | _ => base))
        else (key, value))
  | _ => j

private def validateNode (provenance : Provenance) (j : Json) : Except Diagnostic Unit := do
  if (j.getObjVal? "nodeType").isOk && (J.str? j "nodeType").all (·.isEmpty) then
    throw (diagnostic j .unknownNode `solidity.unknownAstNode "non-string or empty AST node kind")
  if ["Identifier", "Literal", "UnaryOperation", "BinaryOperation", "Conditional",
      "Assignment", "IndexAccess", "MemberAccess", "FunctionCall", "NewExpression",
      "IndexRangeAccess", "TupleExpression"].contains (J.kind j) && (J.tyStr j).isEmpty then
    throw (diagnostic j .invalidAst `solidity.expressionType "expression lacks its compiler type")
  if J.kind j == "UnaryOperation" && !(j.getObjValAs? Bool "prefix").isOk then
    throw (diagnostic j .invalidAst `solidity.unaryPrefix "unary expression lacks its prefix flag")
  if J.kind j == "BinaryOperation" &&
      ((J.opt j "commonType").bind (J.str? · "typeString")).all (·.isEmpty) then
    throw (diagnostic j .invalidAst `solidity.commonType "binary expression lacks its common type")
  if J.kind j == "Literal" &&
      !(["number", "bool", "string", "unicodeString", "hexString"].contains ((J.str? j "kind").getD "")) then
    throw (diagnostic j .invalidAst `solidity.literalKind "unknown literal kind")
  if ["UnaryOperation", "BinaryOperation"].contains (J.kind j) then
    let allowed := if J.kind j == "UnaryOperation" then ["!", "-", "+", "~", "++", "--", "delete"]
      else ["+", "-", "*", "/", "%", "**", "&", "|", "^", "<<", ">>", ">>>",
        "==", "!=", "<", ">", "<=", ">=", "&&", "||"]
    unless allowed.contains ((J.str? j "operator").getD "") do
      throw (diagnostic j .invalidAst `solidity.operator "unknown expression operator")
  if J.kind j == "Assignment" && !["=", "+=", "-=", "*=", "/=", "%=", "**=",
      "&=", "|=", "^=", "<<=", ">>="].contains ((J.str? j "operator").getD "") then
    throw (diagnostic j .invalidAst `solidity.assignment "unknown assignment operator")
  if J.kind j == "VariableDeclaration" then
    let location := (J.str? j "storageLocation").getD ""
    if location == "transient" then
      throw (diagnostic j .missingImplementation `solidity.transientState
        "transient storage is not ordinary persistent state" (some .transientState))
    unless ["default", "storage", "memory", "calldata"].contains location do
      throw (diagnostic j .invalidAst `solidity.storageLocation "unknown data location")
  if J.kind j == "ElementaryTypeName" then
    let name := (J.str? j "name").getD ""
    unless (PrimTy.ofName? name).isSome || (narrowTy? name).isSome ||
        (bytesTy? name).isSome || ["address payable", "bytes", "string"].contains name ||
        name.startsWith "fixed" || name.startsWith "ufixed" do
      throw (diagnostic j .invalidAst `solidity.typeValidation s!"unrecognized elementary type {name}")
  if J.kind j == "FunctionCall" &&
      !["functionCall", "typeConversion", "structConstructorCall"].contains ((J.str? j "kind").getD "") then
    throw (diagnostic j .invalidAst `solidity.callKind "unknown function call kind")
  if J.kind j == "FunctionCallOptions" then
    let names := J.arrD j "names"
    unless names.size == (J.arrD j "options").size &&
        names.toList.all (fun n => (n.getStr?.toOption).any (["gas", "value", "salt"].contains)) do
      throw (diagnostic j .invalidAst `solidity.callOptions "unknown or unmatched call options")
  if provenance.effectiveCoder != some .v2 && J.kind j == "MemberAccess" &&
      J.str? j "memberName" == some "decode" &&
      (J.opt j "expression").any (builtinNamed · "abi") then
    throw (diagnostic j .missingImplementation `solidity.abiCoderV1
      "ABI-v1 decoding needs a mode-indexed decoder" (some .abiDecode))
  if provenance.effectiveCoder != some .v2 && J.kind j == "FunctionCall" &&
      (J.opt j "expression").any isExternalMember then
    throw (diagnostic j .missingImplementation `solidity.abiCoderV1
      "ABI-v1 external return decoding needs a mode-indexed decoder" (some .externalTypedCalls))

private structure Found where
  uses : Array Use := #[]
  references : List Int := []

private def Found.append (a b : Found) : Found :=
  { uses := a.uses ++ b.uses, references := a.references ++ b.references }

/-- The exemption follows exactly the value-call path consumed by the reader.
Receiver, amount and siblings start fresh. -/
private def paymentChild (j : Json) (key : String) (payment : Bool) : Bool :=
  if (valueCall? j).isSome then key == "initialValue"
  else payment && ["FunctionCall", "FunctionCallOptions"].contains (J.kind j) &&
    key == "expression"

private def walk (provenance : Provenance) (declarations : List Json) :
    Nat → Json → Bool → Except Diagnostic Found
  | 0, j, _ => throw (diagnostic j .invalidAst `solidity.astDepth "AST depth bound exhausted")
  | fuel + 1, j, payment => do
    validateNode provenance j
    let resolvedOperator ← match operatorAlias? declarations j with
      | .ok call => pure call
      | .error gap => throw (diagnostic j .invalidAst `solidity.operatorAliases
          gap.msg (some .operatorAliases))
    if J.kind j == "MemberAccess" then
      let member := (J.str? j "memberName").getD ""
      if ["address", "selector"].contains member then
        if let some receiver := J.opt j "expression" then
          let declarationMember := ((J.ref? receiver).bind fun id =>
            declarations.find? (J.id? · == some id)).any fun declaration =>
              J.kind declaration == "FunctionDefinition" ||
                isPublicGetterMember declaration receiver
          -- Error/event references also have a function-shaped compiler type.
          -- Admit only their validated static metadata path, never a receiver
          -- that could have effects or a stored function's address/selector.
          let staticDeclaration := J.kind receiver == "Identifier" ||
            J.kind receiver == "IdentifierPath" ||
            (J.kind receiver == "MemberAccess" &&
              ((J.opt receiver "expression").bind J.ref?).any (fun id =>
                declarations.any (fun d => J.id? d == some id && J.kind d == "ContractDefinition")))
          let declarationSelector := member == "selector" && staticDeclaration &&
            ((J.ref? receiver).bind fun id => declarations.find? (J.id? · == some id)).any (fun d =>
              (["ErrorDefinition", "EventDefinition"].contains (J.kind d)) &&
              (Solidity.Frontend.declarationMetadata declarations receiver member).isOk)
          if (J.tyStr receiver).startsWith "function " && !declarationSelector &&
              (storedFunctionMemberType? j).isNone &&
              !declarationMember then
            throw (diagnostic j .missingImplementation `solidity.functionMemberKind
              "stored function members need typed ABI address/selector observations"
              (some (if member == "address" then .functionAddress else .functionSelector)))
    if J.kind j == "InlineAssembly" then
      return { uses := (atNode j [if (memoryRethrow? declarations j).isSome
        then .canonicalRethrow else .inlineAssembly]).toArray }
    let some features := nodeFeatures j |
      throw (diagnostic j .unknownNode `solidity.unknownAstNode s!"unrecognized solc AST node {J.kind j}")
    let features := if payment && J.kind j == "MemberAccess" then
        features.filter (· != .lowLevelCall) ++ [.emptyDataValueCall] else features
    let commonType := ((J.opt j "commonType").bind (J.str? · "typeString")).getD ""
    let features := features ++ (if resolvedOperator.isSome then [.operatorAliases] else []) ++
      if commonType.startsWith "fixed" || commonType.startsWith "ufixed" then [.fixedPoint] else []
    let mut found : Found := {
      uses := (atNode j features).toArray, references :=
        (J.ref? j).toList.filter (· ≥ 0) ++ resolvedOperator.toList.map (·.1) }
    match j with
    | .arr values =>
      for value in values do found := found.append (← walk provenance declarations fuel value false)
    | .obj fields =>
      for (key, value) in fields.toList do
        found := found.append (← walk provenance declarations fuel value (paymentChild j key payment))
    | _ => pure ()
    return found

private def declarationClosure (provenance : Provenance) (declarations : List Json)
    (index : Std.HashMap Int Json) (constantIds : List Int) (depth : Nat) :
    Nat → Std.HashSet Int → List Int → Except Diagnostic Found
  | _, _, [] => pure {}
  | 0, _, _ => throw {
      kind := .unresolvedReference
      name := `solidity.declarationBudget
      reason := "declaration closure exceeded its finite declaration bound" }
  | fuel + 1, seen, id :: pending => do
    if seen.contains id then
      return ← declarationClosure provenance declarations index constantIds depth fuel seen pending
    let some declaration := index[id]? |
      throw {
        kind := .unresolvedReference
        name := `solidity.unresolvedDeclaration
        reason := s!"declaration #{id} is absent from the compiler AST" }
    let found ← walk provenance declarations depth (header constantIds declaration) false
    return found.append (← declarationClosure provenance declarations index constantIds depth fuel
      (seen.insert id) (pending ++ (found.references.eraseDups.filter fun next =>
        next != id && !seen.contains next && !pending.contains next)))

/-- Classify actual roots independently of inventory implementation status. -/
def scan (ast : Json) (provenance : Provenance) (request : AdmissionRequest) : ScopeScan := Id.run do
  if let some diagnostic := request.diagnostics.head? then return .rejected [] diagnostic
  let declarations := (J.nodes ast).filter (J.id? · |>.isSome)
  let mut index : Std.HashMap Int Json := {}
  for declaration in declarations do
    if let some id := J.id? declaration then
      if index.contains id then
        return .rejected [] (diagnostic declaration .invalidAst `solidity.duplicateDeclaration
          s!"duplicate declaration identity #{id}")
      index := index.insert id declaration
  if let some node := request.unresolvedDispatch.head? then
    return .rejected [] (diagnostic node .missingImplementation `solidity.functionDispatch
      "this call needs a finite set of typed dispatch targets" (some .functionValues))
  let depth := ast.compress.length + 1
  let result : Except Diagnostic Found := do
    let mut found : Found := { uses := (atNode request.entry [.featureDetection]).toArray }
    for root in request.evaluatedRoots do
      found := found.append (← walk provenance declarations depth root false)
    for root in request.declarationRoots do
      found := found.append (← walk provenance declarations depth (header request.constantIds root) false)
    let refs := found.references.eraseDups
    let closure ← declarationClosure provenance declarations index request.constantIds depth
      (declarations.length + refs.length + 1) {} refs
    return found.append closure
  match result with
  | .error diagnostic => return .rejected [] diagnostic
  | .ok found => return (ScopeScan.certify found.uses.toList).normalize

end Solidity.Frontend.Admission



