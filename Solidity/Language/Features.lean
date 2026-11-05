import Lean.Data.Name

/-!
# Solidity feature scope

Generated from docs/solidity-features.json by scripts/solidity-feature-audit.py.
The catalog classifies language features; it does not implement a Solidity parser,
a feature extractor, or a proof of frontend/solc equivalence. The subset wrapper
is meaningful only with a complete, declaration-aware feature extractor.

This module holds what the frontend reads: the features, their scope and their
requirement text. The inspection record of each feature (`Feature.info`: status,
upstream source lines, local evidence) is in `Language/FeatureInfo.lean`, which
only the library root imports, so editing a source-line reference rebuilds that
module alone (`docs/parallelism.md`, P5).
-/

namespace Solidity.Language

inductive Scope where
  | model | abstract | exclude | upstream
  deriving Repr, DecidableEq, Inhabited

/-- Source inspection status, not an end-to-end correctness certificate. -/
inductive Current where
  | present | limited | missing | notApplicable
  deriving Repr, DecidableEq, Inhabited

structure SourceRef where
  path : String
  line : Nat
  deriving Repr, DecidableEq, Inhabited

structure FeatureInfo where
  category : String
  spelling : String
  scope : Scope
  current : Current
  requirement : String
  upstream : List SourceRef
  localEvidence : List String
  deriving Repr, DecidableEq, Inhabited

inductive Feature where
  | identifiers
  | comments
  | numericLiterals
  | booleanLiterals
  | stringLiterals
  | unicodeLiterals
  | hexLiterals
  | addressLiterals
  | etherUnits
  | timeUnits
  | pragmaVersion
  | pragmaAbicoder
  | pragmaOther
  | sourceUnits
  | imports
  | contracts
  | interfaces
  | libraries
  | inheritance
  | overrideDeclarations
  | functions
  | freeFunctions
  | constructors
  | modifiers
  | modifierPlaceholder
  | receiveFunction
  | fallbackFunction
  | visibility
  | stateMutability
  | stateVariables
  | constants
  | immutables
  | publicGetters
  | structDeclarations
  | enumDeclarations
  | valueTypeDeclarations
  | errorDeclarations
  | eventDeclarations
  | usingFor
  | operatorAliases
  | boolType
  | integerTypes
  | addressTypes
  | fixedBytesTypes
  | dynamicBytesType
  | stringType
  | dynamicArrays
  | fixedArrays
  | mappings
  | structTypes
  | enumTypes
  | valueTypes
  | internalFunctionTypes
  | externalFunctionTypes
  | tupleTypes
  | storageLocation
  | memoryLocation
  | calldataLocation
  | recursiveTypes
  | names
  | parentheses
  | tupleExpressions
  | inlineArrays
  | memberAccess
  | indexAccess
  | rangeAccess
  | unaryArithmetic
  | increments
  | deleteExpression
  | arithmetic
  | bitwise
  | shifts
  | comparisons
  | shortCircuit
  | conditional
  | assignment
  | compoundAssignment
  | explicitConversions
  | implicitConversions
  | structConstruction
  | namedArguments
  | newMemory
  | functionCalls
  | callOptions
  | metaTypeExpression
  | blocks
  | uncheckedBlock
  | variableDeclarations
  | expressionStatements
  | ifStatement
  | whileStatement
  | forStatement
  | doWhileStatement
  | breakStatement
  | continueStatement
  | returnStatement
  | tryStatement
  | catchClauses
  | revertStatement
  | emitStatement
  | canonicalRethrow
  | assertBuiltin
  | requireBuiltin
  | revertBuiltin
  | addmodBuiltin
  | mulmodBuiltin
  | keccakBuiltin
  | sha256Builtin
  | ripemd160Builtin
  | ecrecoverBuiltin
  | erc7201Builtin
  | wrapUnwrap
  | bytesConcat
  | stringConcat
  | msgSender
  | msgValue
  | thisAddress
  | addressBalance
  | blockTimestamp
  | blockCoinbase
  | blockDifficulty
  | blockPrevrandao
  | blockNumber
  | blockGaslimit
  | blockChainid
  | blockBasefee
  | blockBlobbasefee
  | blockSlotnum
  | txOrigin
  | txGasprice
  | blockhashBuiltin
  | blobhashBuiltin
  | internalCalls
  | recursiveCalls
  | externalTypedCalls
  | externalSelfCalls
  | extensionCalls
  | functionValues
  | valueOption
  | sendTransfer
  | emptyDataValueCall
  | newContract
  | creationTry
  | callbackSemantics
  | externalLibraryCalls
  | abiEncode
  | abiEncodePacked
  | abiEncodeWithSelector
  | abiEncodeWithSignature
  | abiEncodeCall
  | abiDecode
  | typeBounds
  | typeName
  | interfaceId
  | functionSelector
  | functionAddress
  | errorEventSelector
  | arrayLength
  | arrayPush
  | arrayPushReference
  | arrayPop
  | storageCopy
  | memoryAliasing
  | storageAliasing
  | deleteMappingTails
  | danglingReferences
  | transientState
  | checkedArithmetic
  | uncheckedArithmetic
  | evaluationOrder
  | exactConstants
  | defaultInitialization
  | referenceCopyRules
  | panicCodes
  | revertPayloads
  | rollback
  | abiEntryValidation
  | constructorLifetime
  | nonpayableEntry
  | staticCallRestriction
  | termination
  | worldAssumptions
  | typeValidation
  | featureDetection
  | inlineAssembly
  | gasleft
  | gasOption
  | rawCalldata
  | rawReturndata
  | lowLevelCall
  | delegatecall
  | lowLevelStaticcall
  | selfdestruct
  | create2Salt
  | addressCode
  | addressCodehash
  | creationCode
  | runtimeCode
  | logicalStorageBase
  | storageLayout
  | memoryLayout
  | transientLayout
  | eventLog
  | machineResources
  | fixedPoint
  | removedAliases
  | unsignedRightShift
  | removedUnits
  | reservedKeywords
  | invalidLexemes
  | removedGenericSolidity
  | invalidModifierBody
  deriving Repr, DecidableEq, Inhabited

def Feature.id : Feature → String
  | .identifiers => "identifiers"
  | .comments => "comments"
  | .numericLiterals => "numericLiterals"
  | .booleanLiterals => "booleanLiterals"
  | .stringLiterals => "stringLiterals"
  | .unicodeLiterals => "unicodeLiterals"
  | .hexLiterals => "hexLiterals"
  | .addressLiterals => "addressLiterals"
  | .etherUnits => "etherUnits"
  | .timeUnits => "timeUnits"
  | .pragmaVersion => "pragmaVersion"
  | .pragmaAbicoder => "pragmaAbicoder"
  | .pragmaOther => "pragmaOther"
  | .sourceUnits => "sourceUnits"
  | .imports => "imports"
  | .contracts => "contracts"
  | .interfaces => "interfaces"
  | .libraries => "libraries"
  | .inheritance => "inheritance"
  | .overrideDeclarations => "overrideDeclarations"
  | .functions => "functions"
  | .freeFunctions => "freeFunctions"
  | .constructors => "constructors"
  | .modifiers => "modifiers"
  | .modifierPlaceholder => "modifierPlaceholder"
  | .receiveFunction => "receiveFunction"
  | .fallbackFunction => "fallbackFunction"
  | .visibility => "visibility"
  | .stateMutability => "stateMutability"
  | .stateVariables => "stateVariables"
  | .constants => "constants"
  | .immutables => "immutables"
  | .publicGetters => "publicGetters"
  | .structDeclarations => "structDeclarations"
  | .enumDeclarations => "enumDeclarations"
  | .valueTypeDeclarations => "valueTypeDeclarations"
  | .errorDeclarations => "errorDeclarations"
  | .eventDeclarations => "eventDeclarations"
  | .usingFor => "usingFor"
  | .operatorAliases => "operatorAliases"
  | .boolType => "boolType"
  | .integerTypes => "integerTypes"
  | .addressTypes => "addressTypes"
  | .fixedBytesTypes => "fixedBytesTypes"
  | .dynamicBytesType => "dynamicBytesType"
  | .stringType => "stringType"
  | .dynamicArrays => "dynamicArrays"
  | .fixedArrays => "fixedArrays"
  | .mappings => "mappings"
  | .structTypes => "structTypes"
  | .enumTypes => "enumTypes"
  | .valueTypes => "valueTypes"
  | .internalFunctionTypes => "internalFunctionTypes"
  | .externalFunctionTypes => "externalFunctionTypes"
  | .tupleTypes => "tupleTypes"
  | .storageLocation => "storageLocation"
  | .memoryLocation => "memoryLocation"
  | .calldataLocation => "calldataLocation"
  | .recursiveTypes => "recursiveTypes"
  | .names => "names"
  | .parentheses => "parentheses"
  | .tupleExpressions => "tupleExpressions"
  | .inlineArrays => "inlineArrays"
  | .memberAccess => "memberAccess"
  | .indexAccess => "indexAccess"
  | .rangeAccess => "rangeAccess"
  | .unaryArithmetic => "unaryArithmetic"
  | .increments => "increments"
  | .deleteExpression => "deleteExpression"
  | .arithmetic => "arithmetic"
  | .bitwise => "bitwise"
  | .shifts => "shifts"
  | .comparisons => "comparisons"
  | .shortCircuit => "shortCircuit"
  | .conditional => "conditional"
  | .assignment => "assignment"
  | .compoundAssignment => "compoundAssignment"
  | .explicitConversions => "explicitConversions"
  | .implicitConversions => "implicitConversions"
  | .structConstruction => "structConstruction"
  | .namedArguments => "namedArguments"
  | .newMemory => "newMemory"
  | .functionCalls => "functionCalls"
  | .callOptions => "callOptions"
  | .metaTypeExpression => "metaTypeExpression"
  | .blocks => "blocks"
  | .uncheckedBlock => "uncheckedBlock"
  | .variableDeclarations => "variableDeclarations"
  | .expressionStatements => "expressionStatements"
  | .ifStatement => "ifStatement"
  | .whileStatement => "whileStatement"
  | .forStatement => "forStatement"
  | .doWhileStatement => "doWhileStatement"
  | .breakStatement => "breakStatement"
  | .continueStatement => "continueStatement"
  | .returnStatement => "returnStatement"
  | .tryStatement => "tryStatement"
  | .catchClauses => "catchClauses"
  | .revertStatement => "revertStatement"
  | .emitStatement => "emitStatement"
  | .canonicalRethrow => "canonicalRethrow"
  | .assertBuiltin => "assertBuiltin"
  | .requireBuiltin => "requireBuiltin"
  | .revertBuiltin => "revertBuiltin"
  | .addmodBuiltin => "addmodBuiltin"
  | .mulmodBuiltin => "mulmodBuiltin"
  | .keccakBuiltin => "keccakBuiltin"
  | .sha256Builtin => "sha256Builtin"
  | .ripemd160Builtin => "ripemd160Builtin"
  | .ecrecoverBuiltin => "ecrecoverBuiltin"
  | .erc7201Builtin => "erc7201Builtin"
  | .wrapUnwrap => "wrapUnwrap"
  | .bytesConcat => "bytesConcat"
  | .stringConcat => "stringConcat"
  | .msgSender => "msgSender"
  | .msgValue => "msgValue"
  | .thisAddress => "thisAddress"
  | .addressBalance => "addressBalance"
  | .blockTimestamp => "blockTimestamp"
  | .blockCoinbase => "blockCoinbase"
  | .blockDifficulty => "blockDifficulty"
  | .blockPrevrandao => "blockPrevrandao"
  | .blockNumber => "blockNumber"
  | .blockGaslimit => "blockGaslimit"
  | .blockChainid => "blockChainid"
  | .blockBasefee => "blockBasefee"
  | .blockBlobbasefee => "blockBlobbasefee"
  | .blockSlotnum => "blockSlotnum"
  | .txOrigin => "txOrigin"
  | .txGasprice => "txGasprice"
  | .blockhashBuiltin => "blockhashBuiltin"
  | .blobhashBuiltin => "blobhashBuiltin"
  | .internalCalls => "internalCalls"
  | .recursiveCalls => "recursiveCalls"
  | .externalTypedCalls => "externalTypedCalls"
  | .externalSelfCalls => "externalSelfCalls"
  | .extensionCalls => "extensionCalls"
  | .functionValues => "functionValues"
  | .valueOption => "valueOption"
  | .sendTransfer => "sendTransfer"
  | .emptyDataValueCall => "emptyDataValueCall"
  | .newContract => "newContract"
  | .creationTry => "creationTry"
  | .callbackSemantics => "callbackSemantics"
  | .externalLibraryCalls => "externalLibraryCalls"
  | .abiEncode => "abiEncode"
  | .abiEncodePacked => "abiEncodePacked"
  | .abiEncodeWithSelector => "abiEncodeWithSelector"
  | .abiEncodeWithSignature => "abiEncodeWithSignature"
  | .abiEncodeCall => "abiEncodeCall"
  | .abiDecode => "abiDecode"
  | .typeBounds => "typeBounds"
  | .typeName => "typeName"
  | .interfaceId => "interfaceId"
  | .functionSelector => "functionSelector"
  | .functionAddress => "functionAddress"
  | .errorEventSelector => "errorEventSelector"
  | .arrayLength => "arrayLength"
  | .arrayPush => "arrayPush"
  | .arrayPushReference => "arrayPushReference"
  | .arrayPop => "arrayPop"
  | .storageCopy => "storageCopy"
  | .memoryAliasing => "memoryAliasing"
  | .storageAliasing => "storageAliasing"
  | .deleteMappingTails => "deleteMappingTails"
  | .danglingReferences => "danglingReferences"
  | .transientState => "transientState"
  | .checkedArithmetic => "checkedArithmetic"
  | .uncheckedArithmetic => "uncheckedArithmetic"
  | .evaluationOrder => "evaluationOrder"
  | .exactConstants => "exactConstants"
  | .defaultInitialization => "defaultInitialization"
  | .referenceCopyRules => "referenceCopyRules"
  | .panicCodes => "panicCodes"
  | .revertPayloads => "revertPayloads"
  | .rollback => "rollback"
  | .abiEntryValidation => "abiEntryValidation"
  | .constructorLifetime => "constructorLifetime"
  | .nonpayableEntry => "nonpayableEntry"
  | .staticCallRestriction => "staticCallRestriction"
  | .termination => "termination"
  | .worldAssumptions => "worldAssumptions"
  | .typeValidation => "typeValidation"
  | .featureDetection => "featureDetection"
  | .inlineAssembly => "inlineAssembly"
  | .gasleft => "gasleft"
  | .gasOption => "gasOption"
  | .rawCalldata => "rawCalldata"
  | .rawReturndata => "rawReturndata"
  | .lowLevelCall => "lowLevelCall"
  | .delegatecall => "delegatecall"
  | .lowLevelStaticcall => "lowLevelStaticcall"
  | .selfdestruct => "selfdestruct"
  | .create2Salt => "create2Salt"
  | .addressCode => "addressCode"
  | .addressCodehash => "addressCodehash"
  | .creationCode => "creationCode"
  | .runtimeCode => "runtimeCode"
  | .logicalStorageBase => "logicalStorageBase"
  | .storageLayout => "storageLayout"
  | .memoryLayout => "memoryLayout"
  | .transientLayout => "transientLayout"
  | .eventLog => "eventLog"
  | .machineResources => "machineResources"
  | .fixedPoint => "fixedPoint"
  | .removedAliases => "removedAliases"
  | .unsignedRightShift => "unsignedRightShift"
  | .removedUnits => "removedUnits"
  | .reservedKeywords => "reservedKeywords"
  | .invalidLexemes => "invalidLexemes"
  | .removedGenericSolidity => "removedGenericSolidity"
  | .invalidModifierBody => "invalidModifierBody"

def Feature.scope : Feature → Scope
  | .identifiers => .model
  | .comments => .model
  | .numericLiterals => .model
  | .booleanLiterals => .model
  | .stringLiterals => .model
  | .unicodeLiterals => .model
  | .hexLiterals => .model
  | .addressLiterals => .model
  | .etherUnits => .model
  | .timeUnits => .model
  | .pragmaVersion => .model
  | .pragmaAbicoder => .model
  | .pragmaOther => .model
  | .sourceUnits => .model
  | .imports => .model
  | .contracts => .model
  | .interfaces => .model
  | .libraries => .model
  | .inheritance => .model
  | .overrideDeclarations => .model
  | .functions => .model
  | .freeFunctions => .model
  | .constructors => .model
  | .modifiers => .model
  | .modifierPlaceholder => .model
  | .receiveFunction => .model
  | .fallbackFunction => .model
  | .visibility => .model
  | .stateMutability => .model
  | .stateVariables => .model
  | .constants => .model
  | .immutables => .model
  | .publicGetters => .model
  | .structDeclarations => .model
  | .enumDeclarations => .model
  | .valueTypeDeclarations => .model
  | .errorDeclarations => .model
  | .eventDeclarations => .model
  | .usingFor => .model
  | .operatorAliases => .model
  | .boolType => .model
  | .integerTypes => .model
  | .addressTypes => .model
  | .fixedBytesTypes => .model
  | .dynamicBytesType => .model
  | .stringType => .model
  | .dynamicArrays => .model
  | .fixedArrays => .model
  | .mappings => .model
  | .structTypes => .model
  | .enumTypes => .model
  | .valueTypes => .model
  | .internalFunctionTypes => .model
  | .externalFunctionTypes => .abstract
  | .tupleTypes => .model
  | .storageLocation => .model
  | .memoryLocation => .model
  | .calldataLocation => .model
  | .recursiveTypes => .model
  | .names => .model
  | .parentheses => .model
  | .tupleExpressions => .model
  | .inlineArrays => .model
  | .memberAccess => .model
  | .indexAccess => .model
  | .rangeAccess => .model
  | .unaryArithmetic => .model
  | .increments => .model
  | .deleteExpression => .model
  | .arithmetic => .model
  | .bitwise => .model
  | .shifts => .model
  | .comparisons => .model
  | .shortCircuit => .model
  | .conditional => .model
  | .assignment => .model
  | .compoundAssignment => .model
  | .explicitConversions => .model
  | .implicitConversions => .model
  | .structConstruction => .model
  | .namedArguments => .model
  | .newMemory => .model
  | .functionCalls => .model
  | .callOptions => .model
  | .metaTypeExpression => .model
  | .blocks => .model
  | .uncheckedBlock => .model
  | .variableDeclarations => .model
  | .expressionStatements => .model
  | .ifStatement => .model
  | .whileStatement => .model
  | .forStatement => .model
  | .doWhileStatement => .model
  | .breakStatement => .model
  | .continueStatement => .model
  | .returnStatement => .model
  | .tryStatement => .abstract
  | .catchClauses => .model
  | .revertStatement => .model
  | .emitStatement => .model
  | .canonicalRethrow => .abstract
  | .assertBuiltin => .model
  | .requireBuiltin => .model
  | .revertBuiltin => .model
  | .addmodBuiltin => .model
  | .mulmodBuiltin => .model
  | .keccakBuiltin => .abstract
  | .sha256Builtin => .abstract
  | .ripemd160Builtin => .abstract
  | .ecrecoverBuiltin => .abstract
  | .erc7201Builtin => .model
  | .wrapUnwrap => .model
  | .bytesConcat => .model
  | .stringConcat => .model
  | .msgSender => .abstract
  | .msgValue => .abstract
  | .thisAddress => .abstract
  | .addressBalance => .abstract
  | .blockTimestamp => .abstract
  | .blockCoinbase => .exclude
  | .blockDifficulty => .exclude
  | .blockPrevrandao => .exclude
  | .blockNumber => .exclude
  | .blockGaslimit => .exclude
  | .blockChainid => .exclude
  | .blockBasefee => .exclude
  | .blockBlobbasefee => .exclude
  | .blockSlotnum => .exclude
  | .txOrigin => .exclude
  | .txGasprice => .exclude
  | .blockhashBuiltin => .exclude
  | .blobhashBuiltin => .exclude
  | .internalCalls => .model
  | .recursiveCalls => .model
  | .externalTypedCalls => .abstract
  | .externalSelfCalls => .model
  | .extensionCalls => .model
  | .functionValues => .model
  | .valueOption => .model
  | .sendTransfer => .abstract
  | .emptyDataValueCall => .abstract
  | .newContract => .abstract
  | .creationTry => .abstract
  | .callbackSemantics => .abstract
  | .externalLibraryCalls => .abstract
  | .abiEncode => .model
  | .abiEncodePacked => .model
  | .abiEncodeWithSelector => .model
  | .abiEncodeWithSignature => .model
  | .abiEncodeCall => .model
  | .abiDecode => .model
  | .typeBounds => .model
  | .typeName => .model
  | .interfaceId => .model
  | .functionSelector => .model
  | .functionAddress => .model
  | .errorEventSelector => .model
  | .arrayLength => .model
  | .arrayPush => .model
  | .arrayPushReference => .model
  | .arrayPop => .model
  | .storageCopy => .model
  | .memoryAliasing => .model
  | .storageAliasing => .model
  | .deleteMappingTails => .model
  | .danglingReferences => .model
  | .transientState => .model
  | .checkedArithmetic => .model
  | .uncheckedArithmetic => .model
  | .evaluationOrder => .model
  | .exactConstants => .model
  | .defaultInitialization => .model
  | .referenceCopyRules => .model
  | .panicCodes => .model
  | .revertPayloads => .model
  | .rollback => .model
  | .abiEntryValidation => .abstract
  | .constructorLifetime => .abstract
  | .nonpayableEntry => .model
  | .staticCallRestriction => .abstract
  | .termination => .model
  | .worldAssumptions => .abstract
  | .typeValidation => .model
  | .featureDetection => .model
  | .inlineAssembly => .exclude
  | .gasleft => .exclude
  | .gasOption => .exclude
  | .rawCalldata => .exclude
  | .rawReturndata => .exclude
  | .lowLevelCall => .exclude
  | .delegatecall => .exclude
  | .lowLevelStaticcall => .exclude
  | .selfdestruct => .exclude
  | .create2Salt => .exclude
  | .addressCode => .exclude
  | .addressCodehash => .exclude
  | .creationCode => .model
  | .runtimeCode => .model
  | .logicalStorageBase => .model
  | .storageLayout => .exclude
  | .memoryLayout => .exclude
  | .transientLayout => .exclude
  | .eventLog => .exclude
  | .machineResources => .exclude
  | .fixedPoint => .model
  | .removedAliases => .upstream
  | .unsignedRightShift => .upstream
  | .removedUnits => .upstream
  | .reservedKeywords => .upstream
  | .invalidLexemes => .upstream
  | .removedGenericSolidity => .upstream
  | .invalidModifierBody => .upstream

def Feature.requirement : Feature → String
  | .identifiers => r#"Preserve declaration identity, lexical scope, shadowing and qualified names; builtin spelling alone is insufficient."#
  | .comments => r#"Ignore ordinary comments after lexing; preserve source spans and requested specification annotations; NatSpec is not executable Solidity."#
  | .numericLiterals => r#"Fold exact arbitrary-precision rationals before contextual integer typing; reject invalid denominators and out-of-range conversions."#
  | .booleanLiterals => r#"Produce Boolean values, without numeric implicit coercion."#
  | .stringLiterals => r#"Decode bytes and escapes; concatenate adjacent literals; enforce Solidity literal conversions rather than host string semantics."#
  | .unicodeLiterals => r#"Validate UTF-8 at compile time and retain the resulting bytes."#
  | .hexLiterals => r#"Decode exact byte sequences, including empty values and separators allowed upstream."#
  | .addressLiterals => r#"Enforce address-literal length/checksum and 160-bit bounds; distinguish numeric literals and addresses."#
  | .etherUnits => r#"Multiply literals by exact powers of ten before range checking; denominations do not create a runtime currency type."#
  | .timeUnits => r#"Fold literal unit factors; do not infer real-world clock guarantees or calendar arithmetic."#
  | .pragmaVersion => r#"Check the selected compiler/version range before importing a validated AST; record the compiler version."#
  | .pragmaAbicoder => r#"Record ABI-coder selection and its validation restrictions; do not silently apply v2 to a v1 compilation."#
  | .pragmaOther => r#"Delegate acceptance to pinned solc and reject unknown enabled language modes; compiler settings are part of provenance."#
  | .sourceUnits => r#"Preserve file-level namespaces and all reachable declaration identities across the compilation unit."#
  | .imports => r#"Resolve imports/remappings in solc; preserve qualified references and declaration IDs in the importer."#
  | .contracts => r#"Distinguish deployable and abstract contracts, initialization and declared member visibility."#
  | .interfaces => r#"Preserve external signatures, inherited interface members and the absence of implementation bodies."#
  | .libraries => r#"Inline resolvable pure/internal library calls; externally linked library execution additionally requires an explicit world/storage-context abstraction."#
  | .inheritance => r#"Follow solc C3 linearization, virtual dispatch and base initialization order; do not flatten solely by source name."#
  | .overrideDeclarations => r#"Validate overrides in solc, retain distinct base bodies and the selected implementation, and use retained source ABI identities for renamed inherited/overloaded external function values. Native/source type-erasure collisions remain refused."#
  | .functions => r#"Preserve parameter/return order, named return defaults, overload resolution, implicit return and visibility."#
  | .freeFunctions => r#"Resolve free and imported functions by declaration identity; model them without an implicit contract receiver."#
  | .constructors => r#"Run state initializers and base constructors exactly once in compiler order; handle payments and rollback."#
  | .modifiers => r#"Evaluate arguments and nest pre/body/post execution in source application order, including return/revert interactions."#
  | .modifierPlaceholder => r#"Invoke the modified continuation at each executed placeholder, preserving nesting and returns. A concrete modifier body must contain a placeholder, and a placeholder cannot be inside unchecked; a conditional placeholder can skip the body dynamically. Abstract modifier declarations have no body."#
  | .receiveFunction => r#"Own receive behavior is retained. Selected inherited receive bodies are registered for empty-data self value calls in C3 order, with sender/value framing and failure rollback. Newly registered stipend, modifier and helper-frame paths remain explicitly refused."#
  | .fallbackFunction => r#"A selected no-argument payable fallback supplies modeled empty-data self value calls only when the entire C3 lineage has no receive. Nonpayable, byte-oriented, modifier/helper-frame and stipend paths retain explicit refusals; arbitrary raw calldata dispatch is not modeled."#
  | .visibility => r#"Enforce permitted calls/access and distinguish external entry from internal dispatch; public does not imply every call is external."#
  | .stateMutability => r#"Enforce static restrictions and payment entry guards; view alone does not prove other contracts preserve this contract's state."#
  | .stateVariables => r#"Give each logical root its declared type/default and execute initializers with correct visibility and declaration ordering."#
  | .constants => r#"Evaluate supported constants by declaration identity; preserve contextual width and reject unsupported constant expressions."#
  | .immutables => r#"Enforce constructor initialization/read rules and retain the value across transactions; representing it as a logical root must not allow later writes."#
  | .publicGetters => r#"Primitive/UDVT, enum and contract-valued getter results, nominal mapping keys, interface overrides and exact struct array/mapping omissions are executable. Reference/function results and general reference-valued external return frames remain refused; nominal getter function-value signatures stay conservative refusals."#
  | .structDeclarations => r#"Preserve member identity/order, recursive legality and storage/memory compatibility; recursive shapes remain an implementation task."#
  | .enumDeclarations => r#"Preserve distinct enum identity, ordinals, min/max and runtime conversion checks."#
  | .valueTypeDeclarations => r#"Keep source nominal identity for type checking; lower only after preserving underlying signedness/width and wrap/unwrap rules."#
  | .errorDeclarations => r#"Preserve signature, selector and argument evaluation/encoding for custom errors, including qualified declarations."#
  | .eventDeclarations => r#"Preserve declaration and indexed/anonymous metadata; argument evaluation belongs to the model, log observation is separately excluded."#
  | .usingFor => r#"Resolve extension calls by solc identity and bind the receiver once; global applicability is lexical/type-specific."#
  | .operatorAliases => r#"Resolved scalar UDVT aliases lower to their compiler-selected pure free functions across the permitted unary and binary operator signatures, retaining nominal identity and evaluation order. Broader aggregate/source combinations remain subject to explicit admission limits."#
  | .boolType => r#"Keep Boolean typing distinct from integers and ABI words."#
  | .integerTypes => r#"Track width and signedness at every nested type position and intermediate operation; aliases mean 256 bits."#
  | .addressTypes => r#"Use bounded 160-bit identities and validate payable conversion rules before erasure to the logical address representation."#
  | .fixedBytesTypes => r#"Track byte length, indexing, padding, alignment, bitwise operations and explicit conversions."#
  | .dynamicBytesType => r#"Treat as byte array with Solidity storage/memory/calldata restrictions and exact copying behavior."#
  | .stringType => r#"Model byte content and explicit conversions; string has no direct indexing or length member."#
  | .dynamicArrays => r#"Track runtime lengths, bounds, reference element types and source-dependent assignment/copy behavior."#
  | .fixedArrays => r#"Evaluate constant lengths and retain lengths in types; preserve element bounds and ABI restrictions."#
  | .mappings => r#"Model allowed key types, default values, nested mappings and named getter components without pretending the map is enumerable."#
  | .structTypes => r#"Retain declaration identity and recursive graph restrictions; independently validate storage and memory uses."#
  | .enumTypes => r#"Preserve enum membership ranges in conversions and ABI entry values."#
  | .valueTypes => r#"Erase wrappers only after solc nominal checks and operator resolution, retaining exact primitive shape."#
  | .internalFunctionTypes => r#"Model declaration identities/dispatch tables and uninitialized-function failure, not machine jump addresses."#
  | .externalFunctionTypes => r#"Represent target address plus typed function identity/selector and an explicit external-call relation; no raw code pointers."#
  | .tupleTypes => r#"Preserve simultaneous assignment and evaluation/capture order; tuples are not independently declarable Solidity variable types."#
  | .storageLocation => r#"Represent typed logical paths; distinguish binding a reference, copying an aggregate and mutating its target."#
  | .memoryLocation => r#"Preserve heap object identity, aliasing, allocation and copy boundaries across calls."#
  | .calldataLocation => r#"Model immutable typed views and bounds; typed calldata does not require exposing msg.data or physical ABI offsets."#
  | .recursiveTypes => r#"Ordinary solc_import, scoped syntax, State, heap and calculus still reject recursive structs. A standalone typed graph-storage/copy foundation and ordinary-value bridge exist; connecting them to the ordinary source pipeline remains missing, not an EVM exclusion."#
  | .names => r#"Resolve declarations, distinguish locals/state/type members and retain selected base implementations."#
  | .parentheses => r#"Preserve grouping without introducing a tuple or changing evaluation."#
  | .tupleExpressions => r#"Capture all components once and commit assignments in Solidity order, preserving empty targets."#
  | .inlineArrays => r#"Infer the fixed memory array independently of its target using the first mobile element type and implicit common types; preserve allocation and element-copy timing. Nominal element identities and recursive shapes remain partial."#
  | .memberAccess => r#"Distinguish fields, builtins, type members and extension methods using resolved types/declarations."#
  | .indexAccess => r#"Check bounds for arrays/bytes; use key-type conversion for mappings; capture side effects once."#
  | .rangeAccess => r#"Model legal calldata views with zero-based derived lengths, endpoint checks and shared immutable content."#
  | .unaryArithmetic => r#"Respect width/signedness, Boolean negation and checked minimum-integer negation; no unary numeric plus exists."#
  | .increments => r#"Preserve lvalue evaluation once, old/new result and overflow mode; Lean spelling of decrement differs only at its parser boundary."#
  | .deleteExpression => r#"Reset the target according to its type; mappings inside aggregates retain inaccessible historical entries where Solidity does."#
  | .arithmetic => r#"Apply Solidity typing/overflow and signed division/remainder; exponentiation is right associative and division by zero always fails."#
  | .bitwise => r#"Operate over finite-width representations and preserve bytesN versus integer typing."#
  | .shifts => r#"Preserve left operand type; signed right shift sign-extends; shifts do not gain checked-arithmetic overflow guards."#
  | .comparisons => r#"Admit only comparisons supported by Solidity types; do not invent structural equality on arrays/structs."#
  | .shortCircuit => r#"Evaluate the second operand only when required and preserve failures/side effects in the first."#
  | .conditional => r#"Evaluate only one arm and preserve the conditional's inferred/mobile type, including reference-valued arms."#
  | .assignment => r#"Preserve lvalue/rvalue scheduling and reference-versus-copy semantics; the assigned value is also an expression result where legal."#
  | .compoundAssignment => r#"Capture the target once, read the old value at the proper point and use its declared arithmetic width."#
  | .explicitConversions => r#"Preserve Solidity legality, truncation, sign extension, bytesN alignment and enum checks; casts differ from checked arithmetic."#
  | .implicitConversions => r#"Use solc's resolved type, preserving widths before enclosing operations rather than only at assignment."#
  | .structConstruction => r#"Evaluate arguments in the selected compiler order, use field declaration order and allocate correct memory objects."#
  | .namedArguments => r#"Bind by formal name while preserving actual compiler evaluation order; do not assume textual object order."#
  | .newMemory => r#"Allocate fresh defaulted memory, check feasible lengths and preserve allocation failure as a distinct concern from mathematical unboundedness."#
  | .functionCalls => r#"Evaluate callee/receiver and every argument exactly once before entering a fresh call frame."#
  | .callOptions => r#"Split options by semantic demand: value is modeled, gas is excluded, salt is excluded; a generic options node is not automatically admissible."#
  | .metaTypeExpression => r#"Resolve only integer, enum or contract/interface metatypes accepted upstream; classify each accessed member separately."#
  | .blocks => r#"Allocate locals with Solidity lifetime, default initialization and shadowing; discard bindings when leaving the scope."#
  | .uncheckedBlock => r#"Wrap only applicable arithmetic in lexical scope; retain division/index checks and do not propagate unchecked into called functions."#
  | .variableDeclarations => r#"Preserve declaration identity, defaults, data location, inference constraints and initializer capture order."#
  | .expressionStatements => r#"Execute all effects and failures even when the resulting value is discarded."#
  | .ifStatement => r#"Evaluate a Boolean condition once and execute exactly one branch."#
  | .whileStatement => r#"Reevaluate condition and distinguish termination, revert, break, continue and divergence."#
  | .forStatement => r#"Handle omitted clauses, initializer scope and continue-through-post behavior."#
  | .doWhileStatement => r#"Execute body before condition and route continue to the condition."#
  | .breakStatement => r#"Exit only the innermost loop without evaluating its next condition/post."#
  | .continueStatement => r#"Continue the innermost loop with the correct post/condition destination."#
  | .returnStatement => r#"Capture return values/references and run enclosing modifier continuations with correct frame isolation."#
  | .tryStatement => r#"Separate callee failure from caller argument/return-decoding failures; typed contract creation needs the world abstraction."#
  | .catchClauses => r#"Dispatch by valid revert bytes, handle malformed payloads and preserve caller/callee rollback boundaries."#
  | .revertStatement => r#"Evaluate payload arguments and roll back the correct frame; retain exact bytes where supported and document proof-logic precision limits."#
  | .emitStatement => r#"Evaluate every argument for effects/reverts before erasing the unobserved log; erasure is valid only for properties that do not observe logs."#
  | .canonicalRethrow => r#"Recognize only the verified whole-buffer pattern with matching resolved declarations; lower to raw rethrow, never admit general Yul by this exception."#
  | .assertBuiltin => r#"False raises Panic(0x01); distinguish failure from assumptions and from ordinary require failure."#
  | .requireBuiltin => r#"Evaluate all arguments even if the condition succeeds; retain Error/custom-error encoding and rollback."#
  | .revertBuiltin => r#"Preserve computed reasons and evaluation failures; do not replace revert by a proof assumption."#
  | .addmodBuiltin => r#"Compute with arbitrary-precision intermediate addition; reject a constant zero modulus and fail with Panic(0x12) for a dynamic zero modulus. Raw EVM opcode zero behavior is not Solidity builtin behavior."#
  | .mulmodBuiltin => r#"Compute with arbitrary-precision intermediate multiplication; reject a constant zero modulus and fail with Panic(0x12) for a dynamic zero modulus. Raw EVM opcode zero behavior is not Solidity builtin behavior."#
  | .keccakBuiltin => r#"Use the existing Keccak semantics/explicit abstraction over bytes; injectivity and collision resistance are not unconditional equations."#
  | .sha256Builtin => r#"Use an explicit deterministic cryptographic interpretation; opaque axioms must not claim collision freedom."#
  | .ripemd160Builtin => r#"Preserve the 20-byte result and explicit interpretation independently of precompile gas."#
  | .ecrecoverBuiltin => r#"Computed bounded recovery validates v/r/s and returns zero on failure; concrete kernel/EVM vectors pass. General group-law and precompile-equivalence proofs remain open; signer authorization requires separate premises."#
  | .erc7201Builtin => r#"Evaluate the ERC-7201 namespace formula for runtime strings and constant-foldable inputs: hash the string bytes, subtract one modulo 2^256, hash the encoded word, and clear the low eight bits. Producing a namespace integer does not expose physical storage."#
  | .wrapUnwrap => r#"Preserve the exact underlying value and perform nominal checks before erasure; these are not arithmetic casts."#
  | .bytesConcat => r#"Concatenate exact bytes/bytesN in argument order with fresh result memory."#
  | .stringConcat => r#"Concatenate byte content, preserving argument evaluation and fresh allocation."#
  | .msgSender => r#"Supply a bounded caller identity per call frame; external self-calls change sender."#
  | .msgValue => r#"Supply per-frame payment with payable entry/ledger assumptions; callback/self-call frames may change the value."#
  | .thisAddress => r#"Supply a bounded deployment identity and distinguish the contract value from its external call dispatch."#
  | .addressBalance => r#"Read an explicit ledger and state required balance/supply/world assumptions; arbitrary-address balances are not proved from chain execution."#
  | .blockTimestamp => r#"Read the environment timestamp; monotonicity, accuracy and miner constraints require explicit premises."#
  | .blockCoinbase => r#"This profile supplies only block.timestamp; coinbase requires an additional chain input and premises (feasible in another profile), not an invented constant. Fork gating remains solc's responsibility."#
  | .blockDifficulty => r#"This profile supplies only block.timestamp; difficulty requires an additional chain input and premises (feasible in another profile), not an invented constant. Fork gating remains solc's responsibility."#
  | .blockPrevrandao => r#"This profile supplies only block.timestamp; prevrandao requires an additional chain input and premises (feasible in another profile), not an invented constant. Fork gating remains solc's responsibility."#
  | .blockNumber => r#"This profile supplies only block.timestamp; number requires an additional chain input and premises (feasible in another profile), not an invented constant. Fork gating remains solc's responsibility."#
  | .blockGaslimit => r#"This profile supplies only block.timestamp; gaslimit requires an additional chain input and premises (feasible in another profile), not an invented constant. Fork gating remains solc's responsibility."#
  | .blockChainid => r#"This profile supplies only block.timestamp; chainid requires an additional chain input and premises (feasible in another profile), not an invented constant. Fork gating remains solc's responsibility."#
  | .blockBasefee => r#"This profile supplies only block.timestamp; basefee requires an additional chain input and premises (feasible in another profile), not an invented constant. Fork gating remains solc's responsibility."#
  | .blockBlobbasefee => r#"This profile supplies only block.timestamp; blobbasefee requires an additional chain input and premises (feasible in another profile), not an invented constant. Fork gating remains solc's responsibility."#
  | .blockSlotnum => r#"This profile supplies only block.timestamp; slotnum requires an additional chain input and premises (feasible in another profile), not an invented constant. Fork gating remains solc's responsibility."#
  | .txOrigin => r#"Transaction-origin identity is not carried by the current call environment; it must not be replaced by msg.sender."#
  | .txGasprice => r#"Transaction pricing lies outside the chosen functional environment and gas abstraction."#
  | .blockhashBuiltin => r#"Requires chain history, fork rules and the bounded block-hash window absent from this profile."#
  | .blobhashBuiltin => r#"Requires transaction blob metadata and fork rules absent from this profile."#
  | .internalCalls => r#"Use resolved implementation identity and fresh frames; preserve return/default/reference values and modifier continuations."#
  | .recursiveCalls => r#"Model recursion/frame exhaustion explicitly; the existing bounded call implementation is not unbounded mathematical recursion."#
  | .externalTypedCalls => r#"Use typed inputs/outcomes, payment/rollback and a documented external-call relation; arbitrary external code is not proved by the local interpreter."#
  | .externalSelfCalls => r#"Run a distinct external frame with sender=this, value, return ABI validation and local-state rollback behavior."#
  | .extensionCalls => r#"Bind receiver once and lower to the resolved function; external library calls require their own world/storage abstraction."#
  | .functionValues => r#"Preserve Solidity identity rules, compatible signatures and failure for unset internal function values; avoid code-address equality assumptions."#
  | .valueOption => r#"Evaluate amount and update ledger on success with rollback on failure, respecting payable and self-call semantics."#
  | .sendTransfer => r#"Model success/failure, transfer's revert behavior and payment effects; callback exclusion is an explicit selected assumption, not a timeless gas theorem."#
  | .emptyDataValueCall => r#"Admit only the recognized empty-payload payment form, discard unread return bytes and allow callbacks under the chosen call semantics."#
  | .newContract => r#"Typed catalog world allocation, constructor execution, payment and rollback exist, with restricted solc_world_factory source fragments. General source new C with dynamic arguments, ABI/memory transfer, callbacks and composed worlds remains unintegrated. Existing source wrappers now emit exact world-operation certificates and conditional funded Reachable bridges; general source shapes remain partial."#
  | .creationTry => r#"Typed world creation outcomes and restricted factory source try-new fragments preserve the creation-frame catch boundary; caller argument failures stay outside it. General typed catches and source-world composition remain unsupported. The narrow stateless unpaid Error(string) source continuation now compiles actual local arguments, constructor/handle and caller branches; its conditional kernel correspondence and original creation fixture replay do not establish general world/source or callback validity. Existing source wrappers also emit exact world-operation certificates and conditional funded Reachable bridges; general source shapes remain partial."#
  | .callbackSemantics => r#"Select and record ordinary versus callback modality; state frame guarantees and callback invariants explicitly."#
  | .externalLibraryCalls => r#"Typed linked execution uses caller storage and explicit library identity, with restricted solc_world_library literal field-mutation fragments. General library arguments, aggregate returns and nested external source execution remain unsupported. Existing source wrappers now emit exact world-operation certificates and conditional funded Reachable bridges; general source shapes remain partial."#
  | .abiEncode => r#"Implement canonical head/tail, offsets, padding and recursive value shapes; current supported shape is narrower than all Solidity ABI types."#
  | .abiEncodePacked => r#"Preserve packed widths and array restrictions; ambiguity/collisions of packed encodings are real and must not be erased."#
  | .abiEncodeWithSelector => r#"Prefix a selector to canonical encoding; selector bytes are data, independent of raw CALL support. Existing selector-prefix lowering supports restricted argument shapes; complete recursive ABI shape coverage remains to be established."#
  | .abiEncodeWithSignature => r#"Derive bytes4(keccak256(signature)) then canonical encoding; do not assert hashes are injective. Existing selector-prefix lowering supports restricted argument shapes; complete recursive ABI shape coverage remains to be established."#
  | .abiEncodeCall => r#"Check exact function/tuple compatibility, derive selector and encode typed arguments. Existing selector-prefix lowering supports restricted argument shapes; complete recursive ABI shape coverage remains to be established."#
  | .abiDecode => r#"Validate offsets, lengths, ranges, truncation and fixed-byte padding before traversal/allocation; preserve noncanonical unaligned and overlapping layouts that solc accepts. Nominal enum metadata and complete recursive ABI coverage remain partial."#
  | .typeBounds => r#"Produce exact source-type bounds, including enum cardinality and signed minimum."#
  | .typeName => r#"Return compiler-resolved contract name bytes as a compile-time value."#
  | .interfaceId => r#"Compute the XOR of the interface's own external function selectors according to Solidity rules; inherited functions are excluded."#
  | .functionSelector => r#"Preserve canonical signature and four-byte selector without exposing code addresses or asserting uniqueness. Existing lowering handles modeled external function values; all declaration contexts still need validation."#
  | .functionAddress => r#"Project the bounded receiver identity from an external function value. Existing lowering handles modeled external function values; all declaration contexts still need validation."#
  | .errorEventSelector => r#"Compute bytes4 for error signatures and bytes32 for non-anonymous event signatures, respecting solc declaration resolution; anonymous events have no selector member."#
  | .arrayLength => r#"Return exact length with correct static/dynamic location restrictions; string requires an explicit bytes conversion."#
  | .arrayPush => r#"Evaluate receiver and source in compiler order, grow length, initialize/copy the new element and preserve aliases."#
  | .arrayPushReference => r#"Append a default value and return a storage lvalue/reference; nested member effects must occur in compiler order."#
  | .arrayPop => r#"Fail on empty, shorten length and clear the element according to Solidity mapping-tail rules."#
  | .storageCopy => r#"Deep-copy value content with destination cleanup and correct overlapping/alias behavior; mapping members are not naively copied."#
  | .memoryAliasing => r#"Share object identity where Solidity aliases; external ABI boundaries copy and storage-to-memory creates fresh objects."#
  | .storageAliasing => r#"Rebinding a reference differs from writing its target; represent nested fields and indices without physical slot numbers."#
  | .deleteMappingTails => r#"Preserve mapping entries where Solidity does, and record clean-tail assumptions/selected semantics rather than hiding them."#
  | .danglingReferences => r#"Preserve the chosen Solidity/compiler semantics or reject affected programs explicitly; safe-path assumptions need premises."#
  | .transientState => r#"Typed primitive and established signature-marked function-tag source declarations use disjoint regions of the joint logical root product; nested self-calls share cells and failure rolls back the product. Closed source factory targets may contain certified transient roots; typed compositions of imported frames use an explicit outer World.transact boundary with per-owner reset and full rollback. General source-world statement lowering, transient factory owners, physical layout, raw tload/tstore and raw function addresses remain unsupported."#
  | .checkedArithmetic => r#"Guard every operation at its intermediate width, signedness and overflow mode, including values used only by conditions."#
  | .uncheckedArithmetic => r#"Wrap at each operation's width; zero division and invalid indexing still fail and called functions retain their own lexical mode."#
  | .evaluationOrder => r#"Record the selected compiler pipeline; do not impose a single source-order guarantee where Solidity leaves order unspecified."#
  | .exactConstants => r#"Evaluate exact rationals and contextual/mobile literal types before runtime integer operations."#
  | .defaultInitialization => r#"Default according to complete type and location; unset storage references and function values have special restrictions/failure behavior."#
  | .referenceCopyRules => r#"Define every allowed location pair, reference binding versus deep copy, and nested element compatibility explicitly."#
  | .panicCodes => r#"Retain applicable Solidity panic codes and payloads; some current paths lose data, and malformed storage encoding 0x22 is tied to excluded low-level corruption."#
  | .revertPayloads => r#"Distinguish runtime byte precision from what the current proof modalities can observe; do not advertise exact computed-data proofs where unavailable."#
  | .rollback => r#"Roll back storage, transient state, ledger and outputs at the failing frame boundary while keeping caller state where Solidity does."#
  | .abiEntryValidation => r#"State caller assumptions and enforce ABI range/shape validation; malformed return decoding is a caller failure, not a caught callee revert."#
  | .constructorLifetime => r#"State which claims range over arbitrary typed states versus constructor-reachable traces and deployed instances."#
  | .nonpayableEntry => r#"Refuse nonzero msg.value at external entry without incorrectly restricting internal calls of the same declaration."#
  | .staticCallRestriction => r#"Model forbidden writes/payments in a static context, including transitive calls; source view checking alone does not capture arbitrary external behavior."#
  | .termination => r#"Keep semantic divergence separate from evaluator fuel and real EVM gas; total-correctness claims must state their termination premises."#
  | .worldAssumptions => r#"Carry chain premises and call/callback interpretation in the theorem; do not derive them from the single-contract store."#
  | .typeValidation => r#"Import only validated ASTs from the pinned compiler/settings; the catalog is not a replacement type checker."#
  | .featureDetection => r#"Collect features from initializers, modifiers, inherited bodies, callees, payloads, specifications and call options; reject unknown AST nodes instead of default admission."#
  | .inlineAssembly => r#"General Yul exposes machine memory, slots, opcodes and fork-dependent effects; only the separately recognized whole-buffer rethrow is abstracted."#
  | .gasleft => r#"Requires dynamic gas accounting, memory expansion, refunds and call forwarding absent from functional semantics."#
  | .gasOption => r#"An exact gas budget can change success, failure and reentrancy; it cannot be silently discarded."#
  | .rawCalldata => r#"This profile starts with typed arguments and lacks raw transaction payload/selector dispatch; typed calldata views remain in scope."#
  | .rawReturndata => r#"Exact arbitrary external return bytes and machine return-buffer behavior are outside typed external-call outcomes; caught revert bytes are separate."#
  | .lowLevelCall => r#"Arbitrary selector dispatch and byte-oriented external world effects exceed the recognized empty-data payment form."#
  | .delegatecall => r#"Arbitrary foreign code executes against caller storage and context; requires a code/world semantics beyond typed library abstractions."#
  | .lowLevelStaticcall => r#"Arbitrary byte-oriented dispatch/static-context return bytes require a richer external world than typed view calls."#
  | .selfdestruct => r#"Balance transfer, account deletion and creation-in-transaction exceptions depend on fork-specific world semantics."#
  | .create2Salt => r#"Address derivation requires init-code hashing and account/world collision rules absent from this profile."#
  | .addressCode => r#"Observes deployed bytecode/code size, including construction/deletion states, absent from the source interpreter."#
  | .addressCodehash => r#"Observes account existence and deployed bytecode hashing, absent from the source interpreter."#
  | .creationCode => r#"Static compiler code constants require matching exact compiler/source/settings artifacts; deployed account code, unresolved linking and oversized materialization are not supported."#
  | .runtimeCode => r#"Static compiler code constants require matching exact compiler/source/settings artifacts; deployed account code, unresolved linking and oversized materialization are not supported."#
  | .logicalStorageBase => r#"Accept compiler-validated literal storage bases only for logical typed root operations. Raw slots, offsets, packing, tload/tstore and assembly remain excluded; the base does not change declaration identities or the disjoint persistent/transient root partition."#
  | .storageLayout => r#"Logical typed paths intentionally omit slot arithmetic, packing and the physical storage address space."#
  | .memoryLayout => r#"Typed heap objects have no exposed machine byte addresses, expansion cost or scratch/free-memory regions."#
  | .transientLayout => r#"Logical transaction-local values can be modeled separately; physical transient slot access is a machine observation."#
  | .eventLog => r#"The selected observation model erases logs after evaluating arguments; properties about emitted logs require a new observable trace."#
  | .machineResources => r#"Mathematical execution/fuel bounds are not real gas or stack accounting; exact resource-sensitive outcomes need an EVM semantics."#
  | .fixedPoint => r#"Full fixed-point support beyond the acceptance boundary of pinned solc 0.8.38, which accepts some declarations such as `type T is fixed;` and reports UnimplementedFeatureError for most other uses: fixed/ufixed and fixedMxN/ufixedMxN declarations, literals, conversions and arithmetic need a reference semantics defined in this repository, since solc gives none. Nothing is implemented. Shifts on fixed-point operands stay rejected, as by solc (second-round decision, narrowing G00 Q6); the reference semantics follows the second-round fixed-point answers."#
  | .removedAliases => r#"Retained parser/AST/type entries receive upstream removal errors; report compiler invalidity before model scope diagnostics."#
  | .unsignedRightShift => r#"Lexer/ANTLR retain these tokens but Solidity's type system rejects the unsigned-right-shift operator."#
  | .removedUnits => r#"years is rejected by the type checker; removed historical units are not admitted by the modern compiler."#
  | .reservedKeywords => r#"Reserved lexer words are not executable language features; preserve compiler diagnostics and do not reinterpret them as identifiers."#
  | .invalidLexemes => r#"Scanned tokens without a Solidity parser production remain invalid source; recognizing a token does not admit a language construct."#
  | .removedGenericSolidity => r#"The experimental Generic Solidity language was removed in 0.8.37; it is not part of the pinned mainstream Solidity surface."#
  | .invalidModifierBody => r#"Pinned solc rejects concrete modifiers without any placeholder and placeholders nested inside unchecked blocks; an abstract modifier declaration without a body is legal."#

def Feature.all : List Feature :=
  [ .identifiers,
    .comments,
    .numericLiterals,
    .booleanLiterals,
    .stringLiterals,
    .unicodeLiterals,
    .hexLiterals,
    .addressLiterals,
    .etherUnits,
    .timeUnits,
    .pragmaVersion,
    .pragmaAbicoder,
    .pragmaOther,
    .sourceUnits,
    .imports,
    .contracts,
    .interfaces,
    .libraries,
    .inheritance,
    .overrideDeclarations,
    .functions,
    .freeFunctions,
    .constructors,
    .modifiers,
    .modifierPlaceholder,
    .receiveFunction,
    .fallbackFunction,
    .visibility,
    .stateMutability,
    .stateVariables,
    .constants,
    .immutables,
    .publicGetters,
    .structDeclarations,
    .enumDeclarations,
    .valueTypeDeclarations,
    .errorDeclarations,
    .eventDeclarations,
    .usingFor,
    .operatorAliases,
    .boolType,
    .integerTypes,
    .addressTypes,
    .fixedBytesTypes,
    .dynamicBytesType,
    .stringType,
    .dynamicArrays,
    .fixedArrays,
    .mappings,
    .structTypes,
    .enumTypes,
    .valueTypes,
    .internalFunctionTypes,
    .externalFunctionTypes,
    .tupleTypes,
    .storageLocation,
    .memoryLocation,
    .calldataLocation,
    .recursiveTypes,
    .names,
    .parentheses,
    .tupleExpressions,
    .inlineArrays,
    .memberAccess,
    .indexAccess,
    .rangeAccess,
    .unaryArithmetic,
    .increments,
    .deleteExpression,
    .arithmetic,
    .bitwise,
    .shifts,
    .comparisons,
    .shortCircuit,
    .conditional,
    .assignment,
    .compoundAssignment,
    .explicitConversions,
    .implicitConversions,
    .structConstruction,
    .namedArguments,
    .newMemory,
    .functionCalls,
    .callOptions,
    .metaTypeExpression,
    .blocks,
    .uncheckedBlock,
    .variableDeclarations,
    .expressionStatements,
    .ifStatement,
    .whileStatement,
    .forStatement,
    .doWhileStatement,
    .breakStatement,
    .continueStatement,
    .returnStatement,
    .tryStatement,
    .catchClauses,
    .revertStatement,
    .emitStatement,
    .canonicalRethrow,
    .assertBuiltin,
    .requireBuiltin,
    .revertBuiltin,
    .addmodBuiltin,
    .mulmodBuiltin,
    .keccakBuiltin,
    .sha256Builtin,
    .ripemd160Builtin,
    .ecrecoverBuiltin,
    .erc7201Builtin,
    .wrapUnwrap,
    .bytesConcat,
    .stringConcat,
    .msgSender,
    .msgValue,
    .thisAddress,
    .addressBalance,
    .blockTimestamp,
    .blockCoinbase,
    .blockDifficulty,
    .blockPrevrandao,
    .blockNumber,
    .blockGaslimit,
    .blockChainid,
    .blockBasefee,
    .blockBlobbasefee,
    .blockSlotnum,
    .txOrigin,
    .txGasprice,
    .blockhashBuiltin,
    .blobhashBuiltin,
    .internalCalls,
    .recursiveCalls,
    .externalTypedCalls,
    .externalSelfCalls,
    .extensionCalls,
    .functionValues,
    .valueOption,
    .sendTransfer,
    .emptyDataValueCall,
    .newContract,
    .creationTry,
    .callbackSemantics,
    .externalLibraryCalls,
    .abiEncode,
    .abiEncodePacked,
    .abiEncodeWithSelector,
    .abiEncodeWithSignature,
    .abiEncodeCall,
    .abiDecode,
    .typeBounds,
    .typeName,
    .interfaceId,
    .functionSelector,
    .functionAddress,
    .errorEventSelector,
    .arrayLength,
    .arrayPush,
    .arrayPushReference,
    .arrayPop,
    .storageCopy,
    .memoryAliasing,
    .storageAliasing,
    .deleteMappingTails,
    .danglingReferences,
    .transientState,
    .checkedArithmetic,
    .uncheckedArithmetic,
    .evaluationOrder,
    .exactConstants,
    .defaultInitialization,
    .referenceCopyRules,
    .panicCodes,
    .revertPayloads,
    .rollback,
    .abiEntryValidation,
    .constructorLifetime,
    .nonpayableEntry,
    .staticCallRestriction,
    .termination,
    .worldAssumptions,
    .typeValidation,
    .featureDetection,
    .inlineAssembly,
    .gasleft,
    .gasOption,
    .rawCalldata,
    .rawReturndata,
    .lowLevelCall,
    .delegatecall,
    .lowLevelStaticcall,
    .selfdestruct,
    .create2Salt,
    .addressCode,
    .addressCodehash,
    .creationCode,
    .runtimeCode,
    .logicalStorageBase,
    .storageLayout,
    .memoryLayout,
    .transientLayout,
    .eventLog,
    .machineResources,
    .fixedPoint,
    .removedAliases,
    .unsignedRightShift,
    .removedUnits,
    .reservedKeywords,
    .invalidLexemes,
    .removedGenericSolidity,
    .invalidModifierBody ]

/-- The catalog list enumerates the entire feature type. -/
theorem Feature.all_complete (f : Feature) : f ∈ Feature.all := by
  cases f <;> decide

/-- Fields excluded by this profile; timestamp is intentionally absent. -/
inductive BlockField where
  | coinbase
  | difficulty
  | prevrandao
  | number
  | gaslimit
  | chainid
  | basefee
  | blobbasefee
  | slotnum
  deriving Repr, DecidableEq, Inhabited

def BlockField.id : BlockField → String
  | .coinbase => "coinbase"
  | .difficulty => "difficulty"
  | .prevrandao => "prevrandao"
  | .number => "number"
  | .gaslimit => "gaslimit"
  | .chainid => "chainid"
  | .basefee => "basefee"
  | .blobbasefee => "blobbasefee"
  | .slotnum => "slotnum"

inductive Unmodelled where
  | blockField (field : BlockField)
  | txOrigin
  | txGasprice
  | blockhashBuiltin
  | blobhashBuiltin
  | inlineAssembly
  | gasleft
  | gasOption
  | rawCalldata
  | rawReturndata
  | lowLevelCall
  | delegatecall
  | lowLevelStaticcall
  | selfdestruct
  | create2Salt
  | addressCode
  | addressCodehash
  | storageLayout
  | memoryLayout
  | transientLayout
  | eventLog
  | machineResources
  deriving Repr, DecidableEq, Inhabited

def Unmodelled.feature : Unmodelled → Feature
  | .blockField .coinbase => .blockCoinbase
  | .blockField .difficulty => .blockDifficulty
  | .blockField .prevrandao => .blockPrevrandao
  | .blockField .number => .blockNumber
  | .blockField .gaslimit => .blockGaslimit
  | .blockField .chainid => .blockChainid
  | .blockField .basefee => .blockBasefee
  | .blockField .blobbasefee => .blockBlobbasefee
  | .blockField .slotnum => .blockSlotnum
  | .txOrigin => .txOrigin
  | .txGasprice => .txGasprice
  | .blockhashBuiltin => .blockhashBuiltin
  | .blobhashBuiltin => .blobhashBuiltin
  | .inlineAssembly => .inlineAssembly
  | .gasleft => .gasleft
  | .gasOption => .gasOption
  | .rawCalldata => .rawCalldata
  | .rawReturndata => .rawReturndata
  | .lowLevelCall => .lowLevelCall
  | .delegatecall => .delegatecall
  | .lowLevelStaticcall => .lowLevelStaticcall
  | .selfdestruct => .selfdestruct
  | .create2Salt => .create2Salt
  | .addressCode => .addressCode
  | .addressCodehash => .addressCodehash
  | .storageLayout => .storageLayout
  | .memoryLayout => .memoryLayout
  | .transientLayout => .transientLayout
  | .eventLog => .eventLog
  | .machineResources => .machineResources

def Unmodelled.reason (u : Unmodelled) : String := u.feature.requirement

def Unmodelled.errorName (u : Unmodelled) : Lean.Name :=
  match u with
  | .blockField f => .str (.str (.str .anonymous "solidity") "blockField") f.id
  | _ => .str (.str .anonymous "solidity") u.feature.id

def Feature.unmodelled? : Feature → Option Unmodelled
  | .blockCoinbase => some (.blockField .coinbase)
  | .blockDifficulty => some (.blockField .difficulty)
  | .blockPrevrandao => some (.blockField .prevrandao)
  | .blockNumber => some (.blockField .number)
  | .blockGaslimit => some (.blockField .gaslimit)
  | .blockChainid => some (.blockField .chainid)
  | .blockBasefee => some (.blockField .basefee)
  | .blockBlobbasefee => some (.blockField .blobbasefee)
  | .blockSlotnum => some (.blockField .slotnum)
  | .txOrigin => some .txOrigin
  | .txGasprice => some .txGasprice
  | .blockhashBuiltin => some .blockhashBuiltin
  | .blobhashBuiltin => some .blobhashBuiltin
  | .inlineAssembly => some .inlineAssembly
  | .gasleft => some .gasleft
  | .gasOption => some .gasOption
  | .rawCalldata => some .rawCalldata
  | .rawReturndata => some .rawReturndata
  | .lowLevelCall => some .lowLevelCall
  | .delegatecall => some .delegatecall
  | .lowLevelStaticcall => some .lowLevelStaticcall
  | .selfdestruct => some .selfdestruct
  | .create2Salt => some .create2Salt
  | .addressCode => some .addressCode
  | .addressCodehash => some .addressCodehash
  | .storageLayout => some .storageLayout
  | .memoryLayout => some .memoryLayout
  | .transientLayout => some .transientLayout
  | .eventLog => some .eventLog
  | .machineResources => some .machineResources
  | _ => none

def Unmodelled.all : List Unmodelled :=
  Feature.all.filterMap Feature.unmodelled?

def modelFeatures : List Feature :=
  Feature.all.filter fun f => f.scope == .model

def abstractFeatures : List Feature :=
  Feature.all.filter fun f => f.scope == .abstract

def targetFeatures : List Feature :=
  Feature.all.filter fun f => f.scope == .model || f.scope == .abstract

def outsideScope : List Unmodelled := Unmodelled.all

def rejectedByUpstream : List Feature :=
  Feature.all.filter fun f => f.scope == .upstream

def requirements : List (Feature × String) :=
  targetFeatures.map fun f => (f, f.requirement)

/-- A policy decision; no assertion of current implementation support. -/
def Feature.inProfile (f : Feature) : Prop :=
  f.scope = .model ∨ f.scope = .abstract

def WithinProfile (features : List Feature) : Prop :=
  ∀ f ∈ features, f.inProfile

/-- Restrict an actual syntax representation using a supplied feature extractor.
Completeness of `uses` must be established separately; this is not a fake full AST. -/
def ProfileSyntax (Syntax : Type u) (uses : Syntax → List Feature) : Type u :=
  { ast : Syntax // WithinProfile (uses ast) }

end Solidity.Language
