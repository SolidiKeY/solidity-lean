import Lean.Data.Name

/-!
# Solidity feature scope

Generated from docs/solidity-features.json by scripts/solidity-feature-audit.py.
The catalog classifies language features; it does not implement a Solidity parser,
a feature extractor, or a proof of frontend/solc equivalence. The subset wrapper
is meaningful only with a complete, declaration-aware feature extractor.
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

def Feature.info : Feature → FeatureInfo
  | .identifiers =>
    { category := "lexical", spelling := "identifiers; contextual from/error/revert/global/transient/layout/at",
      scope := .model, current := .limited,
      requirement := r#"Preserve declaration identity, lexical scope, shadowing and qualified names; builtin spelling alone is insufficient."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 428 }], localEvidence := ["Solidity/Frontend/SolcJson/Body.lean", "Solidity/Frontend/Source.lean", "Solidity/Frontend/SolcJson/Admission.lean", "Solidity/Examples/Tactics/SourceAdmissionImport.lean", "Solidity/Examples/Tactics/SourceLiteralsImport.lean", "Solidity/Examples/Tactics/SourceIdentifiersImport.lean", "docs/feature-work/source-admission.md", "Solidity/Frontend/SolcJson/Contract.lean", "tests/solc/Shadowing.sol", "scripts/source-shadowing.test.mjs", "docs/feature-work/dafny-verification.md"] }
  | .comments =>
    { category := "lexical", spelling := "// and /* */; NatSpec /// and /** */",
      scope := .model, current := .limited,
      requirement := r#"Ignore ordinary comments after lexing; preserve source spans and requested specification annotations; NatSpec is not executable Solidity."#,
      upstream := [{ path := "libsolidity/ast/AST.h", line := 443 }], localEvidence := ["Solidity/Frontend/SolcJson/Body.lean", "Solidity/Frontend/Source.lean", "Solidity/Frontend/SolcJson/Admission.lean", "Solidity/Examples/Tactics/SourceAdmissionImport.lean", "Solidity/Examples/Tactics/SourceLiteralsImport.lean", "Solidity/Examples/Tactics/SourceIdentifiersImport.lean", "docs/feature-work/source-admission.md"] }
  | .numericLiterals =>
    { category := "lexical", spelling := "decimal, hexadecimal, underscores, scientific notation, fractional literals",
      scope := .model, current := .limited,
      requirement := r#"Fold exact arbitrary-precision rationals before contextual integer typing; reject invalid denominators and out-of-range conversions."#,
      upstream := [{ path := "docs/grammar/SolidityLexer.g4", line := 240 }], localEvidence := ["Solidity/Frontend/SolcJson/Body.lean", "Solidity/Frontend/Source.lean", "Solidity/Frontend/SolcJson/Admission.lean", "Solidity/Examples/Tactics/SourceAdmissionImport.lean", "Solidity/Examples/Tactics/SourceLiteralsImport.lean", "Solidity/Examples/Tactics/SourceIdentifiersImport.lean", "docs/feature-work/source-admission.md"] }
  | .booleanLiterals =>
    { category := "lexical", spelling := "true; false",
      scope := .model, current := .present,
      requirement := r#"Produce Boolean values, without numeric implicit coercion."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 434 }], localEvidence := ["Solidity/Frontend/SolcJson/Body.lean"] }
  | .stringLiterals =>
    { category := "lexical", spelling := "single/double quotes, escapes, adjacent strings",
      scope := .model, current := .limited,
      requirement := r#"Decode bytes and escapes; concatenate adjacent literals; enforce Solidity literal conversions rather than host string semantics."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 438 }], localEvidence := ["Solidity/Frontend/SolcJson/Body.lean", "Solidity/Frontend/Source.lean", "Solidity/Frontend/SolcJson/Admission.lean", "Solidity/Examples/Tactics/SourceAdmissionImport.lean", "Solidity/Examples/Tactics/SourceLiteralsImport.lean", "Solidity/Examples/Tactics/SourceIdentifiersImport.lean", "docs/feature-work/source-admission.md"] }
  | .unicodeLiterals =>
    { category := "lexical", spelling := "unicode\"...\"",
      scope := .model, current := .limited,
      requirement := r#"Validate UTF-8 at compile time and retain the resulting bytes."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 446 }], localEvidence := ["Solidity/Frontend/SolcJson/Body.lean", "Solidity/Frontend/Source.lean", "Solidity/Frontend/SolcJson/Admission.lean", "Solidity/Examples/Tactics/SourceAdmissionImport.lean", "Solidity/Examples/Tactics/SourceLiteralsImport.lean", "Solidity/Examples/Tactics/SourceIdentifiersImport.lean", "docs/feature-work/source-admission.md"] }
  | .hexLiterals =>
    { category := "lexical", spelling := "hex\"...\"; adjacent hex strings",
      scope := .model, current := .limited,
      requirement := r#"Decode exact byte sequences, including empty values and separators allowed upstream."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 442 }], localEvidence := ["Solidity/Frontend/SolcJson/Body.lean", "Solidity/Frontend/Source.lean", "Solidity/Frontend/SolcJson/Admission.lean", "Solidity/Examples/Tactics/SourceAdmissionImport.lean", "Solidity/Examples/Tactics/SourceLiteralsImport.lean", "Solidity/Examples/Tactics/SourceIdentifiersImport.lean", "docs/feature-work/source-admission.md"] }
  | .addressLiterals =>
    { category := "lexical", spelling := "0x followed by address-sized hexadecimal digits",
      scope := .model, current := .limited,
      requirement := r#"Enforce address-literal length/checksum and 160-bit bounds; distinguish numeric literals and addresses."#,
      upstream := [{ path := "libsolidity/analysis/TypeChecker.cpp", line := 3954 }], localEvidence := ["Solidity/Frontend/SolcJson/Body.lean", "Solidity/Frontend/Source.lean", "Solidity/Frontend/SolcJson/Admission.lean", "Solidity/Examples/Tactics/SourceAdmissionImport.lean", "Solidity/Examples/Tactics/SourceLiteralsImport.lean", "Solidity/Examples/Tactics/SourceIdentifiersImport.lean", "docs/feature-work/source-admission.md"] }
  | .etherUnits =>
    { category := "lexical", spelling := "wei; gwei; ether",
      scope := .model, current := .present,
      requirement := r#"Multiply literals by exact powers of ten before range checking; denominations do not create a runtime currency type."#,
      upstream := [{ path := "docs/grammar/SolidityLexer.g4", line := 67 }], localEvidence := ["Solidity/Frontend/SolcJson/Body.lean"] }
  | .timeUnits =>
    { category := "lexical", spelling := "seconds; minutes; hours; days; weeks",
      scope := .model, current := .present,
      requirement := r#"Fold literal unit factors; do not infer real-world clock guarantees or calendar arithmetic."#,
      upstream := [{ path := "docs/grammar/SolidityLexer.g4", line := 67 }], localEvidence := ["Solidity/Frontend/SolcJson/Body.lean"] }
  | .pragmaVersion =>
    { category := "lexical", spelling := "pragma solidity version constraints",
      scope := .model, current := .limited,
      requirement := r#"Check the selected compiler/version range before importing a validated AST; record the compiler version."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 29 }], localEvidence := ["Solidity/Frontend/SolcJson/Body.lean", "Solidity/Frontend/Source.lean", "Solidity/Frontend/SolcJson/Admission.lean", "Solidity/Examples/Tactics/SourceAdmissionImport.lean", "Solidity/Examples/Tactics/SourceLiteralsImport.lean", "Solidity/Examples/Tactics/SourceIdentifiersImport.lean", "docs/feature-work/source-admission.md"] }
  | .pragmaAbicoder =>
    { category := "lexical", spelling := "pragma abicoder v1/v2; experimental ABIEncoderV2",
      scope := .model, current := .limited,
      requirement := r#"Record ABI-coder selection and its validation restrictions; do not silently apply v2 to a v1 compilation."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 29 }], localEvidence := ["Solidity/Frontend/Source.lean", "Solidity/Frontend/SolcJson/Admission.lean", "Solidity/Examples/Tactics/SourceAdmissionImport.lean", "Solidity/Examples/Tactics/SourceLiteralsImport.lean", "Solidity/Examples/Tactics/SourceIdentifiersImport.lean", "docs/feature-work/source-admission.md"] }
  | .pragmaOther =>
    { category := "lexical", spelling := "other pragmas and experimental feature gates",
      scope := .model, current := .limited,
      requirement := r#"Delegate acceptance to pinned solc and reject unknown enabled language modes; compiler settings are part of provenance."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 29 }], localEvidence := ["Solidity/Frontend/Source.lean", "Solidity/Frontend/SolcJson/Admission.lean", "Solidity/Examples/Tactics/SourceAdmissionImport.lean", "Solidity/Examples/Tactics/SourceLiteralsImport.lean", "Solidity/Examples/Tactics/SourceIdentifiersImport.lean", "docs/feature-work/source-admission.md"] }
  | .sourceUnits =>
    { category := "declarations", spelling := "source files and top-level declarations",
      scope := .model, current := .limited,
      requirement := r#"Preserve file-level namespaces and all reachable declaration identities across the compilation unit."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 12 }], localEvidence := ["Solidity/Frontend/SolcJson/Contract.lean"] }
  | .imports =>
    { category := "declarations", spelling := "import path; as; named aliases; wildcard namespace",
      scope := .model, current := .limited,
      requirement := r#"Resolve imports/remappings in solc; preserve qualified references and declaration IDs in the importer."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 34 }], localEvidence := ["Solidity/Frontend/SolcJson/Contract.lean"] }
  | .contracts =>
    { category := "declarations", spelling := "contract C; abstract contract C",
      scope := .model, current := .limited,
      requirement := r#"Distinguish deployable and abstract contracts, initialization and declared member visibility."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 16 }], localEvidence := ["Solidity/Frontend/SolcJson/Contract.lean"] }
  | .interfaces =>
    { category := "declarations", spelling := "interface I is J",
      scope := .model, current := .limited,
      requirement := r#"Preserve external signatures, inherited interface members and the absence of implementation bodies."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 67 }], localEvidence := ["Solidity/Frontend/SolcJson/Contract.lean"] }
  | .libraries =>
    { category := "declarations", spelling := "library L",
      scope := .model, current := .limited,
      requirement := r#"Inline resolvable pure/internal library calls; externally linked library execution additionally requires an explicit world/storage-context abstraction."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 74 }], localEvidence := ["Solidity/Frontend/SolcJson/Contract.lean"] }
  | .inheritance =>
    { category := "declarations", spelling := "is A(args), B; diamond inheritance",
      scope := .model, current := .limited,
      requirement := r#"Follow solc C3 linearization, virtual dispatch and base initialization order; do not flatten solely by source name."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 84 }], localEvidence := ["Solidity/Frontend/SolcJson/Contract.lean"] }
  | .overrideDeclarations =>
    { category := "declarations", spelling := "virtual; override; override(A,B)",
      scope := .model, current := .limited,
      requirement := r#"Validate overrides in solc and retain distinct base bodies and the selected implementation."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 159 }], localEvidence := ["Solidity/Frontend/SolcJson/Contract.lean"] }
  | .functions =>
    { category := "declarations", spelling := "function f(...) returns (...)",
      scope := .model, current := .limited,
      requirement := r#"Preserve parameter/return order, named return defaults, overload resolution, implicit return and visibility."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 19 }], localEvidence := ["Solidity/Frontend/SolcJson/Contract.lean", "tests/solc/DeclarationMetadata.sol"] }
  | .freeFunctions =>
    { category := "declarations", spelling := "file-level function definitions",
      scope := .model, current := .limited,
      requirement := r#"Resolve free and imported functions by declaration identity; model them without an implicit contract receiver."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 12 }], localEvidence := ["Solidity/Frontend/SolcJson/Contract.lean"] }
  | .constructors =>
    { category := "declarations", spelling := "constructor(...) payable modifiers {...}",
      scope := .model, current := .limited,
      requirement := r#"Run state initializers and base constructors exactly once in compiler order; handle payments and rollback."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 93 }], localEvidence := ["Solidity/Frontend/SolcJson/Contract.lean"] }
  | .modifiers =>
    { category := "declarations", spelling := "modifier m(...); m(args); inherited modifiers",
      scope := .model, current := .limited,
      requirement := r#"Evaluate arguments and nest pre/body/post execution in source application order, including return/revert interactions."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 95 }], localEvidence := ["Solidity/Frontend/SolcJson/Contract.lean"] }
  | .modifierPlaceholder =>
    { category := "declarations", spelling := "_; one or repeated syntactic placeholders; conditionally reached placeholders",
      scope := .model, current := .limited,
      requirement := r#"Invoke the modified continuation at each executed placeholder, preserving nesting and returns. A concrete modifier body must contain a placeholder, and a placeholder cannot be inside unchecked; a conditional placeholder can skip the body dynamically. Abstract modifier declarations have no body."#,
      upstream := [{ path := "libsolidity/parsing/Parser.cpp", line := 1423 }, { path := "libsolidity/analysis/SyntaxChecker.cpp", line := 212 }, { path := "libsolidity/analysis/SyntaxChecker.cpp", line := 402 }], localEvidence := ["Solidity/Frontend/SolcJson/Contract.lean"] }
  | .receiveFunction =>
    { category := "declarations", spelling := "receive() external payable",
      scope := .model, current := .limited,
      requirement := r#"Run the receive body for the modeled empty-data payment entry; preserve payable checks and callback behavior."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 97 }], localEvidence := ["Solidity/Frontend/SolcJson/Contract.lean"] }
  | .fallbackFunction =>
    { category := "declarations", spelling := "fallback(); fallback(bytes calldata) returns(bytes memory)",
      scope := .model, current := .limited,
      requirement := r#"Model the no-argument body only under explicit entry assumptions; the byte-oriented overload also uses excluded raw call data/return data."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 96 }], localEvidence := ["Solidity/Frontend/SolcJson/Contract.lean"] }
  | .visibility =>
    { category := "declarations", spelling := "public; external; internal; private",
      scope := .model, current := .limited,
      requirement := r#"Enforce permitted calls/access and distinguish external entry from internal dispatch; public does not imply every call is external."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 125 }], localEvidence := ["Solidity/Frontend/SolcJson/Contract.lean"] }
  | .stateMutability =>
    { category := "declarations", spelling := "pure; view; payable; default nonpayable",
      scope := .model, current := .limited,
      requirement := r#"Enforce static restrictions and payment entry guards; view alone does not prove other contracts preserve this contract's state."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 153 }], localEvidence := ["Solidity/Frontend/SolcJson/Contract.lean"] }
  | .stateVariables =>
    { category := "declarations", spelling := "state T x; initializer",
      scope := .model, current := .limited,
      requirement := r#"Give each logical root its declared type/default and execute initializers with correct visibility and declaration ordering."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 101 }], localEvidence := ["Solidity/Frontend/SolcJson/Contract.lean"] }
  | .constants =>
    { category := "declarations", spelling := "constant state and file variables",
      scope := .model, current := .limited,
      requirement := r#"Evaluate supported constants by declaration identity; preserve contextual width and reject unsupported constant expressions."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 20 }], localEvidence := ["Solidity/Frontend/SolcJson/Contract.lean"] }
  | .immutables =>
    { category := "declarations", spelling := "immutable state variable",
      scope := .model, current := .limited,
      requirement := r#"Enforce constructor initialization/read rules and retain the value across transactions; representing it as a logical root must not allow later writes."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 101 }], localEvidence := ["Solidity/Frontend/SolcJson/Contract.lean"] }
  | .publicGetters =>
    { category := "declarations", spelling := "synthesized getters; public override variable",
      scope := .model, current := .missing,
      requirement := r#"Generate exact getter signatures and omit struct array/mapping members as solc does; validate interface overrides."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 2865 }], localEvidence := [] }
  | .structDeclarations =>
    { category := "declarations", spelling := "struct S { T f; ... }",
      scope := .model, current := .limited,
      requirement := r#"Preserve member identity/order, recursive legality and storage/memory compatibility; recursive shapes remain an implementation task."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 251 }], localEvidence := ["Solidity/Frontend/SolcJson/Contract.lean"] }
  | .enumDeclarations =>
    { category := "declarations", spelling := "enum E { A, B, ... }",
      scope := .model, current := .limited,
      requirement := r#"Preserve distinct enum identity, ordinals, min/max and runtime conversion checks."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 259 }], localEvidence := ["Solidity/Frontend/SolcJson/Contract.lean"] }
  | .valueTypeDeclarations =>
    { category := "declarations", spelling := "type T is V",
      scope := .model, current := .limited,
      requirement := r#"Keep source nominal identity for type checking; lower only after preserving underlying signedness/width and wrap/unwrap rules."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 263 }], localEvidence := ["Solidity/Frontend/SolcJson/Contract.lean"] }
  | .errorDeclarations =>
    { category := "declarations", spelling := "error E(T a, ...)",
      scope := .model, current := .limited,
      requirement := r#"Preserve signature, selector and argument evaluation/encoding for custom errors, including qualified declarations."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 317 }], localEvidence := ["Solidity/Frontend/SolcJson/Contract.lean"] }
  | .eventDeclarations =>
    { category := "declarations", spelling := "event E(... indexed ...) anonymous",
      scope := .model, current := .limited,
      requirement := r#"Preserve declaration and indexed/anonymous metadata; argument evaluation belongs to the model, log observation is separately excluded."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 304 }], localEvidence := ["Solidity/Frontend/SolcJson/Contract.lean"] }
  | .usingFor =>
    { category := "declarations", spelling := "using L for T/*; using {f} for T; global",
      scope := .model, current := .limited,
      requirement := r#"Resolve extension calls by solc identity and bind the receiver once; global applicability is lexical/type-specific."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 346 }], localEvidence := ["Solidity/Frontend/SolcJson/Contract.lean"] }
  | .operatorAliases =>
    { category := "declarations", spelling := "using {f as op} for T global; op in &, ~, |, ^, +, /, %, *, -, ==, >, >=, <, <=, !=",
      scope := .model, current := .missing,
      requirement := r#"Lower all 15 permitted operator aliases to their resolved pure free functions; distinguish unary and binary signatures."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 325 }], localEvidence := [] }
  | .boolType =>
    { category := "types", spelling := "bool",
      scope := .model, current := .present,
      requirement := r#"Keep Boolean typing distinct from integers and ABI words."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 359 }], localEvidence := ["Solidity/AST.lean"] }
  | .integerTypes =>
    { category := "types", spelling := "uint/int; uint8..uint256; int8..int256 in steps of 8",
      scope := .model, current := .limited,
      requirement := r#"Track width and signedness at every nested type position and intermediate operation; aliases mean 256 bits."#,
      upstream := [{ path := "docs/grammar/SolidityLexer.g4", line := 82 }], localEvidence := ["Solidity/AST.lean"] }
  | .addressTypes =>
    { category := "types", spelling := "address; address payable; contract/interface references",
      scope := .model, current := .limited,
      requirement := r#"Use bounded 160-bit identities and validate payable conversion rules before erasure to the logical address representation."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 359 }], localEvidence := ["Solidity/AST.lean"] }
  | .fixedBytesTypes =>
    { category := "types", spelling := "bytes1..bytes32",
      scope := .model, current := .limited,
      requirement := r#"Track byte length, indexing, padding, alignment, bitwise operations and explicit conversions."#,
      upstream := [{ path := "docs/grammar/SolidityLexer.g4", line := 41 }], localEvidence := ["Solidity/AST.lean"] }
  | .dynamicBytesType =>
    { category := "types", spelling := "bytes",
      scope := .model, current := .limited,
      requirement := r#"Treat as byte array with Solidity storage/memory/calldata restrictions and exact copying behavior."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 359 }], localEvidence := ["Solidity/AST.lean"] }
  | .stringType =>
    { category := "types", spelling := "string",
      scope := .model, current := .limited,
      requirement := r#"Model byte content and explicit conversions; string has no direct indexing or length member."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 359 }], localEvidence := ["Solidity/AST.lean"] }
  | .dynamicArrays =>
    { category := "types", spelling := "T[]; nested dynamic arrays",
      scope := .model, current := .limited,
      requirement := r#"Track runtime lengths, bounds, reference element types and source-dependent assignment/copy behavior."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 358 }], localEvidence := ["Solidity/AST.lean"] }
  | .fixedArrays =>
    { category := "types", spelling := "T[n]; nested fixed arrays",
      scope := .model, current := .limited,
      requirement := r#"Evaluate constant lengths and retain lengths in types; preserve element bounds and ABI restrictions."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 358 }], localEvidence := ["Solidity/AST.lean"] }
  | .mappings =>
    { category := "types", spelling := "mapping(K [keyName] => V [valueName])",
      scope := .model, current := .limited,
      requirement := r#"Model allowed key types, default values, nested mappings and named getter components without pretending the map is enumerable."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 547 }], localEvidence := ["Solidity/AST.lean"] }
  | .structTypes =>
    { category := "types", spelling := "qualified user-defined struct types",
      scope := .model, current := .limited,
      requirement := r#"Retain declaration identity and recursive graph restrictions; independently validate storage and memory uses."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 251 }], localEvidence := ["Solidity/AST.lean"] }
  | .enumTypes =>
    { category := "types", spelling := "qualified enum types",
      scope := .model, current := .limited,
      requirement := r#"Preserve enum membership ranges in conversions and ABI entry values."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 259 }], localEvidence := ["Solidity/AST.lean"] }
  | .valueTypes =>
    { category := "types", spelling := "user-defined value types",
      scope := .model, current := .limited,
      requirement := r#"Erase wrappers only after solc nominal checks and operator resolution, retaining exact primitive shape."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 263 }], localEvidence := ["Solidity/AST.lean"] }
  | .internalFunctionTypes =>
    { category := "types", spelling := "function(...) internal [pure/view] returns(...)",
      scope := .model, current := .limited,
      requirement := r#"Model declaration identities/dispatch tables and uninitialized-function failure, not machine jump addresses."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 358 }], localEvidence := ["Solidity/AST.lean"] }
  | .externalFunctionTypes =>
    { category := "types", spelling := "function(...) external [payable/view/pure] returns(...)",
      scope := .abstract, current := .limited,
      requirement := r#"Represent target address plus typed function identity/selector and an explicit external-call relation; no raw code pointers."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 358 }], localEvidence := ["Solidity/AST.lean"] }
  | .tupleTypes =>
    { category := "types", spelling := "tuple values; holes; multiple returns",
      scope := .model, current := .limited,
      requirement := r#"Preserve simultaneous assignment and evaluation/capture order; tuples are not independently declarable Solidity variable types."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 419 }], localEvidence := ["Solidity/AST.lean"] }
  | .storageLocation =>
    { category := "types", spelling := "storage locals/parameters/returns",
      scope := .model, current := .limited,
      requirement := r#"Represent typed logical paths; distinguish binding a reference, copying an aggregate and mutating its target."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 374 }], localEvidence := ["Solidity/AST.lean"] }
  | .memoryLocation =>
    { category := "types", spelling := "memory locals/parameters/returns",
      scope := .model, current := .limited,
      requirement := r#"Preserve heap object identity, aliasing, allocation and copy boundaries across calls."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 374 }], localEvidence := ["Solidity/AST.lean"] }
  | .calldataLocation =>
    { category := "types", spelling := "typed calldata parameters, locals, slices and returns",
      scope := .model, current := .limited,
      requirement := r#"Model immutable typed views and bounds; typed calldata does not require exposing msg.data or physical ABI offsets."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 374 }], localEvidence := ["Solidity/AST.lean"] }
  | .recursiveTypes =>
    { category := "types", spelling := "recursive structs through mappings/arrays",
      scope := .model, current := .missing,
      requirement := r#"Use a guarded/graph representation where Solidity permits recursion; do not treat a finite-tree implementation limit as an EVM exclusion."#,
      upstream := [{ path := "libsolidity/ast/AST.h", line := 781 }], localEvidence := [] }
  | .names =>
    { category := "expressions", spelling := "identifiers; qualified members; this; super",
      scope := .model, current := .limited,
      requirement := r#"Resolve declarations, distinguish locals/state/type members and retain selected base implementations."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 115 }], localEvidence := ["Solidity/Syntax/Grammar.lean"] }
  | .parentheses =>
    { category := "expressions", spelling := "(e)",
      scope := .model, current := .present,
      requirement := r#"Preserve grouping without introducing a tuple or changing evaluation."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 419 }], localEvidence := ["Solidity/Syntax/Grammar.lean"] }
  | .tupleExpressions =>
    { category := "expressions", spelling := "(a,b); (a,,b); return tuples",
      scope := .model, current := .limited,
      requirement := r#"Capture all components once and commit assignments in Solidity order, preserving empty targets."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 419 }], localEvidence := ["Solidity/Syntax/Grammar.lean"] }
  | .inlineArrays =>
    { category := "expressions", spelling := "[a,b,...]",
      scope := .model, current := .limited,
      requirement := r#"Infer the fixed memory array independently of its target using the first mobile element type and implicit common types; preserve allocation and element-copy timing. Nominal element identities and recursive shapes remain partial."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 423 }], localEvidence := ["Solidity/Syntax/Grammar.lean", "Solidity/Syntax/Elab/Lower.lean", "Solidity/Syntax/Elab/Arms.lean", "Solidity/Examples/Tactics/Aggregates.lean", "Solidity/Examples/Tactics/AggregatesImport.lean", "docs/feature-work/aggregates.md"] }
  | .memberAccess =>
    { category := "expressions", spelling := "e.f",
      scope := .model, current := .limited,
      requirement := r#"Distinguish fields, builtins, type members and extension methods using resolved types/declarations."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 386 }], localEvidence := ["Solidity/Syntax/Grammar.lean"] }
  | .indexAccess =>
    { category := "expressions", spelling := "e[i]",
      scope := .model, current := .limited,
      requirement := r#"Check bounds for arrays/bytes; use key-type conversion for mappings; capture side effects once."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 384 }], localEvidence := ["Solidity/Syntax/Grammar.lean"] }
  | .rangeAccess =>
    { category := "expressions", spelling := "a[start:end]; omitted endpoints",
      scope := .model, current := .limited,
      requirement := r#"Model legal calldata views with zero-based derived lengths, endpoint checks and shared immutable content."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 385 }], localEvidence := ["Solidity/Syntax/Grammar.lean", "Solidity/Examples/Tactics/AggregateSlices.lean", "docs/feature-work/aggregates.md"] }
  | .unaryArithmetic =>
    { category := "expressions", spelling := "-x; ~x; !x",
      scope := .model, current := .limited,
      requirement := r#"Respect width/signedness, Boolean negation and checked minimum-integer negation; no unary numeric plus exists."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 391 }], localEvidence := ["Solidity/Syntax/Grammar.lean"] }
  | .increments =>
    { category := "expressions", spelling := "++x; x++; --x; x--",
      scope := .model, current := .limited,
      requirement := r#"Preserve lvalue evaluation once, old/new result and overflow mode; Lean spelling of decrement differs only at its parser boundary."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 392 }], localEvidence := ["Solidity/Syntax/Grammar.lean"] }
  | .deleteExpression =>
    { category := "expressions", spelling := "delete x",
      scope := .model, current := .limited,
      requirement := r#"Reset the target according to its type; mappings inside aggregates retain inaccessible historical entries where Solidity does."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 391 }], localEvidence := ["Solidity/Syntax/Grammar.lean"] }
  | .arithmetic =>
    { category := "expressions", spelling := "+ - * / % **",
      scope := .model, current := .limited,
      requirement := r#"Apply Solidity typing/overflow and signed division/remainder; exponentiation is right associative and division by zero always fails."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 393 }], localEvidence := ["Solidity/Syntax/Grammar.lean"] }
  | .bitwise =>
    { category := "expressions", spelling := "& ^ |",
      scope := .model, current := .limited,
      requirement := r#"Operate over finite-width representations and preserve bytesN versus integer typing."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 397 }], localEvidence := ["Solidity/Syntax/Grammar.lean"] }
  | .shifts =>
    { category := "expressions", spelling := "<<; >>",
      scope := .model, current := .limited,
      requirement := r#"Preserve left operand type; signed right shift sign-extends; shifts do not gain checked-arithmetic overflow guards."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 396 }], localEvidence := ["Solidity/Syntax/Grammar.lean"] }
  | .comparisons =>
    { category := "expressions", spelling := "< <= > >= == !=",
      scope := .model, current := .limited,
      requirement := r#"Admit only comparisons supported by Solidity types; do not invent structural equality on arrays/structs."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 400 }], localEvidence := ["Solidity/Syntax/Grammar.lean"] }
  | .shortCircuit =>
    { category := "expressions", spelling := "a && b; a || b",
      scope := .model, current := .limited,
      requirement := r#"Evaluate the second operand only when required and preserve failures/side effects in the first."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 402 }], localEvidence := ["Solidity/Syntax/Grammar.lean"] }
  | .conditional =>
    { category := "expressions", spelling := "c ? a : b",
      scope := .model, current := .limited,
      requirement := r#"Evaluate only one arm and preserve the conditional's inferred/mobile type, including reference-valued arms."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 404 }], localEvidence := ["Solidity/Syntax/Grammar.lean"] }
  | .assignment =>
    { category := "expressions", spelling := "x = e; nested assignment expressions",
      scope := .model, current := .limited,
      requirement := r#"Preserve lvalue/rvalue scheduling and reference-versus-copy semantics; the assigned value is also an expression result where legal."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 405 }], localEvidence := ["Solidity/Syntax/Grammar.lean"] }
  | .compoundAssignment =>
    { category := "expressions", spelling := "+= -= *= /= %= &= ^= |= <<= >>=",
      scope := .model, current := .limited,
      requirement := r#"Capture the target once, read the old value at the proper point and use its declared arithmetic width."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 418 }], localEvidence := ["Solidity/Syntax/Grammar.lean"] }
  | .explicitConversions =>
    { category := "expressions", spelling := "T(e); payable(e); bytes/string/array casts",
      scope := .model, current := .limited,
      requirement := r#"Preserve Solidity legality, truncation, sign extension, bytesN alignment and enum checks; casts differ from checked arithmetic."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 389 }], localEvidence := ["Solidity/Syntax/Grammar.lean"] }
  | .implicitConversions =>
    { category := "expressions", spelling := "contextual literal/type conversions",
      scope := .model, current := .limited,
      requirement := r#"Use solc's resolved type, preserving widths before enclosing operations rather than only at assignment."#,
      upstream := [{ path := "docs/types/value-types.rst", line := 481 }], localEvidence := ["Solidity/Syntax/Grammar.lean"] }
  | .structConstruction =>
    { category := "expressions", spelling := "S(args); S({f: e,...})",
      scope := .model, current := .limited,
      requirement := r#"Evaluate arguments in the selected compiler order, use field declaration order and allocate correct memory objects."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 111 }], localEvidence := ["Solidity/Syntax/Grammar.lean"] }
  | .namedArguments =>
    { category := "expressions", spelling := "f({b: e2,a: e1})",
      scope := .model, current := .limited,
      requirement := r#"Bind by formal name while preserving actual compiler evaluation order; do not assume textual object order."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 106 }], localEvidence := ["Solidity/Syntax/Grammar.lean"] }
  | .newMemory =>
    { category := "expressions", spelling := "new T[](n); new bytes(n)",
      scope := .model, current := .limited,
      requirement := r#"Allocate fresh defaulted memory, check feasible lengths and preserve allocation failure as a distinct concern from mathematical unboundedness."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 406 }], localEvidence := ["Solidity/Syntax/Grammar.lean"] }
  | .functionCalls =>
    { category := "expressions", spelling := "f(args); member calls; function-valued expressions",
      scope := .model, current := .limited,
      requirement := r#"Evaluate callee/receiver and every argument exactly once before entering a fresh call frame."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 387 }], localEvidence := ["Solidity/Syntax/Grammar.lean"] }
  | .callOptions =>
    { category := "expressions", spelling := "f{value:v,gas:g}(...); new C{salt:s,value:v}(...)",
      scope := .model, current := .limited,
      requirement := r#"Split options by semantic demand: value is modeled, gas is excluded, salt is excluded; a generic options node is not automatically admissible."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 387 }], localEvidence := ["Solidity/Syntax/Grammar.lean"] }
  | .metaTypeExpression =>
    { category := "expressions", spelling := "type(T)",
      scope := .model, current := .limited,
      requirement := r#"Resolve only integer, enum or contract/interface metatypes accepted upstream; classify each accessed member separately."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 390 }], localEvidence := ["Solidity/Syntax/Grammar.lean"] }
  | .blocks =>
    { category := "statements", spelling := "{...}; nested scopes",
      scope := .model, current := .limited,
      requirement := r#"Allocate locals with Solidity lifetime, default initialization and shadowing; discard bindings when leaving the scope."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 456 }], localEvidence := ["Solidity/Syntax/Scoped.lean", "Solidity/Frontend/SolcJson/Contract.lean", "tests/solc/Shadowing.sol", "scripts/source-shadowing.test.mjs", "docs/feature-work/dafny-verification.md"] }
  | .uncheckedBlock =>
    { category := "statements", spelling := "unchecked {...}",
      scope := .model, current := .limited,
      requirement := r#"Wrap only applicable arithmetic in lexical scope; retain division/index checks and do not propagate unchecked into called functions."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 459 }], localEvidence := ["Solidity/Syntax/Scoped.lean"] }
  | .variableDeclarations =>
    { category := "statements", spelling := "T x; T x=e; tuple declarations with holes",
      scope := .model, current := .limited,
      requirement := r#"Preserve declaration identity, defaults, data location, inference constraints and initializer capture order."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 544 }], localEvidence := ["Solidity/Syntax/Scoped.lean"] }
  | .expressionStatements =>
    { category := "statements", spelling := "e;",
      scope := .model, current := .limited,
      requirement := r#"Execute all effects and failures even when the resulting value is discarded."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 545 }], localEvidence := ["Solidity/Syntax/Scoped.lean"] }
  | .ifStatement =>
    { category := "statements", spelling := "if(c) s; if(c) s else t",
      scope := .model, current := .present,
      requirement := r#"Evaluate a Boolean condition once and execute exactly one branch."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 482 }], localEvidence := ["Solidity/Syntax/Scoped.lean"] }
  | .whileStatement =>
    { category := "statements", spelling := "while(c) s",
      scope := .model, current := .limited,
      requirement := r#"Reevaluate condition and distinguish termination, revert, break, continue and divergence."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 487 }], localEvidence := ["Solidity/Syntax/Scoped.lean"] }
  | .forStatement =>
    { category := "statements", spelling := "for(init;condition;post) s",
      scope := .model, current := .limited,
      requirement := r#"Handle omitted clauses, initializer scope and continue-through-post behavior."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 486 }], localEvidence := ["Solidity/Syntax/Scoped.lean"] }
  | .doWhileStatement =>
    { category := "statements", spelling := "do s while(c);",
      scope := .model, current := .limited,
      requirement := r#"Execute body before condition and route continue to the condition."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 488 }], localEvidence := ["Solidity/Syntax/Scoped.lean"] }
  | .breakStatement =>
    { category := "statements", spelling := "break;",
      scope := .model, current := .present,
      requirement := r#"Exit only the innermost loop without evaluating its next condition/post."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 496 }], localEvidence := ["Solidity/Syntax/Scoped.lean"] }
  | .continueStatement =>
    { category := "statements", spelling := "continue;",
      scope := .model, current := .limited,
      requirement := r#"Continue the innermost loop with the correct post/condition destination."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 492 }], localEvidence := ["Solidity/Syntax/Scoped.lean"] }
  | .returnStatement =>
    { category := "statements", spelling := "return; return e; return(a,b)",
      scope := .model, current := .limited,
      requirement := r#"Capture return values/references and run enclosing modifier continuations with correct frame isolation."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 506 }], localEvidence := ["Solidity/Syntax/Scoped.lean"] }
  | .tryStatement =>
    { category := "statements", spelling := "try externalCall/new C returns(...) {...} catch...",
      scope := .abstract, current := .limited,
      requirement := r#"Separate callee failure from caller argument/return-decoding failures; typed contract creation needs the world abstraction."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 500 }], localEvidence := ["Solidity/Syntax/Scoped.lean"] }
  | .catchClauses =>
    { category := "statements", spelling := "catch Error(string); Panic(uint); (bytes); catch {...}",
      scope := .model, current := .limited,
      requirement := r#"Dispatch by valid revert bytes, handle malformed payloads and preserve caller/callee rollback boundaries."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 504 }], localEvidence := ["Solidity/Syntax/Scoped.lean"] }
  | .revertStatement =>
    { category := "statements", spelling := "revert E(args); revert(); revert(reason)",
      scope := .model, current := .limited,
      requirement := r#"Evaluate payload arguments and roll back the correct frame; retain exact bytes where supported and document proof-logic precision limits."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 514 }], localEvidence := ["Solidity/Syntax/Scoped.lean"] }
  | .emitStatement =>
    { category := "statements", spelling := "emit E(args)",
      scope := .model, current := .limited,
      requirement := r#"Evaluate every argument for effects/reverts before erasing the unobserved log; erasure is valid only for properties that do not observe logs."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 510 }], localEvidence := ["Solidity/Syntax/Scoped.lean"] }
  | .canonicalRethrow =>
    { category := "statements", spelling := "assembly { revert(add(data,32),mload(data)) }",
      scope := .abstract, current := .limited,
      requirement := r#"Recognize only the verified whole-buffer pattern with matching resolved declarations; lower to raw rethrow, never admit general Yul by this exception."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 520 }], localEvidence := ["Solidity/Syntax/Scoped.lean"] }
  | .assertBuiltin =>
    { category := "builtins", spelling := "assert(bool)",
      scope := .model, current := .limited,
      requirement := r#"False raises Panic(0x01); distinguish failure from assumptions and from ordinary require failure."#,
      upstream := [{ path := "libsolidity/analysis/GlobalContext.cpp", line := 85 }], localEvidence := ["Solidity/Syntax/Elab.lean"] }
  | .requireBuiltin =>
    { category := "builtins", spelling := "require(bool); require(bool,string); require(bool,E(...))",
      scope := .model, current := .limited,
      requirement := r#"Evaluate all arguments even if the condition succeeds; retain Error/custom-error encoding and rollback."#,
      upstream := [{ path := "libsolidity/analysis/GlobalContext.cpp", line := 95 }], localEvidence := ["Solidity/Syntax/Elab.lean"] }
  | .revertBuiltin =>
    { category := "builtins", spelling := "revert(); revert(string)",
      scope := .model, current := .limited,
      requirement := r#"Preserve computed reasons and evaluation failures; do not replace revert by a proof assumption."#,
      upstream := [{ path := "libsolidity/analysis/GlobalContext.cpp", line := 98 }], localEvidence := ["Solidity/Syntax/Elab.lean"] }
  | .addmodBuiltin =>
    { category := "builtins", spelling := "addmod(x,y,k)",
      scope := .model, current := .limited,
      requirement := r#"Compute with arbitrary-precision intermediate addition; reject a constant zero modulus and fail with Panic(0x12) for a dynamic zero modulus. Raw EVM opcode zero behavior is not Solidity builtin behavior."#,
      upstream := [{ path := "libsolidity/analysis/GlobalContext.cpp", line := 84 }, { path := "docs/units-and-global-variables.rst", line := 204 }], localEvidence := ["Solidity/Syntax/Elab.lean"] }
  | .mulmodBuiltin =>
    { category := "builtins", spelling := "mulmod(x,y,k)",
      scope := .model, current := .limited,
      requirement := r#"Compute with arbitrary-precision intermediate multiplication; reject a constant zero modulus and fail with Panic(0x12) for a dynamic zero modulus. Raw EVM opcode zero behavior is not Solidity builtin behavior."#,
      upstream := [{ path := "libsolidity/analysis/GlobalContext.cpp", line := 93 }, { path := "docs/units-and-global-variables.rst", line := 207 }], localEvidence := ["Solidity/Syntax/Elab.lean"] }
  | .keccakBuiltin =>
    { category := "builtins", spelling := "keccak256(bytes)",
      scope := .abstract, current := .limited,
      requirement := r#"Use the existing Keccak semantics/explicit abstraction over bytes; injectivity and collision resistance are not unconditional equations."#,
      upstream := [{ path := "libsolidity/analysis/GlobalContext.cpp", line := 91 }], localEvidence := ["Solidity/Syntax/Elab.lean", "Solidity/Examples/Tactics/AbiFeatures.lean", "Solidity/Examples/Tactics/AbiFeaturesImport.lean", "docs/feature-work/abi-hashes.md"] }
  | .sha256Builtin =>
    { category := "builtins", spelling := "sha256(bytes)",
      scope := .abstract, current := .limited,
      requirement := r#"Use an explicit deterministic cryptographic interpretation; opaque axioms must not claim collision freedom."#,
      upstream := [{ path := "libsolidity/analysis/GlobalContext.cpp", line := 102 }], localEvidence := ["Solidity/Syntax/Elab.lean", "Solidity/Examples/Tactics/AbiFeatures.lean", "Solidity/Examples/Tactics/AbiFeaturesImport.lean", "docs/feature-work/abi-hashes.md"] }
  | .ripemd160Builtin =>
    { category := "builtins", spelling := "ripemd160(bytes)",
      scope := .abstract, current := .limited,
      requirement := r#"Preserve the 20-byte result and explicit interpretation independently of precompile gas."#,
      upstream := [{ path := "libsolidity/analysis/GlobalContext.cpp", line := 100 }], localEvidence := ["Solidity/Syntax/Elab.lean", "Solidity/Examples/Tactics/AbiFeatures.lean", "Solidity/Examples/Tactics/AbiFeaturesImport.lean", "docs/feature-work/abi-hashes.md"] }
  | .ecrecoverBuiltin =>
    { category := "builtins", spelling := "ecrecover(hash,v,r,s)",
      scope := .abstract, current := .limited,
      requirement := r#"Computed bounded recovery validates v/r/s and returns zero on failure; concrete kernel/EVM vectors pass. General group-law and precompile-equivalence proofs remain open; signer authorization requires separate premises."#,
      upstream := [{ path := "libsolidity/analysis/GlobalContext.cpp", line := 88 }], localEvidence := ["Solidity/Syntax/Elab.lean", "Solidity/Examples/Tactics/AbiFeatures.lean", "Solidity/Examples/Tactics/AbiFeaturesImport.lean", "docs/feature-work/abi-hashes.md", "Solidity/Secp256k1.lean", "Solidity/Semantics/Heap.lean", "Solidity/Examples/Tactics/Recovery.lean"] }
  | .erc7201Builtin =>
    { category := "builtins", spelling := "erc7201(string memory id) returns(uint)",
      scope := .model, current := .present,
      requirement := r#"Evaluate the ERC-7201 namespace formula for runtime strings and constant-foldable inputs: hash the string bytes, subtract one modulo 2^256, hash the encoded word, and clear the low eight bits. Producing a namespace integer does not expose physical storage."#,
      upstream := [{ path := "libsolidity/analysis/GlobalContext.cpp", line := 89 }, { path := "docs/units-and-global-variables.rst", line := 250 }, { path := "libsolidity/analysis/TypeChecker.cpp", line := 2405 }], localEvidence := ["Solidity/Examples/Tactics/AbiFeatures.lean", "Solidity/Examples/Tactics/AbiFeaturesImport.lean", "docs/feature-work/abi-hashes.md", "Solidity/ERC7201.lean", "Solidity/Syntax/Elab/Lower.lean"] }
  | .wrapUnwrap =>
    { category := "builtins", spelling := "T.wrap(x); T.unwrap(x)",
      scope := .model, current := .limited,
      requirement := r#"Preserve the exact underlying value and perform nominal checks before erasure; these are not arithmetic casts."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 3930 }], localEvidence := ["Solidity/Syntax/Elab.lean"] }
  | .bytesConcat =>
    { category := "builtins", spelling := "bytes.concat(...)",
      scope := .model, current := .limited,
      requirement := r#"Concatenate exact bytes/bytesN in argument order with fresh result memory."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 3930 }], localEvidence := ["Solidity/Syntax/Elab.lean", "Solidity/Examples/Tactics/AbiFeatures.lean", "Solidity/Examples/Tactics/AbiFeaturesImport.lean", "docs/feature-work/abi-hashes.md"] }
  | .stringConcat =>
    { category := "builtins", spelling := "string.concat(...)",
      scope := .model, current := .limited,
      requirement := r#"Concatenate byte content, preserving argument evaluation and fresh allocation."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 3930 }], localEvidence := ["Solidity/Syntax/Elab.lean", "Solidity/Examples/Tactics/AbiFeatures.lean", "Solidity/Examples/Tactics/AbiFeaturesImport.lean", "docs/feature-work/abi-hashes.md"] }
  | .msgSender =>
    { category := "environment", spelling := "msg.sender",
      scope := .abstract, current := .present,
      requirement := r#"Supply a bounded caller identity per call frame; external self-calls change sender."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 4199 }], localEvidence := ["Solidity/Semantics/State.lean"] }
  | .msgValue =>
    { category := "environment", spelling := "msg.value",
      scope := .abstract, current := .limited,
      requirement := r#"Supply per-frame payment with payable entry/ledger assumptions; callback/self-call frames may change the value."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 4201 }], localEvidence := ["Solidity/Semantics/State.lean"] }
  | .thisAddress =>
    { category := "environment", spelling := "this; address(this)",
      scope := .abstract, current := .limited,
      requirement := r#"Supply a bounded deployment identity and distinguish the contract value from its external call dispatch."#,
      upstream := [{ path := "libsolidity/analysis/GlobalContext.cpp", line := 146 }], localEvidence := ["Solidity/Semantics/State.lean"] }
  | .addressBalance =>
    { category := "environment", spelling := "address(a).balance; address(this).balance",
      scope := .abstract, current := .limited,
      requirement := r#"Read an explicit ledger and state required balance/supply/world assumptions; arbitrary-address balances are not proved from chain execution."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 554 }], localEvidence := ["Solidity/Semantics/State.lean"] }
  | .blockTimestamp =>
    { category := "environment", spelling := "block.timestamp",
      scope := .abstract, current := .present,
      requirement := r#"Read the environment timestamp; monotonicity, accuracy and miner constraints require explicit premises."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 4186 }], localEvidence := ["Solidity/Semantics/State.lean"] }
  | .blockCoinbase =>
    { category := "environment", spelling := "block.coinbase",
      scope := .exclude, current := .notApplicable,
      requirement := r#"This profile supplies only block.timestamp; coinbase requires an additional chain input and premises (feasible in another profile), not an invented constant. Fork gating remains solc's responsibility."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 4185 }], localEvidence := [] }
  | .blockDifficulty =>
    { category := "environment", spelling := "block.difficulty",
      scope := .exclude, current := .notApplicable,
      requirement := r#"This profile supplies only block.timestamp; difficulty requires an additional chain input and premises (feasible in another profile), not an invented constant. Fork gating remains solc's responsibility."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 4188 }], localEvidence := [] }
  | .blockPrevrandao =>
    { category := "environment", spelling := "block.prevrandao",
      scope := .exclude, current := .notApplicable,
      requirement := r#"This profile supplies only block.timestamp; prevrandao requires an additional chain input and premises (feasible in another profile), not an invented constant. Fork gating remains solc's responsibility."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 4189 }], localEvidence := [] }
  | .blockNumber =>
    { category := "environment", spelling := "block.number",
      scope := .exclude, current := .notApplicable,
      requirement := r#"This profile supplies only block.timestamp; number requires an additional chain input and premises (feasible in another profile), not an invented constant. Fork gating remains solc's responsibility."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 4190 }], localEvidence := [] }
  | .blockGaslimit =>
    { category := "environment", spelling := "block.gaslimit",
      scope := .exclude, current := .notApplicable,
      requirement := r#"This profile supplies only block.timestamp; gaslimit requires an additional chain input and premises (feasible in another profile), not an invented constant. Fork gating remains solc's responsibility."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 4191 }], localEvidence := [] }
  | .blockChainid =>
    { category := "environment", spelling := "block.chainid",
      scope := .exclude, current := .notApplicable,
      requirement := r#"This profile supplies only block.timestamp; chainid requires an additional chain input and premises (feasible in another profile), not an invented constant. Fork gating remains solc's responsibility."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 4192 }], localEvidence := [] }
  | .blockBasefee =>
    { category := "environment", spelling := "block.basefee",
      scope := .exclude, current := .notApplicable,
      requirement := r#"This profile supplies only block.timestamp; basefee requires an additional chain input and premises (feasible in another profile), not an invented constant. Fork gating remains solc's responsibility."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 4193 }], localEvidence := [] }
  | .blockBlobbasefee =>
    { category := "environment", spelling := "block.blobbasefee",
      scope := .exclude, current := .notApplicable,
      requirement := r#"This profile supplies only block.timestamp; blobbasefee requires an additional chain input and premises (feasible in another profile), not an invented constant. Fork gating remains solc's responsibility."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 4194 }], localEvidence := [] }
  | .blockSlotnum =>
    { category := "environment", spelling := "block.slotnum",
      scope := .exclude, current := .notApplicable,
      requirement := r#"This profile supplies only block.timestamp; slotnum requires an additional chain input and premises (feasible in another profile), not an invented constant. Fork gating remains solc's responsibility."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 4195 }], localEvidence := [] }
  | .txOrigin =>
    { category := "environment", spelling := "tx.origin",
      scope := .exclude, current := .notApplicable,
      requirement := r#"Transaction-origin identity is not carried by the current call environment; it must not be replaced by msg.sender."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 4207 }], localEvidence := [] }
  | .txGasprice =>
    { category := "environment", spelling := "tx.gasprice",
      scope := .exclude, current := .notApplicable,
      requirement := r#"Transaction pricing lies outside the chosen functional environment and gas abstraction."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 4208 }], localEvidence := [] }
  | .blockhashBuiltin =>
    { category := "environment", spelling := "blockhash(n)",
      scope := .exclude, current := .notApplicable,
      requirement := r#"Requires chain history, fork rules and the bounded block-hash window absent from this profile."#,
      upstream := [{ path := "libsolidity/analysis/GlobalContext.cpp", line := 87 }], localEvidence := [] }
  | .blobhashBuiltin =>
    { category := "environment", spelling := "blobhash(i)",
      scope := .exclude, current := .notApplicable,
      requirement := r#"Requires transaction blob metadata and fork rules absent from this profile."#,
      upstream := [{ path := "libsolidity/analysis/GlobalContext.cpp", line := 119 }], localEvidence := [] }
  | .internalCalls =>
    { category := "calls", spelling := "f(args); base-qualified and super calls",
      scope := .model, current := .limited,
      requirement := r#"Use resolved implementation identity and fresh frames; preserve return/default/reference values and modifier continuations."#,
      upstream := [{ path := "libsolidity/ast/Types.h", line := 1259 }], localEvidence := ["Solidity/Semantics.lean"] }
  | .recursiveCalls =>
    { category := "calls", spelling := "direct/mutual recursion",
      scope := .model, current := .limited,
      requirement := r#"Model recursion/frame exhaustion explicitly; the existing bounded call implementation is not unbounded mathematical recursion."#,
      upstream := [{ path := "libsolidity/ast/Types.h", line := 1259 }], localEvidence := ["Solidity/Semantics.lean"] }
  | .externalTypedCalls =>
    { category := "calls", spelling := "c.f(args); interface calls",
      scope := .abstract, current := .limited,
      requirement := r#"Use typed inputs/outcomes, payment/rollback and a documented external-call relation; arbitrary external code is not proved by the local interpreter."#,
      upstream := [{ path := "libsolidity/ast/Types.h", line := 1260 }], localEvidence := ["Solidity/Semantics.lean"] }
  | .externalSelfCalls =>
    { category := "calls", spelling := "this.f(args)",
      scope := .model, current := .limited,
      requirement := r#"Run a distinct external frame with sender=this, value, return ABI validation and local-state rollback behavior."#,
      upstream := [{ path := "libsolidity/ast/Types.h", line := 1260 }], localEvidence := ["Solidity/Semantics.lean"] }
  | .extensionCalls =>
    { category := "calls", spelling := "x.f(args) via using for",
      scope := .model, current := .limited,
      requirement := r#"Bind receiver once and lower to the resolved function; external library calls require their own world/storage abstraction."#,
      upstream := [{ path := "libsolidity/ast/Types.h", line := 1259 }], localEvidence := ["Solidity/Semantics.lean"] }
  | .functionValues =>
    { category := "calls", spelling := "taking, storing, comparing and invoking function values",
      scope := .model, current := .limited,
      requirement := r#"Preserve Solidity identity rules, compatible signatures and failure for unset internal function values; avoid code-address equality assumptions."#,
      upstream := [{ path := "libsolidity/ast/Types.h", line := 1260 }], localEvidence := ["Solidity/Semantics.lean"] }
  | .valueOption =>
    { category := "calls", spelling := "{value: amount}",
      scope := .model, current := .limited,
      requirement := r#"Evaluate amount and update ledger on success with rollback on failure, respecting payable and self-call semantics."#,
      upstream := [{ path := "docs/control-structures.rst", line := 83 }], localEvidence := ["Solidity/Semantics.lean"] }
  | .sendTransfer =>
    { category := "calls", spelling := "address payable .send(v); .transfer(v)",
      scope := .abstract, current := .limited,
      requirement := r#"Model success/failure, transfer's revert behavior and payment effects; callback exclusion is an explicit selected assumption, not a timeless gas theorem."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 564 }], localEvidence := ["Solidity/Semantics.lean"] }
  | .emptyDataValueCall =>
    { category := "calls", spelling := "(bool ok,) = a.call{value:v}(\"\")",
      scope := .abstract, current := .limited,
      requirement := r#"Admit only the recognized empty-payload payment form, discard unread return bytes and allow callbacks under the chosen call semantics."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 557 }], localEvidence := ["Solidity/Semantics.lean"] }
  | .newContract =>
    { category := "calls", spelling := "new C(args) without salt",
      scope := .abstract, current := .missing,
      requirement := r#"Requires fresh address/world allocation, constructor execution, payment, rollback and callable instance identity; feasible source-level extension without bytecode."#,
      upstream := [{ path := "libsolidity/ast/Types.h", line := 1266 }], localEvidence := [] }
  | .creationTry =>
    { category := "calls", spelling := "try new C(args) returns(C c)",
      scope := .abstract, current := .missing,
      requirement := r#"Use contract-world creation outcomes and catch only creation-frame failures; caller-side evaluation errors still propagate."#,
      upstream := [{ path := "libsolidity/ast/Types.h", line := 1266 }], localEvidence := [] }
  | .callbackSemantics =>
    { category := "calls", spelling := "reentrancy during modeled external calls",
      scope := .abstract, current := .limited,
      requirement := r#"Select and record ordinary versus callback modality; state frame guarantees and callback invariants explicitly."#,
      upstream := [{ path := "docs/control-structures.rst", line := 65 }], localEvidence := ["Solidity/Semantics.lean"] }
  | .externalLibraryCalls =>
    { category := "calls", spelling := "linked library public/external calls",
      scope := .abstract, current := .missing,
      requirement := r#"Execute typed library bodies in caller storage context with explicit library identity/static restrictions; internal library lowering alone is insufficient."#,
      upstream := [{ path := "libsolidity/ast/Types.h", line := 1261 }], localEvidence := [] }
  | .abiEncode =>
    { category := "abi", spelling := "abi.encode(...)",
      scope := .model, current := .limited,
      requirement := r#"Implement canonical head/tail, offsets, padding and recursive value shapes; current supported shape is narrower than all Solidity ABI types."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 4212 }], localEvidence := ["Solidity/Syntax/Elab.lean", "Solidity/Examples/Tactics/AbiFeatures.lean", "Solidity/Examples/Tactics/AbiFeaturesImport.lean", "docs/feature-work/abi-hashes.md"] }
  | .abiEncodePacked =>
    { category := "abi", spelling := "abi.encodePacked(...)",
      scope := .model, current := .limited,
      requirement := r#"Preserve packed widths and array restrictions; ambiguity/collisions of packed encodings are real and must not be erased."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 4222 }], localEvidence := ["Solidity/Syntax/Elab.lean", "Solidity/Examples/Tactics/AbiFeatures.lean", "Solidity/Examples/Tactics/AbiFeaturesImport.lean", "docs/feature-work/abi-hashes.md"] }
  | .abiEncodeWithSelector =>
    { category := "abi", spelling := "abi.encodeWithSelector(bytes4,...)",
      scope := .model, current := .limited,
      requirement := r#"Prefix a selector to canonical encoding; selector bytes are data, independent of raw CALL support. Existing selector-prefix lowering supports restricted argument shapes; complete recursive ABI shape coverage remains to be established."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 4232 }], localEvidence := ["Solidity/Syntax/Elab/Lower.lean", "Solidity/Syntax/Elab/Arms.lean", "Solidity/Examples/Tactics/AbiFeatures.lean", "Solidity/Examples/Tactics/AbiFeaturesImport.lean", "docs/feature-work/abi-hashes.md"] }
  | .abiEncodeWithSignature =>
    { category := "abi", spelling := "abi.encodeWithSignature(string,...)",
      scope := .model, current := .limited,
      requirement := r#"Derive bytes4(keccak256(signature)) then canonical encoding; do not assert hashes are injective. Existing selector-prefix lowering supports restricted argument shapes; complete recursive ABI shape coverage remains to be established."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 4252 }], localEvidence := ["Solidity/Syntax/Elab/Lower.lean", "Solidity/Syntax/Elab/Arms.lean", "Solidity/Examples/Tactics/AbiFeatures.lean", "Solidity/Examples/Tactics/AbiFeaturesImport.lean", "docs/feature-work/abi-hashes.md"] }
  | .abiEncodeCall =>
    { category := "abi", spelling := "abi.encodeCall(f,(args))",
      scope := .model, current := .limited,
      requirement := r#"Check exact function/tuple compatibility, derive selector and encode typed arguments. Existing selector-prefix lowering supports restricted argument shapes; complete recursive ABI shape coverage remains to be established."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 4242 }], localEvidence := ["Solidity/Syntax/Elab/Lower.lean", "Solidity/Syntax/Elab/Arms.lean", "Solidity/Examples/Tactics/AbiFeatures.lean", "Solidity/Examples/Tactics/AbiFeaturesImport.lean", "docs/feature-work/abi-hashes.md"] }
  | .abiDecode =>
    { category := "abi", spelling := "abi.decode(bytes,(T,...))",
      scope := .model, current := .limited,
      requirement := r#"Validate offsets, lengths, ranges, truncation and fixed-byte padding before traversal/allocation; preserve noncanonical unaligned and overlapping layouts that solc accepts. Nominal enum metadata and complete recursive ABI coverage remain partial."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 4262 }], localEvidence := ["Solidity/Syntax/Elab.lean", "Solidity/Examples/Tactics/AbiFeatures.lean", "Solidity/Examples/Tactics/AbiFeaturesImport.lean", "docs/feature-work/abi-hashes.md"] }
  | .typeBounds =>
    { category := "metadata", spelling := "type(integer/enum).min/max",
      scope := .model, current := .limited,
      requirement := r#"Produce exact source-type bounds, including enum cardinality and signed minimum."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 4305 }], localEvidence := ["Solidity/Frontend/SolcJson/Body.lean"] }
  | .typeName =>
    { category := "metadata", spelling := "type(C).name",
      scope := .model, current := .present,
      requirement := r#"Return compiler-resolved contract name bytes as a compile-time value."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 4293 }], localEvidence := ["Solidity/Frontend/SolcJson/Body.lean", "Solidity/Examples/Tactics/DeclarationMetadata.lean", "tests/solc/DeclarationMetadata.sol", "docs/feature-work/declarations-metadata.md"] }
  | .interfaceId =>
    { category := "metadata", spelling := "type(I).interfaceId",
      scope := .model, current := .present,
      requirement := r#"Compute the XOR of the interface's own external function selectors according to Solidity rules; inherited functions are excluded."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 4297 }], localEvidence := ["Solidity/Frontend/SolcJson/Body.lean", "Solidity/Examples/Tactics/DeclarationMetadata.lean", "tests/solc/DeclarationMetadata.sol", "docs/feature-work/declarations-metadata.md"] }
  | .functionSelector =>
    { category := "metadata", spelling := "f.selector; C.f.selector",
      scope := .model, current := .limited,
      requirement := r#"Preserve canonical signature and four-byte selector without exposing code addresses or asserting uniqueness. Existing lowering handles modeled external function values; all declaration contexts still need validation."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 3399 }], localEvidence := ["Solidity/Syntax/Elab/Values.lean", "Solidity/Frontend/SolcJson/Contract.lean", "tests/solc/DeclarationMetadata.sol"] }
  | .functionAddress =>
    { category := "metadata", spelling := "externalFunction.address",
      scope := .model, current := .limited,
      requirement := r#"Project the bounded receiver identity from an external function value. Existing lowering handles modeled external function values; all declaration contexts still need validation."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 3399 }], localEvidence := ["Solidity/Syntax/Elab/Values.lean", "Solidity/Frontend/SolcJson/Contract.lean", "tests/solc/DeclarationMetadata.sol"] }
  | .errorEventSelector =>
    { category := "metadata", spelling := "E.selector for errors/events where accepted",
      scope := .model, current := .present,
      requirement := r#"Compute bytes4 for error signatures and bytes32 for non-anonymous event signatures, respecting solc declaration resolution; anonymous events have no selector member."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 3399 }], localEvidence := ["Solidity/Frontend/SolcJson/Body.lean", "Solidity/Examples/Tactics/DeclarationMetadata.lean", "tests/solc/DeclarationMetadata.sol", "docs/feature-work/declarations-metadata.md"] }
  | .arrayLength =>
    { category := "storage", spelling := "arrays/bytes/bytesN .length",
      scope := .model, current := .limited,
      requirement := r#"Return exact length with correct static/dynamic location restrictions; string requires an explicit bytes conversion."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 1925 }], localEvidence := ["Solidity/Semantics/Storage/Ops.lean"] }
  | .arrayPush =>
    { category := "storage", spelling := "storage dynamic array/bytes .push(v)",
      scope := .model, current := .limited,
      requirement := r#"Evaluate receiver and source in compiler order, grow length, initialize/copy the new element and preserve aliases."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 1925 }], localEvidence := ["Solidity/Semantics/Storage/Ops.lean"] }
  | .arrayPushReference =>
    { category := "storage", spelling := "storage dynamic array .push()",
      scope := .model, current := .limited,
      requirement := r#"Append a default value and return a storage lvalue/reference; nested member effects must occur in compiler order."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 1925 }], localEvidence := ["Solidity/Semantics/Storage/Ops.lean"] }
  | .arrayPop =>
    { category := "storage", spelling := "storage dynamic array/bytes .pop()",
      scope := .model, current := .limited,
      requirement := r#"Fail on empty, shorten length and clear the element according to Solidity mapping-tail rules."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 1925 }], localEvidence := ["Solidity/Semantics/Storage/Ops.lean"] }
  | .storageCopy =>
    { category := "storage", spelling := "storage assignment of arrays/structs",
      scope := .model, current := .limited,
      requirement := r#"Deep-copy value content with destination cleanup and correct overlapping/alias behavior; mapping members are not naively copied."#,
      upstream := [{ path := "docs/types/reference-types.rst", line := 64 }], localEvidence := ["Solidity/Semantics/Storage/Ops.lean"] }
  | .memoryAliasing =>
    { category := "storage", spelling := "memory-to-memory and internal memory parameters",
      scope := .model, current := .limited,
      requirement := r#"Share object identity where Solidity aliases; external ABI boundaries copy and storage-to-memory creates fresh objects."#,
      upstream := [{ path := "docs/types/reference-types.rst", line := 64 }], localEvidence := ["Solidity/Semantics/Storage/Ops.lean"] }
  | .storageAliasing =>
    { category := "storage", spelling := "storage local/parameter/return paths",
      scope := .model, current := .limited,
      requirement := r#"Rebinding a reference differs from writing its target; represent nested fields and indices without physical slot numbers."#,
      upstream := [{ path := "docs/types/reference-types.rst", line := 64 }], localEvidence := ["Solidity/Semantics/Storage/Ops.lean"] }
  | .deleteMappingTails =>
    { category := "storage", spelling := "delete aggregates and later reusing dynamic slots",
      scope := .model, current := .limited,
      requirement := r#"Preserve mapping entries where Solidity does, and record clean-tail assumptions/selected semantics rather than hiding them."#,
      upstream := [{ path := "docs/types/reference-types.rst", line := 98 }], localEvidence := ["Solidity/Semantics/Storage/Ops.lean"] }
  | .danglingReferences =>
    { category := "storage", spelling := "references invalidated by pop/delete/resize",
      scope := .model, current := .limited,
      requirement := r#"Preserve the chosen Solidity/compiler semantics or reject affected programs explicitly; safe-path assumptions need premises."#,
      upstream := [{ path := "docs/types/reference-types.rst", line := 496 }], localEvidence := ["Solidity/Semantics/Storage/Ops.lean"] }
  | .transientState =>
    { category := "storage", spelling := "T transient x",
      scope := .model, current := .limited,
      requirement := r#"Typed primitive and established signature-marked function-tag source declarations use disjoint regions of the joint logical root product; nested self-calls share cells, failure rolls back the product, and lifetime/replay transaction boundaries reset cells. Physical layout, raw tload/tstore, raw function addresses and general source world/delegate execution remain unsupported."#,
      upstream := [{ path := "libsolidity/parsing/Parser.cpp", line := 895 }, { path := "docs/contracts/transient-storage.rst", line := 6 }], localEvidence := ["Solidity/Semantics/Storage/Anon.lean", "Solidity/Semantics/Lifetime.lean", "Solidity/Examples/Tactics/TransientStorage.lean", "Solidity/Semantics/TransientWorld.lean", "Solidity/Examples/Tactics/TransientWorld.lean"] }
  | .checkedArithmetic =>
    { category := "semantics", spelling := "Solidity 0.8 default checked arithmetic",
      scope := .model, current := .limited,
      requirement := r#"Guard every operation at its intermediate width, signedness and overflow mode, including values used only by conditions."#,
      upstream := [{ path := "docs/control-structures.rst", line := 519 }], localEvidence := ["docs/solc-alignment.md"] }
  | .uncheckedArithmetic =>
    { category := "semantics", spelling := "modular unchecked operations",
      scope := .model, current := .limited,
      requirement := r#"Wrap at each operation's width; zero division and invalid indexing still fail and called functions retain their own lexical mode."#,
      upstream := [{ path := "docs/control-structures.rst", line := 519 }], localEvidence := ["docs/solc-alignment.md"] }
  | .evaluationOrder =>
    { category := "semantics", spelling := "legacy/via-IR scheduling and optimizer settings",
      scope := .model, current := .limited,
      requirement := r#"Record the selected compiler pipeline; do not impose a single source-order guarantee where Solidity leaves order unspecified."#,
      upstream := [{ path := "docs/control-structures.rst", line := 323 }], localEvidence := ["docs/solc-alignment.md"] }
  | .exactConstants =>
    { category := "semantics", spelling := "rational/constant-expression evaluation",
      scope := .model, current := .limited,
      requirement := r#"Evaluate exact rationals and contextual/mobile literal types before runtime integer operations."#,
      upstream := [{ path := "docs/types/value-types.rst", line := 481 }], localEvidence := ["docs/solc-alignment.md", "Solidity/Frontend/Source.lean", "Solidity/Frontend/SolcJson/Admission.lean", "Solidity/Examples/Tactics/SourceAdmissionImport.lean", "Solidity/Examples/Tactics/SourceLiteralsImport.lean", "Solidity/Examples/Tactics/SourceIdentifiersImport.lean", "docs/feature-work/source-admission.md"] }
  | .defaultInitialization =>
    { category := "semantics", spelling := "zero/default locals, fields and returns",
      scope := .model, current := .limited,
      requirement := r#"Default according to complete type and location; unset storage references and function values have special restrictions/failure behavior."#,
      upstream := [{ path := "docs/control-structures.rst", line := 425 }], localEvidence := ["docs/solc-alignment.md"] }
  | .referenceCopyRules =>
    { category := "semantics", spelling := "storage/memory/calldata assignment matrix",
      scope := .model, current := .limited,
      requirement := r#"Define every allowed location pair, reference binding versus deep copy, and nested element compatibility explicitly."#,
      upstream := [{ path := "docs/types/reference-types.rst", line := 64 }], localEvidence := ["docs/solc-alignment.md", "Solidity/Examples/Tactics/Aggregates.lean", "docs/feature-work/aggregates.md"] }
  | .panicCodes =>
    { category := "semantics", spelling := "Panic 0x00/01/11/12/21/22/31/32/41/51",
      scope := .model, current := .limited,
      requirement := r#"Retain applicable Solidity panic codes and payloads; some current paths lose data, and malformed storage encoding 0x22 is tied to excluded low-level corruption."#,
      upstream := [{ path := "docs/control-structures.rst", line := 612 }], localEvidence := ["docs/solc-alignment.md"] }
  | .revertPayloads =>
    { category := "semantics", spelling := "Error(string), custom errors, Panic, raw bytes",
      scope := .model, current := .limited,
      requirement := r#"Distinguish runtime byte precision from what the current proof modalities can observe; do not advertise exact computed-data proofs where unavailable."#,
      upstream := [{ path := "docs/control-structures.rst", line := 589 }], localEvidence := ["docs/solc-alignment.md"] }
  | .rollback =>
    { category := "semantics", spelling := "require/revert/panic/call failure",
      scope := .model, current := .limited,
      requirement := r#"Roll back storage, transient state, ledger and outputs at the failing frame boundary while keeping caller state where Solidity does."#,
      upstream := [{ path := "docs/control-structures.rst", line := 589 }], localEvidence := ["docs/solc-alignment.md"] }
  | .abiEntryValidation =>
    { category := "semantics", spelling := "external parameters and return decoding",
      scope := .abstract, current := .limited,
      requirement := r#"State caller assumptions and enforce ABI range/shape validation; malformed return decoding is a caller failure, not a caught callee revert."#,
      upstream := [{ path := "docs/control-structures.rst", line := 65 }, { path := "docs/abi-spec.rst", line := 24 }], localEvidence := ["docs/solc-alignment.md"] }
  | .constructorLifetime =>
    { category := "semantics", spelling := "deployment and transaction traces",
      scope := .abstract, current := .limited,
      requirement := r#"State which claims range over arbitrary typed states versus constructor-reachable traces and deployed instances."#,
      upstream := [{ path := "docs/control-structures.rst", line := 216 }], localEvidence := ["docs/solc-alignment.md"] }
  | .nonpayableEntry =>
    { category := "semantics", spelling := "nonpayable function/constructor call",
      scope := .model, current := .limited,
      requirement := r#"Refuse nonzero msg.value at external entry without incorrectly restricting internal calls of the same declaration."#,
      upstream := [{ path := "docs/control-structures.rst", line := 65 }], localEvidence := ["docs/solc-alignment.md"] }
  | .staticCallRestriction =>
    { category := "semantics", spelling := "view/static external execution",
      scope := .abstract, current := .limited,
      requirement := r#"Model forbidden writes/payments in a static context, including transitive calls; source view checking alone does not capture arbitrary external behavior."#,
      upstream := [{ path := "docs/control-structures.rst", line := 65 }], localEvidence := ["docs/solc-alignment.md"] }
  | .termination =>
    { category := "semantics", spelling := "loops/recursion, divergence, resource bounds",
      scope := .model, current := .limited,
      requirement := r#"Keep semantic divergence separate from evaluator fuel and real EVM gas; total-correctness claims must state their termination premises."#,
      upstream := [{ path := "docs/control-structures.rst", line := 2 }], localEvidence := ["docs/solc-alignment.md"] }
  | .worldAssumptions =>
    { category := "semantics", spelling := "balances, code existence and external responses",
      scope := .abstract, current := .limited,
      requirement := r#"Carry chain premises and call/callback interpretation in the theorem; do not derive them from the single-contract store."#,
      upstream := [{ path := "docs/control-structures.rst", line := 65 }], localEvidence := ["docs/solc-alignment.md"] }
  | .typeValidation =>
    { category := "semantics", spelling := "solc validation, nominal types, overloads and mutability",
      scope := .model, current := .limited,
      requirement := r#"Import only validated ASTs from the pinned compiler/settings; the catalog is not a replacement type checker."#,
      upstream := [{ path := "docs/control-structures.rst", line := 65 }], localEvidence := ["docs/solc-alignment.md", "Solidity/Frontend/Source.lean", "Solidity/Frontend/SolcJson/Admission.lean", "Solidity/Examples/Tactics/SourceAdmissionImport.lean", "Solidity/Examples/Tactics/SourceLiteralsImport.lean", "Solidity/Examples/Tactics/SourceIdentifiersImport.lean", "docs/feature-work/source-admission.md"] }
  | .featureDetection =>
    { category := "semantics", spelling := "transitive declaration-aware feature extraction",
      scope := .model, current := .limited,
      requirement := r#"Collect features from initializers, modifiers, inherited bodies, callees, payloads, specifications and call options; reject unknown AST nodes instead of default admission."#,
      upstream := [{ path := "docs/control-structures.rst", line := 65 }], localEvidence := ["Solidity/Frontend/Source.lean", "Solidity/Frontend/SolcJson/Admission.lean", "Solidity/Examples/Tactics/SourceAdmissionImport.lean", "Solidity/Examples/Tactics/SourceLiteralsImport.lean", "Solidity/Examples/Tactics/SourceIdentifiersImport.lean", "docs/feature-work/source-admission.md"] }
  | .inlineAssembly =>
    { category := "excluded", spelling := "arbitrary assembly / Yul including memory-safe flags",
      scope := .exclude, current := .notApplicable,
      requirement := r#"General Yul exposes machine memory, slots, opcodes and fork-dependent effects; only the separately recognized whole-buffer rethrow is abstracted."#,
      upstream := [{ path := "docs/grammar/SolidityParser.g4", line := 520 }], localEvidence := [] }
  | .gasleft =>
    { category := "excluded", spelling := "gasleft()",
      scope := .exclude, current := .notApplicable,
      requirement := r#"Requires dynamic gas accounting, memory expansion, refunds and call forwarding absent from functional semantics."#,
      upstream := [{ path := "libsolidity/analysis/GlobalContext.cpp", line := 90 }], localEvidence := [] }
  | .gasOption =>
    { category := "excluded", spelling := "{gas:g}; exact forwarded gas/stipend",
      scope := .exclude, current := .notApplicable,
      requirement := r#"An exact gas budget can change success, failure and reentrancy; it cannot be silently discarded."#,
      upstream := [{ path := "docs/control-structures.rst", line := 83 }], localEvidence := [] }
  | .rawCalldata =>
    { category := "excluded", spelling := "msg.data; msg.sig; fallback(bytes) input",
      scope := .exclude, current := .notApplicable,
      requirement := r#"This profile starts with typed arguments and lacks raw transaction payload/selector dispatch; typed calldata views remain in scope."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 4202 }], localEvidence := [] }
  | .rawReturndata =>
    { category := "excluded", spelling := "arbitrary raw low-level return bytes; fallback raw output",
      scope := .exclude, current := .notApplicable,
      requirement := r#"Exact arbitrary external return bytes and machine return-buffer behavior are outside typed external-call outcomes; caught revert bytes are separate."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 557 }], localEvidence := [] }
  | .lowLevelCall =>
    { category := "excluded", spelling := "address.call(arbitraryBytes)",
      scope := .exclude, current := .notApplicable,
      requirement := r#"Arbitrary selector dispatch and byte-oriented external world effects exceed the recognized empty-data payment form."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 557 }], localEvidence := [] }
  | .delegatecall =>
    { category := "excluded", spelling := "address.delegatecall(bytes)",
      scope := .exclude, current := .notApplicable,
      requirement := r#"Arbitrary foreign code executes against caller storage and context; requires a code/world semantics beyond typed library abstractions."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 559 }], localEvidence := [] }
  | .lowLevelStaticcall =>
    { category := "excluded", spelling := "address.staticcall(bytes)",
      scope := .exclude, current := .notApplicable,
      requirement := r#"Arbitrary byte-oriented dispatch/static-context return bytes require a richer external world than typed view calls."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 560 }], localEvidence := [] }
  | .selfdestruct =>
    { category := "excluded", spelling := "selfdestruct(payableAddress)",
      scope := .exclude, current := .notApplicable,
      requirement := r#"Balance transfer, account deletion and creation-in-transaction exceptions depend on fork-specific world semantics."#,
      upstream := [{ path := "libsolidity/analysis/GlobalContext.cpp", line := 101 }], localEvidence := [] }
  | .create2Salt =>
    { category := "excluded", spelling := "new C{salt:s}(...); deterministic deployment address",
      scope := .exclude, current := .notApplicable,
      requirement := r#"Address derivation requires init-code hashing and account/world collision rules absent from this profile."#,
      upstream := [{ path := "docs/control-structures.rst", line := 257 }], localEvidence := [] }
  | .addressCode =>
    { category := "excluded", spelling := "address.code; extcodesize",
      scope := .exclude, current := .notApplicable,
      requirement := r#"Observes deployed bytecode/code size, including construction/deletion states, absent from the source interpreter."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 555 }], localEvidence := [] }
  | .addressCodehash =>
    { category := "excluded", spelling := "address.codehash; extcodehash",
      scope := .exclude, current := .notApplicable,
      requirement := r#"Observes account existence and deployed bytecode hashing, absent from the source interpreter."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 556 }], localEvidence := [] }
  | .creationCode =>
    { category := "metadata", spelling := "type(C).creationCode",
      scope := .model, current := .limited,
      requirement := r#"Static compiler code constants require matching exact compiler/source/settings artifacts; deployed account code, unresolved linking and oversized materialization are not supported."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 4291 }], localEvidence := ["Solidity/Frontend/Source.lean", "Solidity/Frontend/SolcJson/Body.lean", "scripts/solc-code.mjs"] }
  | .runtimeCode =>
    { category := "metadata", spelling := "type(C).runtimeCode",
      scope := .model, current := .limited,
      requirement := r#"Static compiler code constants require matching exact compiler/source/settings artifacts; deployed account code, unresolved linking and oversized materialization are not supported."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 4292 }], localEvidence := ["Solidity/Frontend/Source.lean", "Solidity/Frontend/SolcJson/Body.lean", "scripts/solc-code.mjs"] }
  | .logicalStorageBase =>
    { category := "storage", spelling := "literal layout at base with logical field observations",
      scope := .model, current := .limited,
      requirement := r#"Accept compiler-validated literal storage bases only for logical typed root operations. Raw slots, offsets, packing, tload/tstore and assembly remain excluded; the base does not change declaration identities or the disjoint persistent/transient root partition."#,
      upstream := [{ path := "libsolidity/ast/AST.h", line := 635 }], localEvidence := ["Solidity/Frontend/SolcJson/Admission.lean", "Solidity/Semantics/Storage/Anon.lean"] }
  | .storageLayout =>
    { category := "excluded", spelling := "layout at expr; physical slots/packing/offsets",
      scope := .exclude, current := .notApplicable,
      requirement := r#"Logical typed paths intentionally omit slot arithmetic, packing and the physical storage address space."#,
      upstream := [{ path := "libsolidity/ast/AST.h", line := 635 }], localEvidence := [] }
  | .memoryLayout =>
    { category := "excluded", spelling := "raw memory addresses; mload/mstore; free-memory pointer",
      scope := .exclude, current := .notApplicable,
      requirement := r#"Typed heap objects have no exposed machine byte addresses, expansion cost or scratch/free-memory regions."#,
      upstream := [{ path := "docs/grammar/SolidityLexer.g4", line := 304 }], localEvidence := [] }
  | .transientLayout =>
    { category := "excluded", spelling := "physical transient slots; tload/tstore through assembly",
      scope := .exclude, current := .notApplicable,
      requirement := r#"Logical transaction-local values can be modeled separately; physical transient slot access is a machine observation."#,
      upstream := [{ path := "libsolidity/analysis/TypeChecker.cpp", line := 787 }], localEvidence := [] }
  | .eventLog =>
    { category := "excluded", spelling := "log contents/topics/order/gas; indexed/anonymous observation",
      scope := .exclude, current := .notApplicable,
      requirement := r#"The selected observation model erases logs after evaluating arguments; properties about emitted logs require a new observable trace."#,
      upstream := [{ path := "libsolidity/ast/Types.h", line := 1276 }], localEvidence := [] }
  | .machineResources =>
    { category := "excluded", spelling := "gas exhaustion/refunds, stack limits, exact allocation limits",
      scope := .exclude, current := .notApplicable,
      requirement := r#"Mathematical execution/fuel bounds are not real gas or stack accounting; exact resource-sensitive outcomes need an EVM semantics."#,
      upstream := [{ path := "docs/control-structures.rst", line := 61 }], localEvidence := [] }
  | .fixedPoint =>
    { category := "upstream", spelling := "fixed/ufixed; fixedMxN/ufixedMxN",
      scope := .upstream, current := .notApplicable,
      requirement := r#"Grammar/type placeholders exist but fixed-point code generation is upstream incomplete; do not claim complete Solidity runtime support."#,
      upstream := [{ path := "libsolidity/analysis/TypeChecker.cpp", line := 814 }], localEvidence := [] }
  | .removedAliases =>
    { category := "upstream", spelling := "now; sha3; suicide; throw; msg.gas; block.blockhash; callcode; legacy f.gas()/value()",
      scope := .upstream, current := .notApplicable,
      requirement := r#"Retained parser/AST/type entries receive upstream removal errors; report compiler invalidity before model scope diagnostics."#,
      upstream := [{ path := "libsolidity/analysis/TypeChecker.cpp", line := 3879 }], localEvidence := [] }
  | .unsignedRightShift =>
    { category := "upstream", spelling := ">>>; >>>=",
      scope := .upstream, current := .notApplicable,
      requirement := r#"Lexer/ANTLR retain these tokens but Solidity's type system rejects the unsigned-right-shift operator."#,
      upstream := [{ path := "libsolidity/ast/Types.cpp", line := 575 }], localEvidence := [] }
  | .removedUnits =>
    { category := "upstream", spelling := "years; historical finney/szabo",
      scope := .upstream, current := .notApplicable,
      requirement := r#"years is rejected by the type checker; removed historical units are not admitted by the modern compiler."#,
      upstream := [{ path := "libsolidity/analysis/TypeChecker.cpp", line := 3985 }], localEvidence := [] }
  | .reservedKeywords =>
    { category := "upstream", spelling := "after alias apply auto byte case copyof default define final implements in inline let macro match mutable null of partial promise reference relocatable sealed sizeof static supports switch typedef typeof var",
      scope := .upstream, current := .notApplicable,
      requirement := r#"Reserved lexer words are not executable language features; preserve compiler diagnostics and do not reinterpret them as identifiers."#,
      upstream := [{ path := "docs/grammar/SolidityLexer.g4", line := 6 }], localEvidence := [] }
  | .invalidLexemes =>
    { category := "upstream", spelling := "octal-like literals; number glued to identifier; bare ->",
      scope := .upstream, current := .notApplicable,
      requirement := r#"Scanned tokens without a Solidity parser production remain invalid source; recognizing a token does not admit a language construct."#,
      upstream := [{ path := "docs/grammar/SolidityLexer.g4", line := 232 }], localEvidence := [] }
  | .removedGenericSolidity =>
    { category := "upstream", spelling := "pragma experimental solidity; Generic Solidity prototype",
      scope := .upstream, current := .notApplicable,
      requirement := r#"The experimental Generic Solidity language was removed in 0.8.37; it is not part of the pinned mainstream Solidity surface."#,
      upstream := [{ path := "Changelog.md", line := 46 }], localEvidence := [] }
  | .invalidModifierBody =>
    { category := "upstream", spelling := "concrete modifier body without _; placeholder inside unchecked",
      scope := .upstream, current := .notApplicable,
      requirement := r#"Pinned solc rejects concrete modifiers without any placeholder and placeholders nested inside unchecked blocks; an abstract modifier declaration without a body is legal."#,
      upstream := [{ path := "libsolidity/analysis/SyntaxChecker.cpp", line := 212 }, { path := "libsolidity/analysis/SyntaxChecker.cpp", line := 402 }], localEvidence := [] }

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

def Unmodelled.reason (u : Unmodelled) : String := u.feature.info.requirement

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
  Feature.all.filter fun f => f.info.scope == .model

def abstractFeatures : List Feature :=
  Feature.all.filter fun f => f.info.scope == .abstract

def targetFeatures : List Feature :=
  Feature.all.filter fun f => f.info.scope == .model || f.info.scope == .abstract

def outsideScope : List Unmodelled := Unmodelled.all

def presentFeatures : List Feature :=
  targetFeatures.filter fun f => f.info.current == .present

def missingFeatures : List Feature :=
  targetFeatures.filter fun f => f.info.current == .missing

def partialFeatures : List Feature :=
  targetFeatures.filter fun f => f.info.current == .limited

def rejectedByUpstream : List Feature :=
  Feature.all.filter fun f => f.info.scope == .upstream

def requirements : List (Feature × String) :=
  targetFeatures.map fun f => (f, f.info.requirement)

/-- A policy decision; no assertion of current implementation support. -/
def Feature.inProfile (f : Feature) : Prop :=
  f.info.scope = .model ∨ f.info.scope = .abstract

def WithinProfile (features : List Feature) : Prop :=
  ∀ f ∈ features, f.inProfile

/-- Restrict an actual syntax representation using a supplied feature extractor.
Completeness of `uses` must be established separately; this is not a fake full AST. -/
def ProfileSyntax (Syntax : Type u) (uses : Syntax → List Feature) : Type u :=
  { ast : Syntax // WithinProfile (uses ast) }

/-- The diagnostic metadata and exclusion decision cannot disagree. -/
theorem Unmodelled.excluded (u : Unmodelled) : u.feature.info.scope = .exclude := by
  cases u with
  | blockField f => cases f <;> rfl
  | txOrigin => rfl
  | txGasprice => rfl
  | blockhashBuiltin => rfl
  | blobhashBuiltin => rfl
  | inlineAssembly => rfl
  | gasleft => rfl
  | gasOption => rfl
  | rawCalldata => rfl
  | rawReturndata => rfl
  | lowLevelCall => rfl
  | delegatecall => rfl
  | lowLevelStaticcall => rfl
  | selfdestruct => rfl
  | create2Salt => rfl
  | addressCode => rfl
  | addressCodehash => rfl
  | storageLayout => rfl
  | memoryLayout => rfl
  | transientLayout => rfl
  | eventLog => rfl
  | machineResources => rfl

/-- Every deliberately excluded feature has a structured diagnostic. -/
theorem Feature.exclusion_complete (f : Feature) (h : f.info.scope = .exclude) :
    ∃ u : Unmodelled, f.unmodelled? = some u ∧ u.feature = f := by
  cases f <;> first | exact ⟨_, rfl, rfl⟩ | cases h

def upstreamCommit : String := "1835d247de183f23e7b0e2bc4a50732af525b77c"
def upstreamVersion : String := "v0.8.38"

end Solidity.Language
