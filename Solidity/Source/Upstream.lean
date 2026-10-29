import Solidity.Source.Ctor

/-!
# The source syntax against the pinned grammar and the manifest (S00)

Three explicit tables relate `Syn` to its upstream sources.

- `grammarCtors`: each parser rule, and each labelled alternative
  (`expression#Label`), of the pinned ANTLR grammar
  (`tests/upstream/grammar-0.8.38/SolidityParser.g4`) whose content is
  structured syntax, with the constructors that represent it.
- `grammarData`: each rule represented by a datatype or a field instead (a
  visibility, an operator, a literal, an identifier), with that datatype.
- `featureCtors`: each feature of G00's manifest (`docs/solidity-features.json`)
  that is syntax, with its constructors; `featureLexical` lists the syntax
  features that live below the abstract syntax (G08).

`Ctor.grammar_covers` proves that every non-structural constructor
represents some rule, so `Syn` has no constructor without an upstream
origin.  The converse, that every rule and label of the grammar is a key of
exactly one of the two grammar tables and that every key and feature id
exists upstream, is checked against the files by
`scripts/check-source-grammar.mjs`, which also checks the grammar's pinned
hashes.
-/

namespace Solidity.Source

/-- The constructors for repetition and option: the grammar's `*`, `+`, `?`. -/
def Ctor.structural : Ctor → Bool
  | .nil | .cons | .none | .some => true
  | _ => false

/-- Parser rules and labelled alternatives with the constructors that
represent them. -/
def grammarCtors : List (String × List Ctor) := [
  ("sourceUnit", [.unit, .topPart]),
  ("pragmaDirective", [.pragma]),
  ("importDirective", [.importPath, .importSymbols, .importStar]),
  ("importAliases", [.importAlias]),
  ("symbolAliases", [.importSymbols]),
  ("contractDefinition", [.contract]),
  ("interfaceDefinition", [.interface]),
  ("libraryDefinition", [.library]),
  ("inheritanceSpecifierList", [.inherit]),
  ("inheritanceSpecifier", [.inherit]),
  ("contractBodyElement", [.constructor, .function, .modifier, .fallback, .receive, .struct,
    .enum, .udvt, .stateVar, .event, .error, .usingPart]),
  ("namedArgument", [.namedArg]),
  ("callArgumentList", [.positional, .named]),
  ("modifierInvocation", [.modInv]),
  ("parameterList", [.param]),
  ("parameterDeclaration", [.param]),
  ("constructorDefinition", [.constructor]),
  ("functionDefinition", [.function]),
  ("modifierDefinition", [.modifier]),
  ("fallbackFunctionDefinition", [.fallback, .fbNoParams, .fbParams]),
  ("receiveFunctionDefinition", [.receive]),
  ("structDefinition", [.struct]),
  ("structMember", [.structMember]),
  ("enumDefinition", [.enum]),
  ("userDefinedValueTypeDefinition", [.udvt]),
  ("stateVariableDeclaration", [.stateVar]),
  ("constantVariableDeclaration", [.constant]),
  ("eventParameter", [.eventParam]),
  ("eventDefinition", [.event]),
  ("errorParameter", [.errorParam]),
  ("errorDefinition", [.error]),
  ("usingDirective", [.usingPart, .usingPath, .usingAliases]),
  ("usingAliases", [.usingAlias]),
  ("typeName", [.elem, .fnType, .mapping, .userType, .array]),
  ("elementaryTypeName", [.elem, .elemType]),
  ("functionTypeName", [.fnType]),
  ("variableDeclaration", [.varDecl]),
  ("expression", [.index, .slice, .member, .callOptions, .call, .payableConv, .metaType,
    .unaryPrefix, .unarySuffix, .exp, .mulDivMod, .addSub, .shift, .bitAnd, .bitXor, .bitOr,
    .order, .equality, .and, .or, .cond, .assign, .new, .tuple, .inlineArray, .ident, .lit,
    .litUnit, .elemType]),
  ("expression#IndexAccess", [.index]),
  ("expression#IndexRangeAccess", [.slice]),
  ("expression#MemberAccess", [.member]),
  ("expression#FunctionCallOptions", [.callOptions]),
  ("expression#FunctionCall", [.call]),
  ("expression#PayableConversion", [.payableConv]),
  ("expression#MetaType", [.metaType]),
  ("expression#UnaryPrefixOperation", [.unaryPrefix]),
  ("expression#UnarySuffixOperation", [.unarySuffix]),
  ("expression#ExpOperation", [.exp]),
  ("expression#MulDivModOperation", [.mulDivMod]),
  ("expression#AddSubOperation", [.addSub]),
  ("expression#ShiftOperation", [.shift]),
  ("expression#BitAndOperation", [.bitAnd]),
  ("expression#BitXorOperation", [.bitXor]),
  ("expression#BitOrOperation", [.bitOr]),
  ("expression#OrderComparison", [.order]),
  ("expression#EqualityComparison", [.equality]),
  ("expression#AndOperation", [.and]),
  ("expression#OrOperation", [.or]),
  ("expression#Conditional", [.cond]),
  ("expression#Assignment", [.assign]),
  ("expression#NewExpr", [.new]),
  ("expression#Tuple", [.tuple]),
  ("expression#InlineArray", [.inlineArray]),
  ("expression#PrimaryExpression", [.ident, .lit, .litUnit, .elemType]),
  ("tupleExpression", [.tuple]),
  ("inlineArrayExpression", [.inlineArray]),
  ("literal", [.lit]),
  ("literalWithSubDenomination", [.litUnit]),
  ("block", [.block]),
  ("uncheckedBlock", [.uncheckedItem]),
  ("statement", [.blockStmt, .simpleStmt, .stmtItem]),
  ("simpleStatement", [.simpleStmt, .declVar, .declTuple, .exprStmt]),
  ("ifStatement", [.ifStmt]),
  ("forStatement", [.forStmt]),
  ("whileStatement", [.whileStmt]),
  ("doWhileStatement", [.doWhile]),
  ("continueStatement", [.continueStmt]),
  ("breakStatement", [.breakStmt]),
  ("tryStatement", [.tryStmt]),
  ("catchClause", [.catchPlain, .catchSig]),
  ("returnStatement", [.returnStmt]),
  ("emitStatement", [.emit]),
  ("revertStatement", [.revert]),
  ("assemblyStatement", [.assembly]),
  ("variableDeclarationTuple", [.declTuple]),
  ("variableDeclarationStatement", [.declVar, .declTuple]),
  ("expressionStatement", [.exprStmt]),
  ("mappingType", [.mapping]),
  ("yulStatement", [.yulBlock, .yulLet, .yulAssign, .yulExprStmt, .yulIf, .yulFor, .yulSwitch,
    .yulLeave, .yulBreak, .yulContinue, .yulFun]),
  ("yulBlock", [.yulBlock]),
  ("yulVariableDeclaration", [.yulLet]),
  ("yulAssignment", [.yulAssign]),
  ("yulIfStatement", [.yulIf]),
  ("yulForStatement", [.yulFor]),
  ("yulSwitchCase", [.yulCase]),
  ("yulSwitchStatement", [.yulSwitch]),
  ("yulFunctionDefinition", [.yulFun]),
  ("yulPath", [.yulPath]),
  ("yulFunctionCall", [.yulCall]),
  ("yulLiteral", [.yulLit]),
  ("yulExpression", [.yulPath, .yulCall, .yulLit])]

/-- Parser rules represented by a datatype or a field. -/
def grammarData : List (String × String) := [
  ("path", "String (the import path)"),
  ("identifierPath", "IdPath"),
  ("visibility", "Visibility, StateVis, CtorVis"),
  ("stateMutability", "Mutability"),
  ("overrideSpecifier", "Option (List IdPath)"),
  ("userDefinableOperator", "UserOp"),
  ("dataLocation", "DataLoc"),
  ("assignOp", "AssignOp"),
  ("identifier", "String"),
  ("booleanLiteral", "Lit"),
  ("stringLiteral", "Lit"),
  ("hexStringLiteral", "Lit"),
  ("unicodeStringLiteral", "Lit"),
  ("numberLiteral", "NumLit"),
  ("assemblyFlags", "List String"),
  ("variableDeclarationList", "unused by the grammar's other rules"),
  ("mappingKeyType", "MapKey"),
  ("yulBoolean", "YulLit")]

/-- Manifest features that are syntax, with their constructors. -/
def featureCtors : List (String × List Ctor) := [
  ("addressTypes", [.elem]), ("arithmetic", [.exp, .mulDivMod, .addSub, .unaryPrefix]),
  ("assignment", [.assign]), ("bitwise", [.bitAnd, .bitXor, .bitOr, .unaryPrefix]),
  ("blocks", [.block, .blockStmt]), ("boolType", [.elem]), ("booleanLiterals", [.lit]),
  ("breakStatement", [.breakStmt]), ("callOptions", [.callOptions]),
  ("calldataLocation", [.param, .varDecl]), ("canonicalRethrow", [.assembly]),
  ("catchClauses", [.catchPlain, .catchSig]), ("comparisons", [.order, .equality]),
  ("compoundAssignment", [.assign]), ("conditional", [.cond]),
  ("constants", [.constant, .stateVar]), ("constructors", [.constructor]),
  ("continueStatement", [.continueStmt]), ("contracts", [.contract]),
  ("deleteExpression", [.unaryPrefix]), ("doWhileStatement", [.doWhile]),
  ("dynamicArrays", [.array]), ("dynamicBytesType", [.elem]), ("emitStatement", [.emit]),
  ("enumDeclarations", [.enum]), ("enumTypes", [.userType]),
  ("errorDeclarations", [.error, .errorParam]), ("etherUnits", [.litUnit]),
  ("eventDeclarations", [.event, .eventParam]),
  ("explicitConversions", [.call, .payableConv, .elemType]),
  ("expressionStatements", [.exprStmt]), ("externalFunctionTypes", [.fnType]),
  ("fallbackFunction", [.fallback, .fbNoParams, .fbParams]), ("fixedArrays", [.array]),
  ("fixedBytesTypes", [.elem]), ("fixedPoint", [.elem]), ("forStatement", [.forStmt]),
  ("freeFunctions", [.topPart, .function]), ("functionCalls", [.call]),
  ("functions", [.function]), ("hexLiterals", [.lit]), ("identifiers", [.ident]),
  ("ifStatement", [.ifStmt]), ("immutables", [.stateVar]),
  ("imports", [.importPath, .importSymbols, .importStar, .importAlias]),
  ("increments", [.unaryPrefix, .unarySuffix]), ("indexAccess", [.index]),
  ("inheritance", [.inherit]), ("inlineArrays", [.inlineArray]),
  ("inlineAssembly", [.assembly]), ("integerTypes", [.elem]), ("interfaces", [.interface]),
  ("internalFunctionTypes", [.fnType]), ("libraries", [.library]),
  ("mappings", [.mapping]), ("memberAccess", [.member]), ("memoryLayout", [.assembly]),
  ("memoryLocation", [.param, .varDecl]), ("metaTypeExpression", [.metaType]),
  ("modifiers", [.modifier, .modInv]), ("namedArguments", [.named, .namedArg]),
  ("names", [.ident, .member]), ("newMemory", [.new]), ("numericLiterals", [.lit]),
  ("operatorAliases", [.usingAliases, .usingAlias]),
  ("overrideDeclarations", [.function, .modifier, .stateVar]), ("parentheses", [.tuple]),
  ("pragmaAbicoder", [.pragma]), ("pragmaOther", [.pragma]), ("pragmaVersion", [.pragma]),
  ("rangeAccess", [.slice]), ("receiveFunction", [.receive]),
  ("removedGenericSolidity", [.pragma]), ("removedUnits", [.litUnit]),
  ("returnStatement", [.returnStmt]), ("revertStatement", [.revert]), ("shifts", [.shift]),
  ("shortCircuit", [.and, .or]), ("sourceUnits", [.unit, .topPart]),
  ("stateMutability", [.function, .fnType]), ("stateVariables", [.stateVar]),
  ("storageLayout", [.contract]), ("storageLocation", [.param, .varDecl]),
  ("stringLiterals", [.lit]), ("stringType", [.elem]), ("structConstruction", [.call]),
  ("structDeclarations", [.struct, .structMember]), ("structTypes", [.userType]),
  ("timeUnits", [.litUnit]), ("transientState", [.stateVar]), ("tryStatement", [.tryStmt]),
  ("tupleExpressions", [.tuple]), ("tupleTypes", [.tuple, .declTuple]),
  ("unaryArithmetic", [.unaryPrefix]), ("uncheckedBlock", [.uncheckedItem]),
  ("unicodeLiterals", [.lit]), ("unsignedRightShift", [.shift, .assign]),
  ("usingFor", [.usingPart, .usingPath, .usingAliases]), ("valueTypeDeclarations", [.udvt]),
  ("valueTypes", [.udvt]), ("variableDeclarations", [.declVar, .declTuple, .varDecl]),
  ("visibility", [.function, .stateVar, .fnType]), ("whileStatement", [.whileStmt])]

/-- Manifest syntax features below the abstract syntax: lexical classes and
spellings (G08). -/
def featureLexical : List String := ["comments", "invalidLexemes", "reservedKeywords"]

/-- Whether a constructor represents some grammar rule. -/
def Ctor.inGrammar (k : Ctor) : Bool := grammarCtors.any fun r => r.2.contains k

/-- **Every constructor has an upstream origin**: it is structural (a
repetition or option) or represents a rule or labelled alternative of the
pinned grammar. -/
theorem Ctor.grammar_covers : ∀ k ∈ Ctor.all, k.structural = true ∨ k.inGrammar = true := by
  decide +kernel

/-- Every exclusion is a manifest syntax feature represented by the
constructors that trigger it. -/
theorem Excl.mapped : ∀ f ∈ [Excl.inlineAssembly, .storageLayout, .unsignedRightShift,
    .removedUnits, .removedGenericSolidity], (featureCtors.lookup f.id).isSome = true := by
  decide +kernel

end Solidity.Source
