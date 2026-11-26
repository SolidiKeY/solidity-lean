import Solidity.Frontend.SolcJson.CallMetadataControls
import Solidity.Frontend.SolcJson.IrImportControls
import Solidity.Frontend.SolcJson.TryPanicSourceCaller
import Solidity.Frontend.SolcJson.TryPanicSourcePlan
import Solidity.Frontend.SolcJson.YulOccurrenceSchema
import Solidity.SolcValidation.IrCensusParse
import Solidity.Interfaces.FrontendExecution
import Solidity.Interfaces.FrontendValidation
import Solidity.Tools.Goal

/-! The public accepting/rejecting entry points of the solc JSON and IR readers.
Private checks are represented by their public caller. Execution evaluators and
total rendering/collection helpers are not acceptance checks. -/

namespace Solidity.Goals.FrontendValidation

/-- Frozen validator inventory for the frontend validation and connection goals. -/
def validators : List Lean.Name :=
  [
    ``Frontend.Source.ScopeScan.ensure, ``Frontend.J.get, ``Frontend.J.opt, ``Frontend.J.str,
    ``Frontend.J.arr, ``Frontend.J.str?, ``Frontend.J.arr?, ``Frontend.J.ref?,
    ``Frontend.J.id?, ``Frontend.J.hasOperatorFunction, ``Frontend.J.operatorFunction?, ``Frontend.J.typeRef?,
    ``Frontend.builtinNamed, ``Frontend.nativeMember, ``Frontend.storedFunctionMemberType?, ``Frontend.solcArrayLength?,
    ``Frontend.tyText, ``Frontend.abiTyText, ``Frontend.tyOf, ``Frontend.mentionsStruct,
    ``Frontend.mentionsThroughMapping, ``Frontend.ownStructMembers, ``Frontend.specBuiltinHead, ``Frontend.specReadsName,
    ``Frontend.specHasFilteredMembership, ``Frontend.valueTypeSupported, ``Frontend.valueTypeExpr, ``Frontend.operatorAlias?,
    ``Frontend.Q.make, ``Frontend.Q.add, ``Frontend.Q.sub, ``Frontend.Q.mul,
    ``Frontend.Q.div, ``Frontend.Q.int?, ``Frontend.Q.pow, ``Frontend.parseRational,
    ``Frontend.constTy, ``Frontend.constVal, ``Frontend.compound, ``Frontend.declarationSelector,
    ``Frontend.isPublicGetterMember, ``Frontend.declarationMetadata, ``Frontend.typeBound?, ``Frontend.nameOf,
    ``Frontend.pushedTy, ``Frontend.storageRefTy, ``Frontend.isPushCall, ``Frontend.isPushedMember,
    ``Frontend.abiEnumPositions, ``Frontend.staticCompilerLength?, ``Frontend.staticCompilerBytes?, ``Frontend.isBaseMember,
    ``Frontend.isExternalMember, ``Frontend.isValueCallee, ``Frontend.isSuperMember, ``Frontend.pureExpr,
    ``Frontend.condCalleeOk, ``Frontend.condCallee?, ``Frontend.validHexBytes, ``Frontend.byteLiteralText,
    ``Frontend.abiUnparen?, ``Frontend.abiHexDigits?, ``Frontend.abiHexLiteral?, ``Frontend.abiCallComponents?,
    ``Frontend.abiCallBytesParams?, ``Frontend.errorAggregateHasEnum, ``Frontend.checkErrorAggregateParams, ``Frontend.expr,
    ``Frontend.assignText, ``Frontend.operand, ``Frontend.call, ``Frontend.isTuple,
    ``Frontend.isNamedCall, ``Frontend.valueCall?, ``Frontend.inertTypeExpression, ``Frontend.tuple,
    ``Frontend.tupleValue, ``Frontend.tupleAssignmentLeaves, ``Frontend.explicitTupleAssignment, ``Frontend.declText,
    ``Frontend.memoryRethrow?, ``Frontend.stmt, ``Frontend.block, ``Frontend.localStmt,
    ``Frontend.stmt1, ``Frontend.loopSpec, ``Frontend.CallMetadata.readProfile, ``Frontend.CallMetadata.outerQualifiers?,
    ``Frontend.CallMetadata.staticTarget?, ``Frontend.CallMetadata.Info.isStatic, ``Frontend.CallMetadata.inspect, ``Frontend.CallMetadata.check,
    ``Frontend.CallMetadata.Controls.profile, ``Frontend.CallMetadata.Controls.summary, ``Frontend.CallMetadata.walk, ``Frontend.CallMetadata.locate,
    ``Frontend.CallMetadata.Located.descend, ``Frontend.CallMetadata.attach, ``Frontend.CallMetadata.locateDeclarations, ``Frontend.CallMetadata.attachPaths,
    ``Frontend.tagWord?, ``Frontend.keyClause, ``Frontend.keyClauses, ``Frontend.ledgerAssignable,
    ``Frontend.declarationOwner, ``Frontend.isSpecified, ``Frontend.tagOf, ``Frontend.FiniteDispatch.parseType,
    ``Frontend.FiniteDispatch.parseCallable, ``Frontend.nativePaymentCallee, ``Frontend.nativePayment, ``Frontend.writingCall,
    ``Frontend.reach, ``Frontend.checkedReach, ``Frontend.metadataIds, ``Frontend.overrideAliases,
    ``Frontend.mergeC3, ``Frontend.contractLineage, ``Frontend.storageTuplePlan?, ``Frontend.renderInitializers,
    ``Frontend.readContractWithNormalizationV1, ``Frontend.readContract, ``Frontend.sourceAbiType, ``Frontend.sourceAbiSignature,
    ``Frontend.sourceFunction, ``Frontend.publicGetterPlan, ``Frontend.getterNominalSignature, ``Frontend.publicGetterIdentity,
    ``Frontend.SolcJson.Ir.select, ``Frontend.SolcJson.Ir.selectContract, ``Frontend.SolcJson.Ir.lookup, ``Frontend.SolcJson.Ir.Controls.extracted,
    ``Frontend.TryPanicSourceCaller.argument?, ``Frontend.TryPanicSourcePlan.intField, ``Frontend.TryPanicSourcePlan.boolField, ``Frontend.TryPanicSourcePlan.memberAt,
    ``Frontend.TryPanicSourcePlan.unsignedText?, ``Frontend.TryPanicSourcePlan.literal?, ``Frontend.YulJson.field, ``Frontend.YulJson.string,
    ``Frontend.YulJson.array, ``Frontend.YulJson.requireNode, ``Frontend.YulJson.emptyAnnotation, ``Frontend.YulJson.finishLiteral,
    ``Frontend.YulJson.literal, ``Frontend.YulJson.identifierPath, ``Frontend.YulJson.functionName, ``Frontend.YulJson.expressionAux,
    ``Frontend.YulJson.expression, ``Frontend.YulJson.checkExpression, ``Frontend.YulJson.checkExpressionText, ``Frontend.YulJson.typedName,
    ``Frontend.YulJson.names, ``Frontend.YulJson.optionalNames, ``Frontend.YulJson.switchCases, ``Frontend.YulJson.parseBlock,
    ``Frontend.YulJson.parseBlockText, ``Frontend.YulJson.checkBlockShape, ``Frontend.YulJson.checkBlockShapeText, ``Frontend.YulJson.ReferenceAttachment.checkUse,
    ``Frontend.YulJson.BuiltinGuard.parse, ``Frontend.YulJson.BuiltinGuard.checkJson, ``Frontend.YulJson.BuiltinGuard.checkJsonText, ``Frontend.YulJson.ForwardJson.check,
    ``Frontend.YulJson.ForwardJson.checkText, ``Frontend.YulJson.identify, ``Frontend.YulJson.checkDeclarationTable, ``Frontend.YulJson.decimal,
    ``Frontend.YulJson.sourceSpan, ``Frontend.YulJson.natural, ``Frontend.YulJson.boolean, ``Frontend.YulJson.reference,
    ``Frontend.YulJson.references, ``Frontend.YulJson.metadata, ``Frontend.YulJson.MetadataWords.input?, ``Frontend.YulJson.MetadataWords.check,
    ``Frontend.YulJson.Names.select, ``Frontend.YulJson.Names.checkReference, ``Frontend.YulJson.Names.entry?, ``Frontend.YulJson.Occurrences.checkChildren,
    ``Frontend.YulJson.Occurrences.collect, ``Frontend.YulJson.Occurrences.isIdentifier, ``Frontend.YulJson.Occurrences.includeField, ``Frontend.YulJson.ReferenceAttachment.check,
    ``Frontend.YulJson.ReferenceCover.candidate, ``Frontend.YulJson.ReferenceCover.check, ``Frontend.YulJson.ReferenceCover.checkAll, ``Frontend.YulJson.spaceTab,
    ``Frontend.YulJson.docWhitespace, ``Frontend.YulJson.tagSeparator, ``Frontend.YulJson.docTagsAux, ``Frontend.YulJson.documentationTags,
    ``Frontend.YulJson.checkMetadataSafety, ``Frontend.YulJson.ScopedJson.check, ``Frontend.YulJson.ScopedJson.checkText, ``Frontend.YulJson.ScopedParse.check,
    ``Frontend.YulJson.Words.check, ``Frontend.YulJson.Words.checkText, ``Frontend.Admission.scan, ``Frontend.YulJson.blockAux,
    ``Frontend.YulJson.statementAux, ``Frontend.FiniteDispatch.candidate, ``SolcValidation.selectData, ``SolcValidation.DataTable.select,
    ``SolcValidation.IrSyntax.hexDigit?, ``SolcValidation.IrSyntax.toByte?, ``SolcValidation.IrSyntax.escapeByte, ``SolcValidation.IrSyntax.decodeString,
    ``SolcValidation.IrSyntax.stringWord, ``SolcValidation.IrSyntax.LitTok.decode, ``SolcValidation.IrSyntax.isIdStart, ``SolcValidation.IrSyntax.isIdChar,
    ``SolcValidation.IrSyntax.lexString, ``SolcValidation.IrSyntax.lexHex, ``SolcValidation.IrSyntax.dropBlock, ``SolcValidation.IrSyntax.hexValue,
    ``SolcValidation.IrSyntax.lexNumber, ``SolcValidation.IrSyntax.lexGo, ``SolcValidation.IrSyntax.lex, ``SolcValidation.IrSyntax.findVar,
    ``SolcValidation.IrSyntax.findFn, ``SolcValidation.IrSyntax.mkLit, ``SolcValidation.IrSyntax.litTok?, ``SolcValidation.IrSyntax.reserved,
    ``SolcValidation.IrSyntax.freshNames, ``SolcValidation.IrSyntax.single, ``SolcValidation.IrSyntax.parseExpr, ``SolcValidation.IrSyntax.parseArgs,
    ``SolcValidation.IrSyntax.parseArgs1, ``SolcValidation.IrSyntax.parseCall, ``SolcValidation.IrSyntax.parseHeader, ``SolcValidation.IrSyntax.scanSigs,
    ``SolcValidation.IrSyntax.assemble, ``SolcValidation.IrSyntax.resolveTargets, ``SolcValidation.IrSyntax.parseInit, ``SolcValidation.IrSyntax.parseBlock,
    ``SolcValidation.IrSyntax.parseItems, ``SolcValidation.IrSyntax.parseStmt, ``SolcValidation.IrSyntax.parseCases, ``SolcValidation.IrSyntax.parseLoop,
    ``SolcValidation.IrSyntax.parseObject, ``SolcValidation.IrSyntax.parseChildren, ``SolcValidation.IrSyntax.nodupNames, ``SolcValidation.IrSyntax.declOk,
    ``SolcValidation.IrSyntax.nodupWords, ``SolcValidation.IrSyntax.Expr.wf, ``SolcValidation.IrSyntax.Args.wf, ``SolcValidation.IrSyntax.initWf,
    ``SolcValidation.IrSyntax.Stmt.wf, ``SolcValidation.IrSyntax.Cases.wf, ``SolcValidation.IrSyntax.Cases.nonempty, ``SolcValidation.IrSyntax.Loop.wf,
    ``SolcValidation.IrSyntax.Items.wf, ``SolcValidation.IrSyntax.Block.wf, ``SolcValidation.IrSyntax.Bodies.wf, ``SolcValidation.IrSyntax.objectWf,
    ``SolcValidation.IrSyntax.objectsWf, ``SolcValidation.IrSyntax.parse, ``SolcValidation.IrSyntax.Expr.ren, ``SolcValidation.IrSyntax.Args.ren,
    ``SolcValidation.IrSyntax.initRen, ``SolcValidation.IrSyntax.Stmt.ren, ``SolcValidation.IrSyntax.Cases.ren, ``SolcValidation.IrSyntax.Loop.ren,
    ``SolcValidation.IrSyntax.Items.ren, ``SolcValidation.IrSyntax.Block.ren, ``SolcValidation.IrSyntax.Bodies.ren, ``SolcValidation.IrSyntax.parsesTo,
    ``SolcValidation.IrSyntax.namesNodup
  ]

end Solidity.Goals.FrontendValidation

namespace Solidity.Goals
open Solidity.Goal Interfaces.FrontendExecution Interfaces.FrontendValidation

/-- Authenticated external execution, followed by structural acceptance guarantees.
Exercise coverage of the frozen entry-point list is the separate f1b obligation. -/
@[goal Solidity.Frontend.validators_exercised "f1a-frontend-validation-goal"]
def frontendValidatorsExercised : Prop :=
  ∀ (env : Environment) (compiler : Frontend.Source.Compiler) (artifact : ByteArray)
    (inputText outputText : String) (input output : Lean.Json),
    Faithful env compiler artifact inputText outputText input output →
    JsonFields ∧ IrAtoms ∧ RationalChecks ∧ ReaderChecks ∧ CallChecks ∧ YulChecks ∧
    ∀ source contract mode text, SelectedIr output source contract mode text → IrChecks text
end Solidity.Goals
