import Solidity.Frontend.ExecutableAst.Shared.Compose
import Solidity.Frontend.ExecutableAst.Shared.Translate
import Solidity.Frontend.ExecutableAst.Shared.Intrinsic
import Solidity.Tools.DirectRuntime

/-! Axiom inventory of executable boundary definitions and three new numerical
freshness theorems in Scope. These bounds do not prove source preservation
or transitive runtime closure. Standard existing axioms are compared
with the pinned base runtime entrypoint separately. -/
#print axioms Solidity.Frontend.ExecutableAst.Shared.Reader
#print axioms Solidity.Frontend.ExecutableAst.Shared.BodyLoopLowerer
#print axioms Solidity.Frontend.ExecutableAst.Shared.PlainEntryPre
#print axioms Solidity.Frontend.ExecutableAst.Shared.assertionObligation
#print axioms Solidity.Frontend.ExecutableAst.Shared.obligation
#print axioms Solidity.Frontend.ExecutableAst.Shared.field
#print axioms Solidity.Frontend.ExecutableAst.Shared.str
#print axioms Solidity.Frontend.ExecutableAst.Shared.arr
#print axioms Solidity.Frontend.ExecutableAst.Shared.arrDefault
#print axioms Solidity.Frontend.ExecutableAst.Shared.node
#print axioms Solidity.Frontend.ExecutableAst.Shared.optional
#print axioms Solidity.Frontend.ExecutableAst.Shared.prim
#print axioms Solidity.Frontend.ExecutableAst.Shared.typeNameStep
#print axioms Solidity.Frontend.ExecutableAst.Shared.typeName
#print axioms Solidity.Frontend.ExecutableAst.Shared.expressionStep
#print axioms Solidity.Frontend.ExecutableAst.Shared.expression
#print axioms Solidity.Frontend.ExecutableAst.Shared.tokens
#print axioms Solidity.Frontend.ExecutableAst.Shared.precedence
#print axioms Solidity.Frontend.ExecutableAst.Shared.specExpr
#print axioms Solidity.Frontend.ExecutableAst.Shared.specification
#print axioms Solidity.Frontend.ExecutableAst.Shared.rawSpec
#print axioms Solidity.Frontend.ExecutableAst.Shared.rawInvariant
#print axioms Solidity.Frontend.ExecutableAst.Shared.loopSpec
#print axioms Solidity.Frontend.ExecutableAst.Shared.statementsStep
#print axioms Solidity.Frontend.ExecutableAst.Shared.statements
#print axioms Solidity.Frontend.ExecutableAst.Shared.params
#print axioms Solidity.Frontend.ExecutableAst.Shared.reader
#print axioms Solidity.Frontend.ExecutableAst.Shared.validateMetadata
#print axioms Solidity.Frontend.ExecutableAst.Shared.checkedExpression
#print axioms Solidity.Frontend.ExecutableAst.Shared.checkedStatements
#print axioms Solidity.Frontend.ExecutableAst.Shared.function
#print axioms Solidity.Frontend.ExecutableAst.Shared.contract
#check Solidity.Tools.DirectRuntime.check
#print axioms Solidity.Tools.DirectRuntime.check
#check Solidity.Tools.DirectRuntime.checkString
#print axioms Solidity.Tools.DirectRuntime.checkString

#print axioms Solidity.Frontend.ExecutableAst.Shared.executableExpression
#print axioms Solidity.Frontend.ExecutableAst.Shared.executableStatements
#print axioms Solidity.Frontend.ExecutableAst.Shared.executableReader

#print axioms Solidity.Frontend.ExecutableAst.Shared.Scope.nextIndex
#print axioms Solidity.Frontend.ExecutableAst.Shared.Scope.le_foldMax
#print axioms Solidity.Frontend.ExecutableAst.Shared.Scope.member_lt_nextIndex
#print axioms Solidity.Frontend.ExecutableAst.Shared.Scope.reservedNames
#print axioms Solidity.Frontend.ExecutableAst.Shared.Scope.bodySeed
#print axioms Solidity.Frontend.ExecutableAst.Shared.Scope.reserved_lt_bodySeed
#print axioms Solidity.Frontend.ExecutableAst.Shared.Scope.validateScopes

-- H90 canonical narrow-local decoding; no source adequacy theorem.
#print axioms Solidity.Frontend.ExecutableAst.Shared.localPrim
#print axioms Solidity.Frontend.ExecutableAst.Shared.localTypeName
#print axioms Solidity.Frontend.ExecutableAst.Shared.localTypeName_of_narrow

#print axioms Solidity.Frontend.ExecutableAst.Shared.primitiveReturnObligation

#print axioms Solidity.Frontend.ExecutableAst.Shared.localTypeName_of_fixedBytes

#print axioms Solidity.Frontend.ExecutableAst.Shared.localValueTypeName_of_address

#print axioms Solidity.Frontend.ExecutableAst.Shared.environmentMember?

#print axioms Solidity.Frontend.ExecutableAst.Shared.environmentMember?_guard

-- Guard valid environment metadata and result-type inversion; no source adequacy claim.
#check Solidity.Frontend.ExecutableAst.Shared.environmentMember?_of_metadata
#print axioms Solidity.Frontend.ExecutableAst.Shared.environmentMember?_of_metadata
#check Solidity.Frontend.ExecutableAst.Shared.environmentMember?_resultType
#print axioms Solidity.Frontend.ExecutableAst.Shared.environmentMember?_resultType

#check Solidity.Frontend.ExecutableAst.Shared.environmentMember?_guards
#print axioms Solidity.Frontend.ExecutableAst.Shared.environmentMember?_guards
