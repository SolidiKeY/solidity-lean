import Solidity.Frontend.ExecutableAst.Shared.Compose
import Solidity.Frontend.ExecutableAst.Shared.Intrinsic
import Solidity.Frontend.ExecutableAst.Shared.Translate
open Solidity.Frontend.ExecutableAst.Shared
#check Reader
#check Reader.typeName
#check Reader.expression
#check Reader.statements
#check Reader.params
#check Reader.specification
#check typeNameStep
#check expressionStep
#check statementsStep
#check reader
#check function
#check contract

#check BodyLoopLowerer
#check PlainEntryPre
#check assertionObligation
#check obligation

#check validateMetadata
#check checkedExpression
#check checkedStatements

#check Solidity.Frontend.ExecutableAst.Shared.executableExpression
#check Solidity.Frontend.ExecutableAst.Shared.executableStatements
#check Solidity.Frontend.ExecutableAst.Shared.executableReader

#check Solidity.Frontend.ExecutableAst.Shared.Scope.nextIndex
#check Solidity.Frontend.ExecutableAst.Shared.Scope.le_foldMax
#check Solidity.Frontend.ExecutableAst.Shared.Scope.member_lt_nextIndex
#check Solidity.Frontend.ExecutableAst.Shared.Scope.reservedNames
#check Solidity.Frontend.ExecutableAst.Shared.Scope.bodySeed
#check Solidity.Frontend.ExecutableAst.Shared.Scope.reserved_lt_bodySeed
#check Solidity.Frontend.ExecutableAst.Shared.Scope.validateScopes

-- H90 canonical narrow-local decoding; no source adequacy theorem.
#check Solidity.Frontend.ExecutableAst.Shared.localPrim
#check Solidity.Frontend.ExecutableAst.Shared.localTypeName
#check Solidity.Frontend.ExecutableAst.Shared.localTypeName_of_narrow

#check Solidity.Frontend.ExecutableAst.Shared.primitiveReturnObligation

#check Solidity.Frontend.ExecutableAst.Shared.localTypeName_of_fixedBytes

#check Solidity.Frontend.ExecutableAst.Shared.localValueTypeName_of_address

#check Solidity.Frontend.ExecutableAst.Shared.environmentMember?

#check Solidity.Frontend.ExecutableAst.Shared.environmentMember?_guard
