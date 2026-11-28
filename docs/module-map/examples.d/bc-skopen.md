| Module | Its examples |
|---|---|
| `Examples/SolkeyOpen/SolcArithmetic.lean` | solkey `semantics/open/SolcArithmetic.sol`: five wrapping obligations proved (`sol_prove`); `checkedCalledByUncheckedWraps` unknown (`+%`, `% 2^16` under parameter equations); `uncheckedIncrementWraps` refuted in the model (checked `2**256`). |
| `Examples/SolkeyOpen/SolcTypes.lean` | solkey `semantics/open/SolcTypes.sol`: twelve cast and enum obligations proved; `nestedTuplesParenthesized` unknown (refused by the front end); `ternaryLiteralOverflow` refuted (`uint8` overflow). |
| `Examples/SolkeyOpen/SolcSmtControlFlow.lean` | solkey `semantics/open/SolcSmtControlFlow.sol`: both `msg.value` obligations proved. |
| `Examples/SolkeyOpen/SolcConstructors.lean` | solkey `semantics/open/SolcConstructors.sol`: deployment, `msgValueZero`, `mappingLocalCompoundAssignment` proved; `immutableUninitialized` refuted; `multipleInitializationsAssignExpr` unknown (does not parse). |
| `Examples/SolkeyOpen/SolcControlFlow.lean` | solkey `semantics/open/SolcControlFlow.sol`: `conditionalExpressionTuples` unknown (conditional of tuples refused by the front end). |
| `Examples/SolkeyOpen/SolcFunctionCalls.lean` | solkey `semantics/open/SolcFunctionCalls.sol`: `functionsRecursiveUnbounded` unknown (diamond of an unbounded recursion). |
| `Examples/SolkeyOpen/ArrayRemoveByShifting.lean` | solkey `contracts/real-world/open/ArrayRemoveByShifting.sol`: `remove` unknown (invariant leaves; the use case owes `ensures` the invariant does not carry). |
