import Solidity.Frontend.Import

/-!
# solkey's `TestSuite.sol`, imported from solc's AST

The fixture is `tests/solc/TestSuite.ast.json`, written by
`scripts/solc-ast.mjs` with the soljson solkey pins and checked by
`scripts/check-solc-ast.sh`; the script rewrites the hash below, in the
import and in the stale-fixture test's expected message.  The struct
`Triple { uint[3] items; uint tag; }` is the table's `FixedTriple`
(`Semantics.structDef`: `Triple` is another contract's).
-/

solc_import "../../tests/solc/TestSuite.ast.json" hash 0x1ec4bfde1445b2df as Solkey.TestSuite
  renaming Triple => FixedTriple

/-! The pinned migration source, including explicit unsupported rows.
An unsupported function has no program or proof obligation. -/

/--
info: 617 functions (436 diamond, 128 box, 2 skip, 51 internal): 579 elaborated, 2 skipped, 1 excluded, 35 unsupported
unsupported storageArrayMethodReferences: TestSuite.sol:352: the printed text does not parse: <input>:1:35: expected '=', 'storage' or identifier
unsupported storageArrayMethodReferencesComplexReceiver: TestSuite.sol:362: the printed text does not parse: <input>:1:102: expected '='
unsupported storageArrayMethodReferencesComposedCallReceiver: TestSuite.sol:401: a member of a pushed element (`x.push().f`) other than an assignment's left-hand side of a constant or a declaration's whole initial value: hoisting the push would change solc's order of evaluation
unsupported storageArrayMethodReferencesCallReceiver: TestSuite.sol:411: the printed text does not parse: <input>:1:40: expected '='
unsupported storagePopReferenceOutOfBounds: TestSuite.sol:421: the printed text does not parse: <input>:1:38: expected '='
unsupported storagePopReferenceCallOutOfBounds: TestSuite.sol:428: the printed text does not parse: <input>:1:46: expected ';'
unsupported logicalAndStorageAssignment: TestSuite.sol:599: the printed text does not parse: <input>:1:58: expected ')' or ','
unsupported logicalOrStorageAssignment: TestSuite.sol:606: the printed text does not parse: <input>:1:57: expected ')' or ','
unsupported storageAssignmentValueNested: TestSuite.sol:613: the printed text does not parse: <input>:1:25: expected ')' or ','
unsupported storageAssignmentValueIndexOnce: TestSuite.sol:622: the printed text does not parse: <input>:1:79: expected ')' or ','
unsupported storageAssignmentValueRhsBeforeIndex: TestSuite.sol:631: the printed text does not parse: <input>:1:61: expected ')' or ','
unsupported logicalAndStorageAssignmentSkipsIndex: TestSuite.sol:639: the printed text does not parse: <input>:1:70: expected ')' or ','
unsupported logicalOrStorageAssignmentSkipsIndex: TestSuite.sol:646: the printed text does not parse: <input>:1:68: expected ')' or ','
unsupported unprovableStorageShortCircuitMutation: TestSuite.sol:653: the printed text does not parse: <input>:1:48: expected ')' or ','
excluded recursiveStructMapping: TestSuite.sol:2973: struct `Tree` (line 64) is recursive through a mapping: its default value is infinite, and the model's are finite
unsupported memoryIndexWriteStorageRefRhsCapture: TestSuite.sol:3105: a memory reference is expected
unsupported memoryIndexWriteStorageStructCopy: TestSuite.sol:3123: a memory reference is expected
unsupported memoryIndexWriteStorageRefImpureIndex: TestSuite.sol:3142: a memory reference is expected
unsupported memoryIndexWriteStorageRefOutOfBoundsReverts: TestSuite.sol:3150: a memory reference is expected
unsupported memoryIndexWriteStorageRefSourceOutOfBoundsReverts: TestSuite.sol:3158: a memory reference is expected
skipped tryCalleeGet: TestSuite.sol:3804: tagged `@custom:key skip`
skipped tryCalleePing: TestSuite.sol:3809: tagged `@custom:key skip`
unsupported bitAndOneValues: TestSuite.sol:3888: operator & does not take int
unsupported bitAndGeneralValues: TestSuite.sol:3900: operator & does not take int
unsupported bitAndSymbolic: TestSuite.sol:3909: operator & does not take int
unsupported conditionalCallee: TestSuite.sol:3934: a call's callee is a function's name
unsupported conditionalCalleeEffects: TestSuite.sol:3947: only push, pop and transfer are calls on a receiver
unsupported invariantQuantifiedOverPrefix: TestSuite.sol:4485: the loop clause `invariant \forall uint q; 0 <= q && q < i -> values[q] == 0`: the specification language
unsupported conditionalContinuationBody: TestSuite.sol:4686: modifier solcModifier19451: `return` in a modifier
unsupported modifierSkippedPlaceholder: TestSuite.sol:4695: modifier solcModifier19451: `return` in a modifier
unsupported modifierTakenPlaceholder: TestSuite.sol:4702: modifier solcModifier19451: `return` in a modifier
unsupported nestedReturningContinuation: TestSuite.sol:4719: modifier solcModifier19545: `return` in a modifier
unsupported modifierReturnResumesOuterSuffix: TestSuite.sol:4728: modifier solcModifier19545: `return` in a modifier
unsupported arithmeticAssignmentValues: TestSuite.sol:5026: the printed text does not parse: <input>:1:39: expected ';'
unsupported arithmeticDiscardKeepsSideEffects: TestSuite.sol:5042: the printed text does not parse: <input>:1:34: expected '='
unsupported arithmeticDiscardKeepsZeroDivisorRevert: TestSuite.sol:5059: the printed text does not parse: <input>:1:75: expected '='
unsupported testShiftRightNegativeRoundsDown: TestSuite.sol:5119: operator >> does not take int
unsupported testShiftOperandEvaluation: TestSuite.sol:5131: the printed text does not parse: <input>:1:39: expected ')' or ','
-/
#guard_msgs in
#eval IO.println (Solidity.Frontend.ImportRow.summary Solkey.TestSuite.report)

/-! A fixture of another hash is refused: the module would be stale. -/

/--
error: ../../tests/solc/TestSuite.ast.json has the hash 0x1ec4bfde1445b2df, not the one named: re-run scripts/solc-ast.mjs, which rewrites the literal
-/
#guard_msgs in
solc_import "../../tests/solc/TestSuite.ast.json" hash 0x1 as Solkey.Stale
