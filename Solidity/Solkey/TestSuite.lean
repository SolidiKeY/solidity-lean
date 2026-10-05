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

solc_import "../../tests/solc/TestSuite.ast.json" hash 0x4610a0af28d984e0 as Solkey.TestSuite
  renaming Triple => FixedTriple

/-! What became of each function: every one but the two solkey skips and the
struct recursive through a mapping is a program of the imported contract. -/

/--
info: 420 functions (316 diamond, 102 box, 2 skip): 417 elaborated, 2 skipped, 1 excluded, 0 unsupported
excluded recursiveStructMapping: TestSuite.sol:2741: struct `Tree` (line 36) is recursive through a mapping: its default value is infinite, and the model's are finite
skipped tryCalleeGet: TestSuite.sol:3483: tagged `@custom:key skip`
skipped tryCalleePing: TestSuite.sol:3488: tagged `@custom:key skip`
-/
#guard_msgs in
#eval IO.println (Solidity.Frontend.ImportRow.summary Solkey.TestSuite.report)

/-! A fixture of another hash is refused: the module would be stale. -/

/--
error: ../../tests/solc/TestSuite.ast.json has the hash 0x4610a0af28d984e0, not the one named: re-run scripts/solc-ast.mjs, which rewrites the literal
-/
#guard_msgs in
solc_import "../../tests/solc/TestSuite.ast.json" hash 0x1 as Solkey.Stale
