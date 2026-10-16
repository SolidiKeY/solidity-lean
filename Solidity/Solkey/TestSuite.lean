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

solc_import "../../tests/solc/TestSuite.ast.json" hash 0x6553ea1d6de3da1f as Solkey.TestSuite
  renaming Triple => FixedTriple

/-! The pinned migration source, including explicit unsupported rows.
An unsupported function has no program or proof obligation. -/

/--
info: 551 functions (397 diamond, 117 box, 2 skip, 35 internal): 547 elaborated, 2 skipped, 1 excluded, 1 unsupported
excluded recursiveStructMapping: TestSuite.sol:2829: struct `Tree` (line 64) is recursive through a mapping: its default value is infinite, and the model's are finite
skipped tryCalleeGet: TestSuite.sol:3599: tagged `@custom:key skip`
skipped tryCalleePing: TestSuite.sol:3604: tagged `@custom:key skip`
unsupported invariantQuantifiedOverPrefix: TestSuite.sol:4140: the loop clause `invariant \forall uint q; 0 <= q && q < i -> values[q] == 0`: the specification language
-/
#guard_msgs in
#eval IO.println (Solidity.Frontend.ImportRow.summary Solkey.TestSuite.report)

/-! A fixture of another hash is refused: the module would be stale. -/

/--
error: ../../tests/solc/TestSuite.ast.json has the hash 0x6553ea1d6de3da1f, not the one named: re-run scripts/solc-ast.mjs, which rewrites the literal
-/
#guard_msgs in
solc_import "../../tests/solc/TestSuite.ast.json" hash 0x1 as Solkey.Stale
