# Testing Solidity files

The Lean API can compile a `.sol` source, discover its contracts and functions,
generate their obligations, and check proofs. Run it from the repository root:

```sh
node scripts/test-solidity.mjs path/to/Test.sol
node scripts/test-solidity.mjs --json path/to/test-directory
node scripts/test-solidity.mjs --contract Test --function example path/to/Test.sol
node scripts/test-solidity.mjs --list path/to/test-directory
```

Directories are recursive, sorted and deduplicated. Every source is compiled
once with `scripts/solc-ast.mjs`, using the SHA-checked compiler pinned by the
SolKey checkout. The runner builds `Solidity.Frontend.Testing` once and processes
contracts sequentially. `--solkey DIR` (or `SOLKEY_ROOT`) and `--soljson DIR`
select the checkout and compiler directory. No npm or Lean package dependency
is added. `--no-build` uses already built modules.

This follows SolKey's `SolidityExampleTests.contractFunctions` and
`SolidityProblemSpec`: discover functions from the source, select by contract
and function, and synthesize each obligation from its NatSpec tags. It uses
Lean's existing frontend and calculus rather than the Java remote API.

Plain functions have the diamond obligation; `@custom:key box` selects the box.
Specified functions use `cspec[C]{f}` and `sol_spec_try`, including their
`requires`, `ensures`, and contract invariants. Explicit constructors use the
existing deployment obligations. Internal functions are helpers rather than
independent obligations. These are verification obligations over typed states
and all arguments, not calls at a few concrete inputs.

| Result | Meaning |
|---|---|
| `proved` | Kernel-checked proof, using only Lean's standard three axioms. |
| `pending` | Open goals, incomplete proof, or a search/kernel budget failure; no claim of falsity. |
| `skipped` / `skip` | Explicit NatSpec skip tag. |
| `internal` | Internal helper; no independent obligation. |
| `unsupported` / `excluded` | An import or obligation gap; prevents suite success. |
| `ready` | Listing only; no proof attempted. |
| `notRun` | Contract process interrupted before this function completed. |

The JSON report is `{results, errors}`. Each result includes the absolute source
path, contract, function, tag, status, reason and elapsed milliseconds. Compiler,
contract import and subprocess failures appear in `errors`. Importer warnings
about omitted initializers also appear there and prevent success. A result file
is checkpointed before search and after each function, preserving completed
rows and marking unattempted ones if a process times out.

Exit status is 0 only when at least one obligation is proved (or ready in list
mode), every other row is proved or deliberately skipped/internal, and there
are no errors. Status 1 means a suite has pending/gap/error results; status 2
means an invocation, discovery or initial build failure. A suite containing
only skipped functions cannot pass. `--timeout-ms N` bounds each subprocess,
including the initial build and each whole-contract Lean invocation (default
120000 ms). Lean's existing per-step limits and ambient heartbeat limit also
apply. A timeout is not an expected-open verdict.

The JavaScript API exports `solidityFiles(paths)`,
`runSolidityTests(paths, options)`, and `testsPassed(report, listing)` from
`scripts/test-solidity.mjs`. It is synchronous. The options are `contract`,
`function`, `list`, `timeoutMs`, `solkey`, `soljson` and `build`.

For an existing solc fixture, the Lean entry point is:

```lean
import Solidity.Frontend.Testing

solc_import "Example.ast.json" hash 0xHASH as Imported.Example testing
solc_scoped_problems Imported.Example decl
#solkey_test Imported.Example to "/tmp/results.json"
-- Optional: only "functionName", then listing, before `to`.
```

The hash must be the fixture's actual FNV-1a hash, as written by
`scripts/solc-ast.mjs`. Direct Lean callers must inspect the import's diagnostics
as well as the result file; the file runner does this automatically.
The explicit `testing` import mode retains NatSpec clauses and all callable
function declarations. The original import mode retains only declarations
needed for internal calls. Specifications requiring renamed locals are
reported as unsupported, contract-level specification clauses must be
invariants, and function-level invariants are refused. Unsupported clause
syntax remains an import failure.

The runner exposes frontend limitations: Solidity source imports/remappings,
inheritance and unsupported AST forms are not added by this API. The current
compiler helper reads one source unit, and the Lean frontend reads each
contract's own members. Expected-open suites will need a separate expectation
manifest when the SolKey corpus is imported; `pending` alone does not certify
an invalid specification. The SolKey test sources have not been copied yet.

## Verification and review

`node --test scripts/test-solidity.test.mjs` exercises compilation, multiple
contracts, parameterized assertions, true and false specifications, box versus
diamond on revert, internal/skip tags, unsupported assembly, omitted implicit
initializers, selection and listing. Per-file Lean diagnostics check the API.

The milestone's read-only finder and skeptic review confirmed the discarded
initializer warning could silently hide coverage. The runner now retains it
as an error, with a regression. The finder also identified whole-contract
timeouts losing earlier rows; checkpointing now retains results and marks
unattempted functions explicitly.
The skeptic found contract invariants lost when the initializer member list
replaced the plain member list. Both lists now carry the invariants. Regressions
require an invariant-breaking function and constructor to stay pending.
Both reviewers also identified function-level invariants becoming global
premises and a lost `payable` flag weakening specification premises. Testing
imports now refuse function-level invariants, and function members preserve
`payable`; both boundaries have source-to-proof regressions.
Each NatSpec clause is also parsed independently before it is included in a
contract, preventing a malformed expression from introducing another member
and changing the obligation's premises.

Validation on 2026-10-15:

- Per-file Lean MCP diagnostics: no errors in the changed frontend modules.
- `node --test scripts/test-solidity.test.mjs`: 6 passed, 0 failed.
- CLI smoke test with automatic build: `ScopedFlip.additionStorageWrite` proved.
- SolKey's actual `benchmark/Counter.sol`, selecting `Counter.inc`: specified
  obligation proved, with no import errors.
- `./run-lean.sh`: default build and all `SolkeyTestSuite` modules passed;
  the final `solkeycheck` failed on four annotation mismatches against the
  current sibling checkout (336 taclets versus this repository's older pin).
- `node scripts/check-orphans.mjs`: 296 reachable, zero orphaned.
- `git diff --check`: passed.
- `./scripts/check-doc-paths.sh`: six pre-existing missing references in
  `vendor/LeanTeX/VENDOR.md`.
- `./scripts/check-testsuite.sh`: the sibling SolKey TestSuite source hash
  differs from the pinned AST fixture. Re-importing the suite and re-pinning
  annotations are separate changes, not part of this API milestone.
