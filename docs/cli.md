# Command line interface

Build the native entry point and the source APIs from the repository root:

```sh
lake build solidity-lean Solidity.Frontend.Cli
.lake/build/bin/solidity-lean --help
```

`lake build` also builds the executable as a default target. Add
`.lake/build/bin` to `PATH` to use `solidity-lean` directly. Commands resolve
source paths against the caller's working directory, including outside the
checkout. Directories are recursive, sorted and deduplicated.

The executable locates runtime scripts beside its checkout. If copying the
binary elsewhere, set `SOLIDITY_LEAN_ROOT` to the original checkout. This is a
native launcher for the existing source pipeline, not a self-contained
distribution: the checkout, Node, the pinned Lean/Lake toolchain, and the
SHA-checked Solidity compiler are runtime requirements. Select the solkey
checkout with `--solkey DIR` or `SOLKEY_ROOT`, and optionally the compiler
directory with `--soljson DIR`. Nothing downloads automatically. The core
still has no package dependencies.

## Verify and discover

```sh
solidity-lean verify Counter.sol
solidity-lean verify contracts/ --json > results.json
solidity-lean verify Token.sol --contract Token --function 'transfer(address,uint256)'
solidity-lean list Token.sol
```

`verify` uses the existing source testing API: actual NatSpec specifications,
constructor obligations, callback interpretation and clean-tail premises.
Every `proved` row has a kernel-checked theorem and passes the standard-axiom
gate. `list` imports the source and generates obligations, but performs no
proof search. A function name selects all its overloads; a source signature
selects one. Source signatures are available from `list --json`, preserving
the frontend's source type names. Selectors accept both `uint`/`uint256` and
`int`/`int256`; punctuation and other type names remain significant.

The statuses retain the [source testing API](solidity-testing.md) meanings:
`proved`, `pending`, `ready`, `unsupported`, `excluded`, `skipped`, `internal`,
`notRun`, and `error`. This source pipeline currently leaves false obligations
`pending`; it does not automatically invoke the native specification
counterexample finder. An open goal never means a certified refutation.
Import omissions and compiler failures prevent verification success.

`--timeout 30s` bounds **each subprocess**: the initial build, compiler, and
each Lean contract/batch invocation. The default is `5m`; integer milliseconds
(`500` or `500ms`), seconds (`30s`) and minutes (`5m`) are accepted. This is
not a total suite deadline. Timed-out jobs retain completed checkpoints and
report an error with `tool.timedOut: true`. Terminal interruption and timeouts
kill the tool's process group, including descendant Lean workers on POSIX.
`--no-build` requires up-to-date
modules. Lean's existing heartbeat budgets also apply.

`--self-address A` (decimal or hexadecimal) adds the deployment-address
premise ([source-inputs.md](source-inputs.md)).

## Inspect

```sh
solidity-lean inspect Counter.sol --function inc --show obligation
solidity-lean inspect Counter.sol --function inc --show goals
solidity-lean inspect Counter.sol --function inc --show tree --json
```

`obligation` is the default. It retains the source input premises and the
clean-tail premise where verification uses it. Specified functions print
their actual specification formula. The report includes the `reading`
(`clean` or `solc`); callback interpretation remains the one documented by
the source testing API.

`goals` runs the same verification attempt and shows its remaining goals;
successful proofs say `No open goals.` Resource failures remain errors.
Recursive proof attempts may give their existing explanatory note instead
of individual goals. Inspecting ordinary open goals succeeds with exit 0.

`tree` uses the ordinary proof-tree API on the same formula and tails premise.
JSON results include its structured `tree` object, including sequents, open
goals and statistics. This is a diagnostic strategy tree, not a new
verification verdict: its row is `inspected`. Recursive and callback
obligations report `unsupported` here; their obligations and verification
goals remain available through the other views. The ordinary tree's closer
can leave goals that another verification tactic closes.

## Run a concrete call

```sh
solidity-lean run Counter.sol --contract Counter --function inc --arg 1 --state initial.json
solidity-lean run Token.sol --function 'approve(address,uint256)' --arg 0x7 --arg 100
```

`run` executes one selected function in the typed model, as `#run` does.
Repeat `--arg` for primitive integer or boolean parameters in declaration
order. Overloads must resolve to exactly one row. Without `--state`, the
model starts with default storage, zero balance and default transaction.
An example `initial.json` is:

```json
{
  "storage": {"count": "41", "paused": false},
  "sender": "0x7",
  "value": "0",
  "timestamp": "1700000000",
  "balance": "1000",
  "selfAddress": "0x8"
}
```

Unknown state keys, unsafe numeric JSON literals, and out-of-range words are
rejected. Use strings for large integers so JSON cannot round them. Storage
supports primitive roots; arrays, mappings, structs, arbitrary serialized
heaps and constructor execution require the Lean APIs. The selected
function's return shape must be supported by `#run`. The model's primitive
type bounds apply; this command does not add an ABI decoder to `#run`.
Source initializers and constructors are not automatically executed.

Run results are `ok`, `revert`, `panic` or `diverge`, with returned values and
storage in `text`. A subprocess timeout is an error, not a diagnosis of
divergence. Concrete execution is not a proof about all inputs.

## Rules and output

```sh
solidity-lean rules check --key solidityProgramRules.key
solidity-lean rules check --json
```

`rules check` invokes the existing sort-annotation conformance checker.
`--key FILE` overrides `SOLKEY_RULES`, then the sibling solkey checkout's
default rule path. A missing file is a setup failure; the CLI never reports
a skipped audit as success.

Text output shows one status per function, details for inspection/execution,
and a summary. `--json` produces exactly one JSON document on stdout;
progress and diagnostics use stderr. The schema is:

```json
{
  "schemaVersion": 1,
  "version": "0.1.0",
  "command": "verify",
  "results": [],
  "errors": [],
  "summary": {}
}
```

Source results retain absolute `source`, `contract`, `function`, `signature`,
`tag`, `status`, `reason`, `reading`, and `elapsedMs`. Inspection and runs
also include `text`; tree inspection adds `tree`. Rule audit rows include
`source`, `status` (`matched` or `mismatch`) and `text`. `summary` counts rows
by status. Consumers should accept additional fields within schema version 1.
All JSON encoding is structured; user inputs are data rather than injected
Lean terms or shell commands.

Exit codes:

| Code | Meaning |
|---|---|
| 0 | At least one checked/listed/inspected/executed obligation or matched audit, with no gaps or errors; explicitly skipped/internal rows are permitted. |
| 1 | Pending verification, import gaps, errors while processing sources, a reverting/panicking run, or a rule mismatch. Inspection may successfully report pending goals. |
| 2 | Invalid invocation, missing input/selection, discovery failure, missing executable, or initial build failure. Compiler configuration failures found while processing a source are code 1. |

An empty suite or one containing only skipped/helpers cannot pass. Existing
source limitations, including imports/remappings, remain explicit frontend
limitations; see [solidity-testing.md](solidity-testing.md).

## Tests

`node --test scripts/solidity-lean.test.mjs` exercises the compiled entry
point (statuses, source premises, open goals, proof trees, concrete runs,
large words, overloads, paths with spaces, JSON, exit codes, interruption and
the frozen rule audit). Build the executable, `Solidity.Frontend.Cli` and
`solkeycheck` first. The display/execution `evalExpr` sites of
`Frontend/Cli.lean` construct no proofs and are in the trust inventory.
