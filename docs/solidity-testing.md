# Testing Solidity files

The native `solidity-lean verify` and `list` commands ([cli.md](cli.md))
expose this API with versioned JSON output; the JavaScript and Lean entry
points below are the same pipeline.

The Lean API can compile a `.sol` source, discover its contracts and functions,
generate their obligations, and check proofs. Run it from the repository root:

```sh
node scripts/test-solidity.mjs path/to/Test.sol
node scripts/test-solidity.mjs --json path/to/test-directory
node scripts/test-solidity.mjs --contract Test --function example path/to/Test.sol
node scripts/test-solidity.mjs --list path/to/test-directory
node scripts/test-solidity.mjs --audit-preconditions path/to/Contract.sol
node scripts/test-solidity.mjs --counterexamples path/to/Contract.sol
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

Every plain imported source obligation also assumes `address(this) < 2^160`;
`--self-address A` pins the address ([source-inputs.md](source-inputs.md)).

Source-unit free functions and library functions can be inlined as helpers,
resolved by solc declaration identity. Extension receivers are the first
argument, including with named arguments and tuple returns. Independent rows
belong to contracts and libraries; top-level free functions have no independent
test row. Recursion and unsupported helper signatures remain import gaps.

Declaration metadata uses solc identities and canonical selector fields:
`type(C).name`, an interface's own-function XOR ID, error/event selectors,
and static function selectors. Anonymous events have no selector. Dynamic
selector receivers retain their evaluation and lazy expression position.
Unnamed input parameters receive fresh model names. See
[the declaration milestone](feature-work/declarations-metadata.md) for
verified shapes and remaining gaps.

**What `proved` states.** The runner reads the actual obligation, including
`cspec` rows. Whenever `Fml.callsBack false` holds it proves
`ValidT .noCallback` by the callback calculus. Otherwise plain rows retain
`⊢ N.f.problem`, and specified rows retain internal formula validity.
Bare high-level external calls are included. View/pure calls also receive
the conservative callback reading until static-call restrictions occur in
the operational call type (`docs/options.md`, O7). The TestSuite's hand
written derived theorems remain internal `⊢` statements under their stated
reading. See [correctness.md](correctness.md) for public `Spec` correctness.

| Result | Meaning |
|---|---|
| `proved` | Kernel-checked proof, using only Lean's standard three axioms. |
| `refuted` | Opt-in, exact-goal kernel-checked refutation with the same candidate's model prestate. |
| `pending` | Ordinary open proof goals; no claim of falsity. Runtime and budget failures are errors. |
| `skipped` / `skip` | Explicit NatSpec skip tag. |
| `internal` | Internal helper; no independent obligation. |
| `unsupported` / `excluded` | An import or obligation gap; prevents suite success. |
| `ready` | Listing only; no proof attempted. |
| `notRun` | Contract process interrupted before this function completed. |

The JSON report is `{results, errors}`. Each result includes the absolute source
path, contract, function, signature, tag, status, reason, reading and elapsed
milliseconds. Editor clients also receive the exact solc `sourceId`, the compiled
source's SHA-256 as `sourceHash`, and a `range` with zero-based UTF-16 positions
when a source declaration is available. Synthesized constructors use the contract
range. The runner checks that source bytes still match the compiler fixture
before associating positions. These fields locate results; they are not part of
the proof claim. See [the extension](../vscode/README.md) for commands and tests.
`reading` is the tails reading the obligation was stated under
(`docs/options.md`, O6): `clean` (`⊢ cleanTail(storage) = true → N.f.problem`)
for a plain obligation of a contract every function of which exposes nothing
(`Prog.exposesNone`), so that clean tails are its invariant; `solc` otherwise,
and for specifications, obligations that call back and recursive ones.
Large contracts run in batches of 32 imported rows. `batchSize` selects the
JavaScript API batch size, and `onProgress` receives each retained batch.
Runtime and heartbeat exceptions report `error`, distinct from ordinary
`pending` open goals. Compiler,
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
300000 ms: a self-call `try` read with callbacks, `docs/options.md` O8,
closes the callee's leaves and the oracle's). Lean's existing per-step limits
and ambient heartbeat limit also apply. A timeout is not an expected-open verdict.

The JavaScript API exports `solidityFiles(paths)`,
`runSolidityTests(paths, options)`, and `testsPassed(report, listing)` from
`scripts/test-solidity.mjs`. It is synchronous. The options are `contract`,
`function`, `list`, `timeoutMs`, `solkey`, `soljson`, `build`, `batchSize`,
`onProgress`, `renaming`, `selfAddress`, `auditPreconditions` and `counterexamples`. A function selector may be a source name (all its
overloads) or its source signature (one overload). Reports retain source types
before enum, address or value-type lowering.

`auditPreconditions: true` (`--audit-preconditions`) additionally certifies whether
specified functions have possible entry states. It is separate from proving
postconditions. Audited rows add `preconditions` and `preconditionReason`;
`impossible`, `unknown` and interrupted `notRun` audits cannot pass strict suites.
Plain functions report `notApplicable`. Listing and auditing cannot be combined.
The [verification notes](feature-work/dafny-verification.md) describe the
certificates, finite-membership syntax and exact limits.

`counterexamples: true` (`--counterexamples`) searches ordinary pending,
specified functions with primitive inputs and storage under the internal
`Fml.Valid` reading. An accepted candidate adds `counterexample` and changes the
status to `refuted` only after the exact tested goal's negation is retained as a
kernel-checked theorem using standard axioms. The report preserves decimal
strings for integers and exact source argument names when available. A refuted
suite fails. Unsupported callback, recursive, reference-storage and plain
obligations stay pending; an inconclusive search supplies no evidence. Listing
cannot request counterexamples. These are typed model prestates, with no
constructor-reachability or transaction-replay claim.

For an existing solc fixture, the Lean entry point is:

```lean
import Solidity.Frontend.Testing

solc_import "Example.ast.json" hash 0xHASH as Imported.Example testing
solc_scoped_problems Imported.Example decl
#solkey_test Imported.Example to "/tmp/results.json"
-- Optional: only "functionName" or "functionName(uint)", then
-- from N count K, then listing, before `to`.
```

The hash must be the fixture's actual FNV-1a hash, as written by
`scripts/solc-ast.mjs`. Direct Lean callers must inspect the import's diagnostics
as well as the result file; the file runner does this automatically.
The explicit `testing` import mode retains NatSpec clauses and all callable
function declarations. The original import mode retains only declarations
needed for internal calls. Specifications follow declaration renaming through
the parsed syntax: parameters remain available in preconditions and `\old`,
named returns only in post-state `ensures`, and quantified variables retain
their shadows. Generated names avoid other generated names and annotation
identifiers. Loop annotations use the locals visible at their lexical position,
including modifier, return and catch parameters; leaving a block or `for`
restores the enclosing scope. Contract-level specification clauses must be
invariants, and function-level invariants are refused. Quantifiers may begin
an implication's consequent; their bodies extend through the remaining formula.
Clauses of an admitted body are validated individually before insertion.
A refused body contributes no clause or member, and its callers remain gaps.
Parser-invalid modifiers are omitted from the declaration environment; their
users fail modifier lookup rather than running without the modifier.
Unsupported elementary state fields and narrow container fields stay gaps,
including functions whose specifications mention an omitted field. Contract
invariants retain their existing whole-contract validation. Unsupported clause
syntax remains refused before it can contribute a member or a premise. Testing
rows expose `invalidSpecification` for a parser-invalid clause, including a
required callee's invalid clause. Mixed reports retain these local `unsupported`
rows. If every selected non-internal/non-skipped verification candidate has
that structured diagnostic, the file API also reports one `specification` input
error: the selection has no well-formed specification to verify. Ordinary
implementation gaps, exclusions, unfinished proofs and tool interruptions never
qualify merely because their messages look like parser errors. Rows and original
failure diagnostics are retained in both cases.

Large literal tables are compiled in segments of at most 64 list cells.
A kernel-checked reflexivity certificate verifies that the resulting contract
equals the original literal. This lets the testing import retain the full
617-function frozen TestSuite (solkey `473da8944c`) without increasing code-generation or proof
limits. Imported scoped programs remain uncompiled, as before.

Enum members in NatSpec are resolved from the validated solc declarations,
using canonical names and short names visible in the imported contract or
source unit. Resolution preserves whole dotted names and refuses ambiguity or
a head shadowed by a state variable, parameter, return or local. Clauses with
quantifiers or escaped identifiers stay verbatim; enum resolution in them
requires a future parser-based extension. Function and loop annotations use
their defining contract or library's scope, including inlined helpers.
The test runner uses `lake --no-build lean` after building the API, so its
single-file checks can also read imports held only in Lake's shared cache.
It uses the first executable `lake` on `PATH`, preserving local wrappers. If
none is found, it uses `ELAN_HOME/bin/lake` (by default `~/.elan/bin/lake`).

The compiler helper reads one source unit; source imports/remappings and
unsupported AST forms remain frontend limitations. The frontend imports
inherited state, helper bodies and modifiers using checked Solc C3 metadata.
Only the selected contract's own functions receive independent test rows.
Specifications can read `this`/`address(this)` and its ledger entry; `\old`
retains the address and selects the existing ledger snapshot.
Ledger integers support unary minus. Beside a ledger integer, an unsigned
negand widens before negation, including under `\old` and on either side of
a comparison. Primitive subexpressions keep their checked arithmetic;
unsigned negation outside that context and signed/ledger mixtures remain
refused.
Lexical unsigned constants with bounded literal-only initializers are imported
as typed `uint(n)` specification literals. Private visibility, shadows and
ambiguity are preserved. Other constant forms, quantified substitutions and
casts in loop invariants remain explicit limitations.
Ledger locations in `assignable` clauses are refused per function and the
refusal propagates through callers. Builtin call heads and escaped keywords
remain distinct from constants sharing their spelling.
Base constructors run in solc's legacy order, their arguments in either form;
`super.f` names the next implementation in the most-derived C3 order; a base's
contract clauses are the derived contract's too. Duplicate state root names,
modifiers on a base constructor or on a constructor with base constructors,
and `return` in a base constructor are rejected. Virtual calls use the most-derived
implementation; explicit `Base.f` calls keep the named implementation, and
external calls retain their external semantics. Expected-open suites use an expectation
manifest when the SolKey corpus is imported; `pending` alone does not certify
an invalid specification. The pinned SolKey test sources and their expectation manifest now live in
`tests/migration/`; see [solkey-migration.md](solkey-migration.md) for the
in-progress migration and its remaining coverage gaps.

## Tests

`node --test scripts/test-solidity.test.mjs` exercises compilation, multiple
contracts, true and false specifications, box versus diamond on revert,
internal/skip tags, unsupported assembly, omitted initializers (an error, not
a silent omission), function-level invariants refused, `payable` kept,
checkpointing on timeout, selection and listing.
