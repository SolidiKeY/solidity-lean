# TestSuite performance, compiled verifier 0.5.5

The generated-C native verifier, VS Code backend and offline browser each prove
all **83 functions** from the linked Velvet TestSuite. Ordinary checks load no
Lean environment and run no Lean kernel. The browser package now contains only
the compiled verifier, editor and Solidity compiler: **41.48 MB** of HTML,
including **16.38 MB** of verifier WASM. The installable VSIX is **9.65 MB**.

These are local measurements on 2026-11-03, using an AMD EPYC 9V74 host with a
four-CPU quota, Node 24.21, native Lean 4.24 and system Chromium. No builds ran
during the final measurements. Raw records, source hashes and build manifests
are in [the evidence directory](benchmarks/testsuite-2026-11-03/summary.json).

| Interface | Median source-to-result | Cold first result | Suite result |
|---|---:|---:|---|
| VS Code stdio LSP, packaged native C | 66.0 ms | 0.61 s | 83/83 proved |
| Offline browser, generated C/WASM | 155.7 ms | 2.34 s | 83/83 proved |
| SolKey persistent server | 100.1 ms | 2.03 s (standalone CLI) | 82 proved, 1 open |

The desktop median is about 1.52 times faster than
SolKey's CLI-to-server request. The browser takes about
1.56 times as long. Its cold first result takes
1.15 times as long as SolKey's.
These are comparable interactive latencies, not a claim of identical execution
cost or a guarantee on other machines.

The standalone native process becomes ready in 4.99 ms;
its median precompiled-AST request takes 0.82 ms. Those figures
exclude Solidity compilation and the editor and must not be compared directly
to whole SolKey requests. SolKey's own median proof timer is
24 ms. The packaged extension's portable WASM fallback also
proved 83/83, with a 70.0 ms median in its separate one-round run.

## What changed

`Tools.DirectRuntime` admits ordinary assertion obligations, typed arrays and
mappings, indexing, storage length, push/pop/delete and loops through the existing
raw source elaborator and intrinsic obligation builders. Unsupported siblings
no longer force a supported function through the general frontend. Overloads
are selected by compiler declaration ID.

The executable `Seq.run` sequent walk applies the arithmetic closer to each
symbolic leaf. Proof-carrying strengthening handles primitive anonymous loop
locals and discards well-formedness premises when proving a stronger leaf.
Bounded affine propagation and the existing typed-input, dependent and array
reductions carry validity proofs erased by Lean's C compiler. Short annotated
loops can retry exact bounded unrolling; exhaustion remains unknown.

The native and WASM builds prune module registration and retain only reachable
functions and closed data. Native workers use a persistent line protocol; browser
workers use the same generated-C closure. Normal unsupported or undecided inputs
remain unknown. Only explicit certificate/audit requests use the optional general
frontend. The default HTML embeds no kernel or serialized `.olean` environment.
Source, compiler, bridge, generated-C and binary identities are checked at build
or load boundaries; stale artifacts are refused.

## Workloads and measurement boundaries

The inventory is every function in
[Bridge/SolidityVelvet/TestSuite.lean](../Bridge/SolidityVelvet/TestSuite.lean),
with inventory hash `a4c66b77ffbdc4337be20a8822f176a4b22d50a91247b159acd8024969c11f43`. Each function becomes one real
Solidity contract retaining the suite's shared storage declarations. The exact
same source bytes go to SolKey, native C, extension and browser. There are no
function-name or source-hash special cases in the verifier.

Velvet syntax needs three documented source adaptations: convert the Unicode
minus in decrement examples to ASCII, translate loop invariants/quantifiers to
SolKey `@custom:key` comments, and mark each obligation `box` to match Velvet's
partial-correctness reading. The generated sources, their hashes and AST hashes
are preserved in [workloads.json](benchmarks/testsuite-2026-11-03/workloads.json).
No assertions are removed. This compares the implementations on matched
programs; it does not establish equivalence of every Solidity semantic choice.
See [Solidity alignment](solc-alignment.md) for model boundaries.

Three rounds cover all 83 functions in one persistent verifier per interface.
The extension uses a new URI per submission; the browser changes the live editor
on every submission. Increasing check sequence numbers, one worker identity,
exact source hashes and zero environment imports exclude cached result retrieval.
Per-function medians include all three rounds, including each function's first
request. The median in the table is the median of those 83 medians.

Extension timings include the real stdio LSP, worker, compiler and protocol,
including source validation. They exclude launching the VS Code application
itself. Its cold first result starts before LSP process creation. Browser startup
starts at navigation in a fresh Chromium profile and includes tool preparation;
Chromium process launch is excluded. SolKey's cold request includes JVM startup
and source compilation. Its server marker appears after
305 ms, but that marker excludes the first request's
initialization and must not be treated as a first-result time.

The SolKey reference commit and JAR identity are in
[solkey.json](benchmarks/testsuite-2026-11-03/solkey.json). Its source was unmodified.
The build supplied the official same-version Besu 24.12.2 release JARs in place
of dependencies on unavailable Maven hosts; hashes and the exact Gradle init
script are included in the evidence. The compiler is pinned Solidity 0.8.34.
No Dafny translation was timed.

`forWritesStorageArray` stayed OPEN in all three SolKey rounds
(`NO_APPLICABLE_RULE`); the compiled verifier proved it. Its latency below is
reported as an open result and is not evidence of a faster successful proof.

## Validation and remaining limits

The final native and browser matrix has 249/249 successful requests each;
the packaged native extension has 249/249 and the packaged WASM fallback 83/83.
Eight existing positive/negative specification controls retain their exact
verdicts, including three refutations. Five mutated false ordinary assertions
remain unknown rather than being proved; concrete refutation for that fragment
is still incomplete. A vacuous `require(false)` assertion is proved as expected.

Per-file Lean MCP checks passed for both changed modules and the automation
regression. The relevant 337-job target built successfully. Unit tests passed
130, skipped two optional cases and failed zero; closure tests, dependency-layer
checks, registration checks and both read-only reviews passed. Existing dependency
linter warnings remain. [Validation receipts](benchmarks/testsuite-2026-11-03/validation.json)
record their scope; a whole-repository build is not claimed.

The real single-HTML browser smoke passed compiler errors, edits, exact source
provenance, stale-result clearing, refutation controls, unsupported calldata,
imports, rename and formatting. After stopping the HTTP server and disconnecting
the browser, a fresh worker still compiled and proved semantically new edits.
The managed Chromium policy blocks `file://` navigation, so direct disk-file
launch could not be verified in this environment. The HTTP/offline test passed;
that does not substitute for a successful disk-file launch test.

Calls, inheritance, reference locals, narrow integer types and other unsupported
source shapes can remain unknown on the compact path. Budgets can also leave
supported shapes undecided. No universal speed or completeness claim is made.
The generated-C verifier is trusted at runtime; proof transports are checked at
build time, and no per-result kernel certificate is constructed.

## Reproduce

Use the pinned compiler and Lean toolchains described in
[the compact build instructions](compact-verifier.md). Build the native and
WASM artifacts before timing, and keep heavy builds out of the measurement run.
With `SOLKEY_ROOT` set to a built reference checkout:

```sh
node scripts/testsuite-performance.mjs --native
node scripts/check-direct-testsuite.mjs
node vscode/test/measure-testsuite-speed.cjs
node web/test/testsuite-performance.cjs
node scripts/measure-solkey.mjs "$SOLKEY_ROOT" \
  .lake/testsuite-performance/inputs.json .lake/testsuite-performance/solkey.json
```

The last command runs one reference round. For the recorded three rounds,
repeat each entry of `inputs.json.trials` three times with `repeat: 0, 1, 2`
before passing the file to the reference script. The extension/browser default
to three rounds. Use `SOLIDITY_LEAN_DIRECT_DIR` to select the packaged native or
WASM runtime and `TESTSUITE_REPEATS=1` for the fallback control. Run
`scripts/report-testsuite-performance.mjs` after producing all expected reports
to validate source matching and regenerate the CSV and summary.

## Every function

All figures are milliseconds. C is the precompiled-AST request; the extension,
browser and SolKey columns include source handling. SolKey proof is its own
internal timer. The complete hashes and all observations are retained in the
[CSV](benchmarks/testsuite-2026-11-03/per-function.csv) and raw JSON reports.

| Function | C | Extension | Browser | SolKey | SolKey proof | SolKey result |
|---|---:|---:|---:|---:|---:|---|
| `additionStorageWrite` | 1.73 | 67.6 | 174.9 | 138.7 | 58 | PROVED |
| `additionSimple` | 0.68 | 64.8 | 153.3 | 94.8 | 9 | PROVED |
| `additionStorageRead` | 0.82 | 65.8 | 154.7 | 99.7 | 23 | PROVED |
| `subtractionSimple` | 0.71 | 64.9 | 156.3 | 79.6 | 9 | PROVED |
| `subtractionStorageRead` | 0.74 | 64.6 | 159.2 | 94.4 | 25 | PROVED |
| `multiplicationSimple` | 0.64 | 64.4 | 187.2 | 86.7 | 12 | PROVED |
| `divisionSimple` | 0.64 | 62.6 | 156.6 | 92.2 | 13 | PROVED |
| `moduloSimple` | 0.64 | 61.1 | 157.1 | 86.6 | 12 | PROVED |
| `powerSimple` | 0.62 | 66.1 | 154.4 | 81.1 | 8 | PROVED |
| `localArithmeticInRange` | 1.57 | 69.8 | 155.3 | 131.1 | 56 | PROVED |
| `greaterEqualSimple` | 0.64 | 67.4 | 150.5 | 86.1 | 9 | PROVED |
| `greaterThanSimple` | 0.71 | 67.1 | 152.9 | 81.3 | 5 | PROVED |
| `lessEqualSimple` | 0.58 | 67.7 | 152.4 | 82.4 | 6 | PROVED |
| `lessThanSimple` | 0.59 | 65.1 | 154.2 | 84.7 | 7 | PROVED |
| `notEqualSimple` | 0.60 | 65.3 | 154.8 | 75.6 | 4 | PROVED |
| `logicalAndSimple` | 0.59 | 66.0 | 153.9 | 94.0 | 12 | PROVED |
| `logicalAndShortCircuitRhs` | 0.82 | 67.3 | 152.9 | 91.8 | 21 | PROVED |
| `logicalNotSimple` | 0.58 | 64.1 | 152.5 | 78.6 | 4 | PROVED |
| `logicalOrSimple` | 0.64 | 64.7 | 153.2 | 86.2 | 7 | PROVED |
| `logicalOrShortCircuitRhs` | 0.86 | 68.4 | 152.0 | 109.2 | 34 | PROVED |
| `ternaryCaptureCond` | 0.87 | 66.4 | 160.1 | 99.7 | 24 | PROVED |
| `ternaryToIf` | 0.73 | 66.5 | 155.8 | 88.9 | 16 | PROVED |
| `ifUnfold` | 0.81 | 67.1 | 163.6 | 101.2 | 24 | PROVED |
| `ifElseUnfold` | 0.84 | 65.7 | 160.9 | 90.6 | 20 | PROVED |
| `ifSplit` | 0.76 | 67.0 | 157.4 | 88.7 | 14 | PROVED |
| `ifElseSplit` | 0.82 | 70.5 | 159.5 | 93.3 | 17 | PROVED |
| `ifTrue` | 0.70 | 66.3 | 152.1 | 86.1 | 9 | PROVED |
| `ifFalse` | 0.69 | 66.2 | 150.5 | 85.7 | 10 | PROVED |
| `ifElseTrue` | 0.76 | 66.6 | 152.7 | 81.5 | 10 | PROVED |
| `ifElseFalse` | 0.75 | 65.3 | 156.1 | 80.9 | 9 | PROVED |
| `ifElseNegated` | 0.85 | 69.6 | 154.7 | 90.2 | 18 | PROVED |
| `requireTrueLiteral` | 0.51 | 64.4 | 156.9 | 80.1 | 4 | PROVED |
| `requireFalseLiteral` | 0.56 | 64.8 | 153.6 | 74.5 | 4 | PROVED |
| `requireGuardBox` | 1.02 | 65.7 | 154.8 | 103.6 | 30 | PROVED |
| `requireHoldsDiamond` | 0.90 | 68.4 | 155.0 | 105.5 | 25 | PROVED |
| `testSimpleAssert` | 0.73 | 65.0 | 154.3 | 90.6 | 16 | PROVED |
| `storageRootReadWrite` | 0.69 | 64.2 | 157.2 | 92.2 | 19 | PROVED |
| `storageRootAddAssign` | 0.76 | 65.5 | 155.3 | 90.8 | 21 | PROVED |
| `storageRootSubAssign` | 0.78 | 63.3 | 153.3 | 97.8 | 21 | PROVED |
| `storageRootMulAssign` | 0.76 | 64.6 | 152.2 | 97.0 | 22 | PROVED |
| `storageRootDivAssign` | 0.83 | 64.7 | 154.4 | 102.6 | 22 | PROVED |
| `storageRootModAssign` | 0.81 | 63.1 | 155.3 | 97.3 | 24 | PROVED |
| `storageRootMultipleWrites` | 0.90 | 63.3 | 151.8 | 94.5 | 19 | PROVED |
| `storageRootPostincrement` | 0.74 | 63.0 | 154.9 | 92.8 | 24 | PROVED |
| `storageRootPreincrement` | 0.71 | 64.5 | 151.9 | 100.1 | 22 | PROVED |
| `storageRootPredecrement` | 0.73 | 65.2 | 152.9 | 101.5 | 27 | PROVED |
| `storageRootDelete` | 0.74 | 63.6 | 153.0 | 96.0 | 21 | PROVED |
| `storageRootDisjoint` | 0.74 | 65.1 | 156.2 | 87.6 | 21 | PROVED |
| `storageRootWriteRhsCapture` | 2.89 | 68.7 | 161.8 | 161.3 | 93 | PROVED |
| `storageBoolRootReadWrite` | 0.62 | 62.9 | 155.9 | 86.6 | 11 | PROVED |
| `storageIndexRootMapping` | 0.75 | 65.2 | 153.2 | 100.4 | 20 | PROVED |
| `storageIndexMappingAddAssign` | 0.84 | 64.9 | 158.1 | 120.5 | 44 | PROVED |
| `storageIndexReadMappingStoreRoot` | 1.21 | 65.2 | 155.4 | 122.6 | 47 | PROVED |
| `storageIndexWriteNseChain` | 3.20 | 71.0 | 160.8 | 181.2 | 104 | PROVED |
| `storageIndexDeleteMappingBool` | 0.82 | 65.0 | 152.5 | 113.7 | 31 | PROVED |
| `storageIndexDeleteNseIndex` | 1.34 | 67.3 | 153.6 | 124.5 | 51 | PROVED |
| `testStorageMapReadWriteAndDelete` | 1.75 | 69.3 | 162.9 | 204.5 | 130 | PROVED |
| `storageIndexCopyValue` | 4.47 | 75.6 | 168.1 | 209.6 | 136 | PROVED |
| `storageGridWriteRead` | 1.20 | 67.9 | 157.8 | 135.5 | 64 | PROVED |
| `storageBoolKeyedMapping` | 0.80 | 66.4 | 162.1 | 112.1 | 36 | PROVED |
| `storageIndexAddAssign` | 2.23 | 67.4 | 163.6 | 172.2 | 100 | PROVED |
| `storageIndexSubAssign` | 2.12 | 66.2 | 156.5 | 168.6 | 99 | PROVED |
| `storageIndexMultipleWrites` | 1.66 | 65.5 | 156.7 | 164.6 | 86 | PROVED |
| `storageIndexPostincrement` | 2.15 | 67.6 | 158.9 | 166.0 | 95 | PROVED |
| `storageIndexPostdecrement` | 2.17 | 66.6 | 156.7 | 164.0 | 89 | PROVED |
| `storageIndexDelete` | 1.59 | 64.7 | 155.2 | 154.4 | 82 | PROVED |
| `storageIndexReadNseIndex` | 1.82 | 69.1 | 164.5 | 158.5 | 84 | PROVED |
| `storageIndexArrayAddAssignOutOfBoundsReverts` | 1.00 | 64.2 | 152.2 | 103.2 | 26 | PROVED |
| `storageIndexArrayReadOutOfBoundsReverts` | 1.05 | 65.3 | 155.8 | 99.7 | 27 | PROVED |
| `storageMatrixWriteRead` | 2.85 | 68.4 | 158.3 | 229.4 | 159 | PROVED |
| `storageMatrixNseIndex` | 12.73 | 81.2 | 190.7 | 388.3 | 308 | PROVED |
| `storagePushEmpty` | 1.13 | 65.7 | 158.3 | 111.6 | 42 | PROVED |
| `storagePushLengthPositive` | 0.81 | 62.8 | 155.7 | 109.7 | 36 | PROVED |
| `storagePushNonsimpleArg` | 3.92 | 72.3 | 161.9 | 209.7 | 135 | PROVED |
| `storagePushReadBack` | 1.57 | 69.1 | 155.1 | 174.4 | 103 | PROVED |
| `storagePopAfterPush` | 1.22 | 67.4 | 154.3 | 158.9 | 92 | PROVED |
| `storagePopNonempty` | 1.62 | 70.0 | 157.3 | 203.1 | 127 | PROVED |
| `storagePopUnknownLength` | 0.49 | 63.9 | 150.8 | 136.5 | 48 | PROVED |
| `whileCountsUp` | 1.11 | 66.3 | 157.2 | 120.7 | 44 | PROVED |
| `whileBodyDeclaresLocal` | 90.54 | 156.1 | 331.5 | 388.3 | 314 | PROVED |
| `forWritesStorageArray` | 18.85 | 86.5 | 194.8 | 415.1 | 350 | OPEN |
| `invariantCountsToBound` | 1.35 | 69.5 | 158.1 | 153.9 | 78 | PROVED |
| `invariantForCountsArrayLength` | 1.75 | 67.0 | 160.9 | 173.9 | 104 | PROVED |
