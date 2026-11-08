# Editor parity evidence

`constant.sol` and `constant.dfy` are the reduced shared workload: `f0` proves,
and `f1` has a false postcondition. Solidity uses the repository's actual
`@custom:key ensures \result` annotation. Ignoring an unrecognized NatSpec tag
would invalidate the comparison.

The live harness generates repeated true/false variants of this fragment.
Runtime artifacts belong under `.cache/editor-parity/` and include JSON results,
raw protocol traces, process samples and renderer observations. The
[harness guide](../../docs/dafny-editor-parity.md) gives reproduction commands,
methodology and limitations. The checked-in baseline summarizes completed runs;
it is descriptive evidence on the recorded machine, not a universal performance
threshold or claim of full parity.

[baseline.md](.) is the human summary;
[baseline.json](baseline.json) retains the machine-readable measurements and
per-feature evidence. [audit.json](audit.json) records independent rediscovery,
review findings, repairs and remaining work. Failed pre-fix launcher attempts are
listed separately in the baseline instead of contributing timing estimates.

[stdio-baseline.md](.) and [stdio-baseline.json](stdio-baseline.json)
retain the fresh server-only measurements and their blocked editor/build scope.
`services.dfy` and `services.sol` preserve the reduced call-site fixture used for
navigation, rename, signature-help and incremental/full-replacement completion
regressions. The independent [registration ledger](../../docs/dafny-editor-audit.json)
records unported reference cases as unexamined.


The mechanical continuation extends the same inventory with individual
contributions, TypeScript call sites, live capability/method discovery and
explicit lifecycle/visual/performance obligations. `lifecycle/` contains real
reference-only open/edit/break/fix/save/close traffic and phase observations.
`parity-gate-report.json` records the required gate's failed result; zero rows
are currently judged complete. See the guide's Handoffs section for the external
first-run row freeze, commands, independent review repairs and provisioning block.


`recovery-c0ef3ec7/` retains controller/phase regression output, source-hashed
real service-only measurements and raw traffic archive, plus recovered-tool and
resource-scope probes. All rows remain incomplete; these results establish no
visual parity, Lean proof execution or proof-worker scaling.


`recovery-5bad5756/` records diagnostic migration/related-location, hover scheduling
and native Testing request regressions; live local compiler and exact pinned Dafny
migration traffic; retained failed attempts; and source/review evidence. These are
partial observations. All 270 original rows remain, with 23 added scenario rows;
no rendered editor or local kernel proof equivalence is established.

Lookup migration recovery evidence is in `recovery-bdbc1491/`: initial failing reproduction, focused/full regressions, native compiler-backed service responses and raw ordered traffic, synthetic metadata overhead samples and independent source reviews. Run `node --max-old-space-size=512 vscode/parity/lookup-benchmark.cjs` from the repository root for the bounded warm synthetic migration/query benchmark. It excludes snapshot capture, compiler, proof, UI and worker scaling; it does not discharge the original performance rows. All 302 obligations remain non-complete, including the added nine lookup scenarios.

Structural lookup investigation is retained in `recovery-structural/`: the original wrong inherited-target failure, initial fixture error, focused failing scope/type tests, final ordered native inheritance/block/overload invalidation and recovery, source reviews and revised synthetic timings. The existing lookup benchmark now exercises declaration header guards and brace depths32/128. No proof, snapshot-capture, rendered or general Dafny equivalence is inferred. Seven obligations append to the prior302; none is complete.

Startup/version recovery is retained in `recovery-startup/`, including real failed exits and ordered production client LSP traffic. Run `SOLKEY_ROOT=... node vscode/parity/startup.cjs --output NEW_DIRECTORY` with the configured existing compiler source root. It records missing/unexecutable runtime, missing backend, invalid initialization, configuration correction, native initialize, scoped restart and actual child disposal, plus five serial process-cold/warm startup samples. It performs no download, Lean build or proof; startup success is not backend/proof readiness. Injected UI/version fixtures are separately labeled. All326 obligations remain non-complete.

Version lifecycle evidence is in `recovery-version/`. The existing startup harness accepts `--output NEW_DIRECTORY --versions` for ordered native producer and explicitly labeled injected cases, raw per-source traffic, real5000ms fallback, late/duplicate/malformed data, failure/disposal, cancellation and scoped close/reopen recovery. Normal startup mode now asserts native initialize response → initialized → version → identity ordering. No Lean proof, renderer or compiler/EVM agreement is inferred. Existing pinned reference trace is reused without rewriting it. All342 obligations remain non-complete.

Status summary/menu evidence is in `recovery-status/`. Existing startup harness mode `--output NEW_DIRECTORY --status` records actual native compiler/status traffic through the production controller and an injected editor API, plus exact pinned TypeScript message/menu execution under an injected document boundary. It covers native compile/failure/fix, rapid edits, background files, identical-source reopen, cancellation, scoped restart and disposal; mixed completed/proof/check/audit outcomes remain injected tests. Public proof-help routing remains pending Q-STATUS-HELP-01. No proof, renderer, compiler/EVM equivalence or full parity is established; all363 rows remain non-complete.

Automatic Testing recovery uses `SOLKEY_ROOT=... node vscode/parity/startup.cjs --output NEW_DIRECTORY --testing`. It records native compiler/client/production-controller lifecycle with injected VS Code APIs; per-function progress and terminal proof outcomes are explicitly injected. `testing-reference.cjs` executes the exact pinned Testing view algorithm with injected statuses. Neither establishes rendered Testing UI, native automatic proof transitions or kernel parity. `recovery-auto-testing/` retains before failures, reviewer counterexamples, failed concurrent startup deadlines and successful serial Node checks. All384 obligations remain non-complete.

Hierarchy recovery uses `SOLKEY_ROOT=... node vscode/parity/startup.cjs --output NEW_DIRECTORY --hierarchy`. It records actual pinned compiler ASTs and LSP symbols through the production controller; result rows, editor APIs and manual terminal outcomes are explicitly injected. `--testing` also retains exact pinned hierarchy comparisons for matched/missing/unmatched/historical symbols. Neither certifies rendered or kernel parity. `recovery-hierarchy/` retains failing reproductions, strict documented collection API checks, reviews and raw native evidence.406 obligations remain non-complete.

Retention recovery uses `SOLKEY_ROOT=... node vscode/parity/startup.cjs --output NEW_DIRECTORY --retention`. It records owned PID/birth/session and thread observations across actual compiler cycles; frozen/crash faults, fake builds and transport fixtures are labeled. Live processes, terminated zombies, and harness-only crash-directory removal remain separate. Compiler warm median/p95 is not proof/solver scaling. `recovery-retention/` retains failures, source reviews and raw traffic. All435 obligations remain non-complete.


### H44 bulk evidence delivery

Generated evidence/fixtures/logs are intentionally ignored, not deleted. The
checksum-bound VM archive and file index are listed in
`docs/dafny-parity-bulk-manifest.json`. Before running the unchanged Node,
inventory or parity checks in a fresh checkout, copy both `bulk.tar.gz` and
`files.json` from that manifest's VM directory to the runner, then run:

```
flock /tmp/solidity-lean-feature-groups-20261025/writer.lock python3 scripts/coord-tools/dafny-parity-bulk.py --directory /absolute/provisioned/bundle --restore
```

The helper validates archive/index/member checksums and restores only ignored,
untracked paths, refusing changed existing files. It never downloads, uploads,
skips tests or changes gate predicates. CI performs the same preparation using
`DAFNY_PARITY_BULK_DIR` (repository variable) when provisioned; missing artifacts
fail preparation. Hosted-runner delivery still requires coordinator provisioning;
no storage destination or publication was selected. Native data-dependent tests
and the frozen baseline trace remain exact, with no synthetic replacement.


### Native compiler-only custom imports

`run.cjs --suite custom-import-actions` extends the existing native launcher.
Provide the pinned Code/Dafny/extension/.NET paths and use `--workers 1 --cache
none --trials 1 --warmups 0 --obligations 1`. Default operation/launch deadlines
remain unchanged. Local verification is disabled. The paired source fixtures
exercise imports; they do not replace the annotated workload or its failed
admission receipt. Resource defaults, actual F6 input/cancellation, a subsequent
dirty edit, owned command/session receipts, both source hashes and artifact
contents are observed. Request/reply files reuse the atomic phase writer;
partial reads are retained and replayed request IDs do not dispatch twice.

A failing annotated CRLF case is still a failure. Raw compiler diagnosis can
identify a documentation-span mismatch without producing an admitted artifact.
Producer repair is required before that unchanged case can pass. Missing
positioned traces cannot be replaced with certified model-prestate strings.
All native compiler/action observations remain separate from kernel proofs,
rendered full-lifecycle equivalence, performance/scaling matrices and row judges.

`--suite dafny-compiler-output --targets dafny` isolates the pinned upstream output-directory contract in the existing native runner. It preserves ordinary/custom CLI quoting, actual terminal outcomes and output bytes; relative-path space splitting and unsupported folder scope remain failed evidence. No local AST/executable equality is inferred. Artifact scans require observed recursive filesystem support rather than a newly invented product Node floor.
