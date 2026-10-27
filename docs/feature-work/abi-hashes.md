# ABI, hashes and concatenation

Inventory status: partial. Regressions: `Examples/Tactics/AbiFeatures.lean`,
`Examples/Tactics/AbiFeaturesImport.lean` (`tests/abi-0.8.38/Features.sol`),
`Examples/Tactics/Recovery.lean`, `Examples/Tactics/AbiHexCall.lean`
(`tests/abi-0.8.38/HexCall.sol`).

## Supported

- **ERC-7201** (`Solidity/ERC7201.lean`). `ERC7201.root` is the namespace
  formula over bytes: Keccak-256, minus one modulo 2^256, ABI-encode, hash
  again, clear the low byte. Literal calls fold at elaboration; runtime calls
  use the same hash, encoding and wrapping arithmetic. `root_aligned` proves
  the low-byte invariant for every identifier. The result gives no access to
  physical storage layout.
- **`ecrecover`** (`Solidity/Secp256k1.lean`): a bounded 256-bit modular
  exponentiation and scalar walk. Coordinates and scalars are `Fin`; points
  carry their curve equation and every result is checked. Inputs enter as
  naturals, so malformed ABI input is admitted and then validated. High-s
  signatures, v = 27/28 and 0 < r, s < n are accepted; a missing square root or
  infinity fails. The hash symbol and taclet read an `@[irreducible]`
  interpretation, so symbolic proofs do not unfold recovery.
- **`abi.encodeWithSignature`** hashes the literal's UTF-8 bytes once.
- **External function values** keep their ABI `bytes24` type before address
  and selector become arithmetic: standard encoding right-pads to 32 bytes,
  packed takes 24.
- **`abi.encodeCall`** reads parameter spellings before dispatch
  canonicalization erases widths, then checks arity, primitive kinds, integer
  widths, fixed-byte widening and function components, and applies contextual
  conversions. A computed receiver is evaluated before the arguments even when
  its selector folds. Local function values and `this.f` keep their own
  identities when a local shadows `f`. Discarded builtin calls go through the
  same validation.
- **Exact-width hex arguments.** The target is resolved by solc's
  `referencedDeclaration`. A direct numeric hex literal gets `bytesN` context
  only when its token has exactly `2*N` hex digits and its compiler type is a
  numeric constant (leading zeros, mixed case, separators and parentheses
  around one argument allowed). The result is `Fin (2^(8*N))`; the raw AST is
  importer evidence only. Parentheses around a whole multi-argument tuple make
  one component and are not flattened.
- **`bytes.concat`/`string.concat`** check their argument kinds, nested
  concatenations and explicit casts included.
- **Decoder bounds.** Offsets and lengths are checked against the remaining
  input before arithmetic, traversal or allocation, so a maximal encoded length
  cannot overflow the check or start a huge allocation. Unaligned and
  overlapping offsets that solc accepts stay accepted: a decoder must not
  impose the encoder's canonical layout.

## Refused, and why

- Internal function markers in an encoding, where the metadata keeps them.
- An implicit fixed-byte narrowing in `encodeCall`.
- Decimal numerals, short or long hex tokens, arithmetic, typed numeric locals
  and 40-digit address literals as `bytesN` arguments: no contextual coercion.
  `abi.encode(0xabcd)` keeps its numeric word layout. The `sol{}` DSL erases
  literal spelling, so it needs an explicit `bytes2(0xabcd)`.

## Decisions

- No collision-freedom, authorization, primality, group-law or recovery axiom.
  The vector proofs are concrete reductions, not a theorem of equivalence with
  the EVM precompile. Semantic and calculus proofs refer to the executable
  interpretation. Opacity of recovery dates from `7d57d9c0` as an
  unimplemented boundary, not a speed optimization.
- `scripts/solc-ast.mjs` accepts an explicit compiler only with its checksum,
  source and output, and never repins the frozen SolKeY compiler or fixtures.

## Left

- Struct enum members lose nominal identity and cardinality in
  `Contract.spellTy`/`enumRows`, and function mutability and some aggregate
  function markers are absent, so exact legality and enum decoding wait on
  the declaration metadata ([declarations-metadata.md](declarations-metadata.md)).
- Arrays of hex literals and other aggregate contextual coercions.
- ABI identity of inherited renamed function values.
- ABI traversal of recursive graphs ([recursive-types.md](recursive-types.md)).
- External reference-valued returns: `ExtResult` carries only primitive words.
- Dynamic recursive round-trip proofs; the recovery/precompile equivalence.

## Reproduction

```sh
node scripts/solc-ast.mjs --compiler-file /path/to/soljson-v0.8.38+commit.1835d247.js \
  --compiler-sha256 6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390 \
  --source tests/abi-0.8.38/Features.sol --out tests/abi-0.8.38/Features.ast.json \
  --wrapper Solidity/Examples/Tactics/AbiFeaturesImport.lean
node scripts/solc-ast.mjs --compiler-file /path/to/soljson-v0.8.38+commit.1835d247.js \
  --compiler-sha256 6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390 \
  --source tests/abi-0.8.38/HexCall.sol --out tests/abi-0.8.38/HexCall.ast.json --no-wrapper
node scripts/check-abi-vectors.mjs COMPILER_FILE EXTERNAL_NODE_MODULES
node scripts/check-abi-hex-call.mjs /external/node_modules \
  /path/to/soljson-v0.8.38+commit.1835d247.js /path/to/soljson-v0.8.34+commit.80d5c536.js
```

The checkers run Cancun bytecode with EthereumJS VM/common/util 10.1.3 and
ethers 6.17.0, installed outside the Lean package.

## M3: upstream Group 10, exact retained revert data (2026-10-26)

Status: staged adapter repair; **semantic coverage of the group is incomplete**. The
historical blocked list at `006fcd593f5beeb540e7adf2bc76de4638566924`
contains 325 dynamic/aggregate/bytes/function vectors, 27 noncanonical ABI
inputs and 85 concrete revert-data expectations. These are historical adapter
blocks on `cadb628c`, not demonstrated semantic bugs on current master.
The independent task branch starts at `006fcd59`; no master merge or push is
part of this work.

The runtime gate ran in the attached managed executor, with
`/workspace/.setup/activate.sh` sourced: Lean 4.24.0 (`797c613e`), Lake
5.0.0-src+797c613, and a successful `lake build Solidity.KeySort`.
`node scripts/solidity-upstream.mjs verify` verified all 11,622 archived files.
The exact reference compiler is 0.8.38+1835d247, SHA-256
`6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`.
The archive and all historical results remain unchanged.

The JavaScript adapter preserves native parameter formatting: unpadded
`hex"..."` chunks, numeric/Boolean words, explicit left/right word alignment,
and strings of at most 32 bytes with supported native byte escapes. It follows
`TestFileParser::parseParameter` and `BytesUtils` in the pinned source.
Quoted commas/hash bytes are preserved; hash comments are admitted only at
argument/expectation boundaries and cannot fuse tokens. Ambiguous leading-zero
decimals, negative hex and unsupported spellings remain blocked. The Lean replay compares every retained byte of `.revertWith`,
including selectors, code words and trailing zeros. Empty-data failure means
empty data; constructors do not discard data. `.panic` is always inconclusive:
no expected code is inferred from a generic model panic. Failed calls retain
the previous state. Early exits retain the preceding observations and an
inconclusive executed vector is reported explicitly.

This is an observational adapter change, with no semantic/rule/representation
change, new dependency, axiom, admitted proof or raised heartbeat limit.
Existing typed values, programs and exception semantics are reused. In
particular ordinary error/reason lowering may abstract data away outside a
self frame; an observed payload mismatch does not establish an upstream EVM
bug or a universal correctness theorem. No self frame, host value or panic
code is invented to force agreement.

The second stage decodes raw ABI argument bytes using the existing intrinsic
ABI operations, invokes the admitted source declaration once, then ABI-encodes
its actual returns. Actual source types and width metadata must agree with the
compiler ABI schema, including nested tuple components. Entry selection uses
the unique selected source declaration and its canonical ABI signature; no
name-only fallback is used for imported contracts. Typed memory output is read
through `RevPart.mem .raw`; `ABI.readBytes_exact` proves its equality to the
existing heap-byte observation. Successful calls retain global state; failures
roll back. The canonical probe is separate, calls no source body, and discards
its temporary heap. No expected return/failure guides admission.

Reference/function arguments require byte-identical decode/re-encode before
execution. This deliberately blocks noncanonical, overlapping, unaligned or
malformed reference layouts: external calldata references can defer checks
that a memory decoder performs eagerly. Dirty unused array elements therefore
cannot certify an expected failure. Primitive v2 entry decoding checks widths,
sign extension, Boolean values, lengths and fixed-bytes padding before the
body. ABI v1 raw replay remains blocked using actual compiler pragma metadata,
including comments between pragma tokens. Native scalar replay remains
available for supported canonical v1 cases. Raw replay with inline assembly
is blocked because physical calldata/memory layout observations need their own
adapter. Nominal enum ranges are blocked recursively before erasure.

Remaining stages include lazy/noncanonical aggregate entry decoding, compound
type expressions and multiple reference returns not admitted by the existing
wrapper, function ABI values requiring retained function metadata, nominal
enum cardinalities, and exact failure data where ordinary-call reading
abstracts it. Host/gas/log/configuration and resource requirements
remain blocked until implemented. No feature-catalog coverage is upgraded.

Read-only finder and independent skeptic reviews ran without Lean workers.
The finder identified observation loss on early exits; the patch fixes it.
The skeptic found no false-pass defect and requested count assertions for
observations preceding an unresolved call and a failed-deployment host call;
both controls were added. Parser tests cover raw selectors, signed words,
empty hex, malformed hex/words and unsupported spellings. Replay tests cover
complete raw bytes, trailing-zero mismatch, empty-data mismatch, rollback,
concrete 0x12 versus 0x11, generic panic blocking and retained observations.
No Lean MCP diagnostic tools were exposed. Configured per-file Lean checking
and replay commands are used instead.

The complete-run attempt exposed a shared snapshot extraction race: a
concurrent runner could read a file while another `tar` replaced it. Fresh
snapshots now extract into a private sibling directory, verify all 11,622
files and publish atomically. A concurrent publisher that loses the rename
validates the winner. Reused populated trees are checked byte for byte and
never rewritten; drift remains an error. Staging cleanup removes only that
invocation's directory. Independent finder/skeptic followups found no blocker.
The concurrency regression also checks that later corrupted bytes are rejected
and preserved. It does not force every possible rename scheduling interleaving;
older in-place extractors must finish before relying on the new protocol.

The payload parser conservatively rejects multi-digit leading-zero decimal
words because the native integer converter may read them as octal. An audit
of all 85 assigned failure fixtures / 754 payload tokens found none. The
per-fixture evidence retains runner-hash transitions for this hardening and
snapshot publication; model sources stayed unchanged through those transitions.
No retry reports with differing provenance are merged by the historical retry
merger. Interrupted invocations remain separate and are not fixture verdicts.

The newly reachable import gaps are taken from `variants[].gaps`, rather
than inferred from filenames. They include an out-of-range folded ERC-7201
literal, a constant public getter read as a storage slot, narrow constant
conversions (`uint8`/`int8`), signed-to-enum conversion, and member-qualified
custom errors in a library/interface. They remain frontend/import gaps. The
adapter does not incorporate another group's unpublished constant/declaration
or exception work. The enormous-memory-array case reaches a process resource
limit and remains blocked; no concrete panic code is inferred from that limit.

Stage 1 evidence is retained in `tests/upstream/group10-stage1-results.json`:
437 exact runs, 0 working / 68 broken / 369 blocked, with 21 initial base-commit
reproductions and all pipeline observations/source/model/runner hashes. Stage 2
uses fresh output directories and a complete independent base-commit rerun;
its final evidence is recorded below after completion.

Stage 2 positive/negative replay controls cover dynamic bytes/array returns,
state retention and once-only execution, mismatched output bytes, dirty unused
calldata arrays, malformed offset/length, uint8 entry bounds, int8 extension,
fixed-bytes padding, actual-schema mismatch, an aggregate constructor with
an initializer, and external-function address/selector fields with nonzero
address/selector bytes. Dirty function padding blocks; wrong selector output
breaks; function-valued return transport stays blocked by the existing
uint192/metadata admission. A failed canonical probe (including its resource
limits) stays inconclusive; its diagnostic does not establish malformed bytes. All 18 Node controls pass. Per-file Lean checking and replay
checking pass using the configured toolchain; the replay and observer theorem
use only `[propext, Classical.choice, Quot.sound]`. Strict automation reports
491 automatic / 61 budgeted / 11 refuted / 0 pending; reachability is 667 with
zero orphans; all 143 core modules remain outside the elaborator dependency
graph. No proof limits were raised.

The read-only finder and independent skeptic confirmed and closed three
additional admission issues: commented ABI v1 pragmas, comment token fusion,
and the older scalar parser bypassing ambiguous-number rejection. Tests pin
each exclusion. Neither reviewer opened Lean workers. The lazy-array guard
was chosen after the skeptic identified eager versus deferred decoding as a
soundness boundary, rather than interpreting a decoder failure as a source
failure.


Existing independent reference suites also pass with the SHA-checked 0.8.38
compiler: `check-abi-vectors.mjs` reports 31 EVM vectors and 5 compiler rejection
cases; `check-abi-hex-call.mjs` reports 18 legacy/via-IR EVM runs and 20 compiler
rejections. These compiler rejections are reference checks, not Lean coverage.
Their documented optional dependencies were installed only under
`/workspace/.setup/abi-reference`; the core/package dependencies are unchanged.
The unchanged `SortCheck/Faithfulness.lean` passed both a direct configured Lean
check and a separate Lake rebuild (337 s), after the earlier broad invocation
reported process exit 135 without an elaboration diagnostic. No proof limit or
representation was changed to obtain that result.


All four configured existing source-family checks pass:
`AbiFeatures.lean`, `AbiFeaturesImport.lean`, `AbiHexCall.lean` and
`CallExceptions.lean`. The final code/control finder and independent skeptic
passes found no further correctness blocker and opened no Lean workers. The
finder noted legacy `metadata.scope` wording (“scalar vectors”); this frozen
runner field understates the new subset. The stage description and each
vector's `inputTypes`, `outputTypes` and `returnBytes` describe the actual
aggregate/function-field observations. It is not a generated-EVM/SSA claim.

An interrupted preliminary memory-allocation run left a detached worker. It
was terminated; the kernel recorded one OOM event during that interval. Final
process-blocked fixtures are retried serially, after other fixture/family
workers finish, with the unchanged 120,000 ms per-pipeline timeout and 1,000
loop fuel. Both attempts and every prior conclusive observation are retained.
No interrupted attempt is counted as a pass.


### Complete assigned fixture evidence

The complete exact base rerun at `006fcd59` has 0 working / 0 broken /
437 blocked. None was already runnable through the base adapter. Stage 2 has
**118 working / 150 broken / 169 blocked**; no semantic rule was changed to
obtain the new agreements. Of the broken rows, 88 retain actual frontend gaps
in `variants[].gaps`; 62 are runtime/elaboration mismatches. They are not
presented as demonstrated upstream compiler/EVM bugs. Of the blocked rows,
168 retain adapter/host/configuration limits and one is a genuine isolated
process/resource block.

All 437 fixtures have exact-path commands with `--batch-size 1` and distinct
output directories. Required modes are 408 legacy+viaIR, 18 legacy-only and
11 viaIR-only. Every working fixture agrees in every required mode:
116 in both modes and two viaIR-only, retaining all 559 working call
observations. No expected source/expectation byte,
observation, premise, timeout, loop fuel or proof limit was weakened.

The serial retry of `array/external_array_args.sol` agrees in both modes;
its earlier process-blocked report remains attached. The enormous memory-array
case still ends with process exit 137 in both modes when run alone; the kernel
recorded two further OOM events during those isolated attempts. It stays
blocked, and cannot certify panic code 0x41. Both original and isolated reports
are retained. At the end of serial fixture testing the observed kernel OOM count was three:
one during the interrupted-worker interval and two during this isolated case.

The largest remaining exclusions are 65 pre-replay dynamic/aggregate adapter
blocks (including ABI v1), 47 physical-assembly layout blocks, ten multiple
reference-return wrappers, ten noncanonical inputs not admitted by the current
path, ten missing unique source ABI identities, eight nominal-enum ranges,
eight lazy/noncanonical aggregate probe refusals, four compound dynamic type
expressions, four generic panics and the explicit gas observation. One nested
fixed-array width guard also remains intact. These are retained runner
reasons, not guessed filename-based feature claims.

Final fixture wall times are 1,163 ms minimum, 10,618 ms median and 232,150 ms
maximum. These include verification, compiler/admission/build/replay and
contention, with two pipelines where required; they are not proof-checking
benchmarks. The final adapter leaf build took 4.6 s. No core representation or
proof-search budget changed.

The final model SHA-256 is
`28956cd3d7e4fa473b3118ea50d356e5497d9faf950bada4f8b370a852edb5f3`;
the runner SHA-256 is
`d8f0687fbf1de3d79eba143a9a8c9203aa133594612a14817a1488b7d07eb47d`.
The exact base model is `c86945ed62a18ffccf0b72b291c6271f44462f7b1d60b101e73fd2ec565c8699`.
The historical `cadb628c` summary instead records model
`c042a72f4d864a780a366ad4f27d148df0d7e213d33c37d4b6a51f0ad33710df`;
that historical evidence is not a fresh result on the task base.

[Per-fixture evidence](../../tests/upstream/group10-results.json) includes both
executed base and final results, all observations, mode requirements, exact
commands, source/fixture/compiler/archive/model/runner/report hashes and every
isolated retry. The first-stage evidence remains in
`tests/upstream/group10-stage1-results.json`. Shared changes are confined to
the upstream adapter/replay, its tests and snapshot publication; they depend
only on typed ABI lowering, `SourceFunction` identities and `revertWith`/typed
memory observation already on the task base. No unpublished group change is
assumed. Optional Bridge and obsolete SolKey readers are untouched.

### Final validation and review status

[The validation manifest](../../tests/upstream/group10-validation.json) records
all exact commands, exit codes, log hashes and retained long-log paths. The
final runtime versions and target builds pass. All 35 Lean replay outcome
controls, 18 Node tests, four existing ABI/exception source-family checks,
strict automation, reachability and layering pass. The independent reference
EVM suites pass; their compiler rejection cases remain reference checks.
Frozen TestSuite and sort checks pass. `lake build SolidityCorpus` passes all
257 jobs, and the frozen corpus check reproduces all 774 obligations with no
verdict, generated-module or scoreboard drift.

The broad `./run-lean.sh` gate is **inconclusive**, not passing. It completed
646/649 default targets before the unchanged `Examples/DecisionArrays.lean`
module was stopped after 2,729 seconds of wall time (the stated 45-minute
bound). Lean then exited 143 and Lake exited 1. There was no elaboration
diagnostic before interruption. All 298 modules in its local
import closure, including the target (297 dependencies plus the target), are
byte-identical to `006fcd59`; the closure does not include
the changed upstream adapter. The closure audit, interruption record and full
build log are retained in `.lake/upstream/group10-validation`. No proof limit,
expected result or representation was changed to obtain a gate result.
The earlier unrelated Faithfulness exit 135 did not recur in its separate
successful rebuild; the final serial corpus gate also passes.

The documentation-path check remains exit 1 for exactly the same 13 missing
references as the baseline; the complete missing-reference lists were compared
and are identical. No historical result, pinned archive/source/expectation,
frozen SolKey input or corpus expectation was changed.

Final read-only finder and independent skeptic passes verified the complete
437-path set, all 874 before/final report hashes and contents, fixture/source
pins, unchanged limits, all required working modes and all 559 working call
observations. Both retry histories remain intact. Neither reviewer opened
Lean workers or builds. No further correctness/provenance blocker was found.
The staged patch remains on `codex/group10-abi-vectors`; no master push or
merge is part of this handoff. Remaining semantic/adapter exclusions are
listed above and remain explicit rather than being counted as passing.

## M4: Group 10 continuation from c31e76b6 (2026-10-27)

The complete fixture replay is recorded below; the final build checks are recorded separately.
The prior commit, patch and all M3 evidence remain preserved on
`codex/group10-abi-vectors`. The continuation starts from the recorded
118 agreements / 150 mismatches / 169 blocks; these are not fresh failures
on a newly fetched master.

External-entry source bodies now opt into retained failure data through an
elaboration flag separate from `selfFrame`. The original transaction caller
and value are preserved, including internal calls and constructor initializers.
The flag participates in callee cache identities; ordinary calculus entry
points keep their existing reading and body sharing. ABI preparation, the
canonical probe and output serialization stay outside this source-data mode.
Existing indexed panic guards generate bytes before execution; generic panic
results still cannot certify a code. Local guard theorems prove exact failure
bytes, whole-state preservation on success, and priority of a prior failure.
No semantic/rule/state representation, dependency, axiom or proof budget changes.

Calldata provenance recognizes unshadowed allocating ABI/concatenation
builtins as fresh results. Operand writes and nested alias assignments remain
scanned; direct calldata aliases, casts and unsupported copying stay guarded.
A type-only dynamic-array marker preserves compound dimension order through
the existing typed recursive ABI decoder. Multiple reference returns and
reference-valued public getters remain separate unsupported interfaces.

Raw ABI v1 is admitted only behind a canonical-prefix probe, including its
primitive inputs. V2 reference/function inputs use the same prefix boundary.
Trailing bytes are retained in full as `calldataBytes`; high-level declared
objects cannot reach them, while physical calldata, `msg.data`, host and gas
observers remain excluded. Dirty/short prefixes and overlapping/noncanonical
layouts are not turned into source failures. All observations and required
pipelines remain mandatory. Runner scope metadata now describes this subset
explicitly instead of retaining M3's understated scalar wording.

The stopped `DecisionArrays` gate was investigated down to the arithmetic
walk with its existing `2^64` node bound. Merely projecting a verdict before
countermodel reconstruction did not remove that search cost. Its three
original verdict calls now have one closed compiler-replay certificate:
universal proofs of the two true source leaves and a checked finite arithmetic
assignment for the false leaf, connected through the actual typed reduction
and normalization equivalences. The kernel checks the normalized templates;
no extra premise is assumed. Existing coverage checks and the exact
`["proved", "refuted", "proved"]` output pin remain. The `csimp` equality
rewrites only that closed sample, leaving general solver behavior/bounds
unchanged. This is result replay, not a benchmark of original search or
countermodel materialization. The repaired per-file check passes; the complete Lake target now passes: unchanged `Decision` rebuilt in 738 s
and the certified `DecisionArrays` module in 43 s.

Read-only finder and independent skeptic reviews identified and closed the
source/ABI instrumentation boundary and confirmed ignored-suffix admission
under the existing host exclusions. Neither reviewer opened Lean workers.
The guard/observer and closed verdict certificate axiom audits report only
`[propext, Classical.choice, Quot.sound]`. New positive/negative controls cover
caller/value preservation, exact codes/reasons/custom errors, nested rollback,
fresh-result provenance, compound dimensions, v1 canonical admission and
retained arbitrary suffix bytes. The Node suite has 19 passing controls and
the configured Lean replay passes. Independent pinned reference suites retain
31 EVM vectors + 5 compiler rejections and 18 legacy/viaIR EVM runs + 20
compiler rejections; the rejections are reference checks, not Lean coverage.

Runtime scheduling is external to the repository: at most two actual Lean
processes, configured task threads of two, and a six-GiB resident-memory guard
per process in the sixteen-GiB executor. An initial virtual-address-space cap
was unsuitable: unchanged `DecideTyped` failed to create a thread at roughly
6.2 GB virtual but only 1.15 GB resident usage. This was an executor limit,
not a proof diagnostic. The unchanged target passed with resident-memory accounting;
no proof heartbeat, recursion, loop-fuel or fixture timeout limit is raised.
A transient executor reconnect preserved the worktree; the concrete
Lean/Lake/KeySort gate passed again after reconnecting.

The complete continuation rerun is in
`tests/upstream/group10-resume-results.json`: **175 agreements / 102 failures /
160 blocked**, versus the preserved M3 **118 / 150 / 169**. All 118 previous
agreements remain; 57 additional fixtures agree. The 347 passing pipeline
variants retain all 1,348 observations. The collector independently recompiles
the pinned ABI, reparses original vectors, and checks call order, failure flags,
exact return/revert bytes and full raw calldata. Every fixture has its exact
`--filter` command, `--batch-size 1`, distinct output directory, required modes,
source hashes and before/after report hashes. No historical result is overwritten.

The frozen model SHA256 is
`e7776fa6b2affdf0715e3efa222c8b059ab94fe1aeae883897965dde432ad721`;
runner SHA256
`dc97568c2597dc4cb65a4a153d21d3389f9fc5c8067b19aa70a2474efb5ea3fc`;
compiler SHA256
`6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`.
The compiler/source/archive pins remain M3's. Fixture elapsed times (including
compilation, admission and concurrent validation) range from 997 ms to
109,074 ms, median 3,969 ms; these are not proof benchmarks.

Failures remain visible: 85 frontend-gap fixtures, six explicit source-profile
refusals, six custom-error reference-argument elaboration failures, and five
admitted-source execution mismatches. The latter are legacy addmod/mulmod-zero
panic data, named-error payload order (two fixtures), exponentiation overflow,
and fixed-bytes unary behavior. Another 159 fixtures retain adapter/host/configuration
exclusions. The enormous-memory allocation fixture remains a resource block,
not a certified panic. Named error repair must capture typed effects in each
pipeline's evaluation order before assembling declaration-order payloads;
sorting source expressions would be unsound. This continuation does not claim
full repair or universal correctness from finite agreement.

The final read-only finder and independent skeptic audits found no false-pass
or provenance blocker. Both inspected the complete reports against the original
fixtures. The finder independently checked all 706 retained raw input arrays;
the skeptic recompiled pinned-solc ABI for every working fixture and regenerated
all working vectors. Both confirmed all 1,348 observations, required pipelines,
unchanged limits and previous evidence. Neither opened Lean workers or edited
files. The five actual admitted-source failures above remain failures; neither
review treats unsupported imports or resource termination as semantic success.


The build-only resource retry uses a separate twelve-GiB RSS guard and one
actual Lean worker after all fixtures and focused checks finish. The unchanged
`DecisionHashes` target, previously stopped at six GiB, passes in 324 s. The
unchanged `Decision` dependency passes in 738 s (the preserved prior run took
935 s), and `DecisionArrays` passes in 43 s. These completed targets supersede
the initial resource failures without changing proof budgets. All eight affected
source-family checks pass, as do strict automation (491 automatic, 61 budgeted,
11 refuted, zero pending), reachability (667 reachable, zero orphaned), and
layering (143 core modules, none reaching the elaborator).

Integration: the continuation is self-contained on the existing Group 10 lane;
it assumes none of another group's unpublished changes. Shared frontend edits
are limited to the failure-data policy/cache identity, allocating-builtin
provenance, and recursive ABI type expression recognition. The runner change
adds canonical-only v1 admission and corrects scope metadata. Resolve overlaps
with other lanes by preserving those boundaries and the controls; no core
representation, host implementation or optional Bridge dependency is required.

Final build validation is complete: `./run-lean.sh` exits zero, including the
649-job default build, 249-job Solkey TestSuite build and frozen sort check
(377 taclets, 131 read-bearing annotations, all matching). The TestSuite audit
finds no native proof shortcut, admitted theorem or mismatched axiom set in
its 30 trust-scanned modules: 552 derived, 11 refuted, zero pending, one
excluded and two skips. `SolidityCorpus` builds (257 jobs), and the frozen
473da8944c corpus probe reproduces all 774 rows without drift. Snapshot
verification, both Lean replay checks, all 19 Node controls and both independent
reference suites pass. No Lean diagnostic MCP is exposed; configured per-file
CLI checks were used. No new sorry, axiom, dependency or raised proof limit.
Lake job durations include cache/scheduling effects and are not pure proof
benchmarks. The cgroup OOM count remains at its prior three events.

The documentation path gate remains failed on the exact c31 baseline:
26 missing-reference diagnostics, consisting of 13 underlying omissions plus
13 quotations in the preserved M3 validation JSON. A detached c31 worktree
reproduces the identical missing-reference list without opening Lean workers.
The new validation record stores unmarked diagnostic text and hashes the raw
logs, avoiding further recursive quotations; historical evidence is unchanged.
This is an existing gate failure, not a passing check.

`tests/upstream/group10-resume-validation.json` records all commands, exits,
log hashes, proof audits, resolved preliminary resource failures and runtime
policies. Exported local artifacts are
`.lake/upstream/group10-continuation.patch` (from c31),
`.lake/upstream/group10-abi-vectors-v2.patch` (from 006fcd), and
`.lake/upstream/group10-resume-evidence.tar.gz` (raw reports and validation
logs). `.lake/upstream/group10-resume-export.json` records their SHA256 hashes
and exact head/base commits. The original patch remains unchanged. No push or
merge is performed. The 102 failures and 160 blocks remain explicit scope;
this milestone does not claim that all 437 fixtures are repaired.

The final read-only packaging finder and independent skeptic both approved:
all 25 main-check logs, five supporting logs and five runtime artifacts match
their recorded hashes and byte counts. Both confirmed the completed build,
frozen sort, corpus and functional checks, the exact c31 documentation failure,
and the remaining fixture scope. Neither opened Lean workers, ran builds or
edited files; no confirmed issue remains in the patch/evidence packaging.

## M5: repair the five admitted execution mismatches (2026-10-27)

This continuation preserves e430f436, all earlier reports/exports and the
437 immutable upstream inputs. It repairs the five concrete admitted failures,
rather than treating successful packaging as their completion. Diagnosis data
in `.lake/upstream/group10-five-diagnosis/before.json` retains complete first
mismatching bytes, one-based call positions, preceding observations, exact
source text and both compiler ASTs (including resolved declarations, names,
source positions and conversion types). Ten original and ten repaired entry
programs are quoted and kernel-defined against identical ASTs; their traces
and axiom outputs are retained there. The original model is executed in a
detached e430f436 comparison checkout, without changing the active lane.

Named reverts previously ignored argument names. `trigger2` was observation2
and emitted words7,2 after trigger1 correctly emitted2,7; `intWidening` was
observation1 and emitted200,1 instead of1,200. Both pipelines had the same
word-order mismatch, not evidence of a signed conversion fault. The reader
now resolves the error by declaration identity, validates its unique visible
identity, name, parameter kinds, arity and complete name permutation, captures
typed operands in legacy formal order or IR source order, then reorders only
the captured values. A legacy explicit order override is evaluated once and
quoted back consistently for body printing and the Contract. Its native data
evaluation site is inventoried; no theorem result is accepted from it.

Reference captures preserve storage aliases until encoding; copying into
memory before a later operand clears storage would be unsound. The skeptic
identified this and the corrected storage mutation controls now reject stale
bytes in both modes. Ordinary revert lowering retains declaration types until
its final abstract revert. Exact string/bytes error data reuses the existing
typed ABI encoder, with checked declared shapes and primitive ABI kinds;
unsupported aggregate reference interfaces remain explicit.

Legacy addmod/mulmod already captured and checked the modulus first. Its early
plain require produced empty bytes before the later modular panic guard.
Exact-data observation now uses the existing0x12 guard at the SAME position.
For fixed bytes, complement lowering now reads the original nominal width
before literal casts erase it and uses the existing mask-minus wrapped-word
operation. Generic complement bounds/involution and typed evalNum correspondence
are kernel-proved; ordinary integer complement follows its existing path.

Power overflow preceded narrow checks, and Checked.rangeU deliberately had no
power guard. History documents this ordinary empty-revert reading, not a
removed speed optimization. Only exact external-entry checked unsigned powers
now lower to existing checked multiplications: both operands captured once in
the pipeline order; zero/one/exponent-zero handled after those captures; for
base at least 2 an exponent at least 256 emits0x11; otherwise at most 255 loop
iterations use existing multiplication and narrow guards. Ordinary, unchecked
and explicit checking-option readings remain unchanged. The potential checking
cost of expression-to-loop lowering was warned about before implementation;
no intrinsic representation or core rule changed and no resource limit rose.

FiveControls proves the mathematical checked-multiplication recurrence,
cutoff and fuel bound, plus compact-byte word semantics. These facts are NOT
a universal equivalence theorem for generated Prog.runF loops or Solidity's
compiler. Kernel-checked typed programs and finite source controls separately
cover the emitted loop, both operand failure priorities, narrow uint8,2^255
fit/2^256 overflow, zero/one with huge exponents, unchanged unchecked/default
reading, signed words, selectors, full word order, empty/truncated/extended
payload rejection, source context, rollback and storage provenance. The new
control ASTs are pinned0.8.38 analysis evidence; compiler/reference checks are
not counted as Lean execution coverage.

The five original fixtures agree in all required modes and complete sequential
vectors in stage3, including every later dynamic-error and uint256 power
observation. Final hash-consistent inventory replays all 175 prior agreements,
the five repairs, and six directly affected reference-error elaboration cases.
The other 251 prior import/profile/host/configuration/resource reports retain
their original evidence and are explicitly marked not rerun; they are not
silently certified against the changed model. Final inventory and validation results
follow below. The full source trust scanner's25 unrelated
inventory findings reproduce exactly at e430f436; only the new override site
is added to its inventory. The c31 documentation failure also remains a known
failure. No new axiom, sorry, native proof shortcut, dependency or raised proof
heartbeat/fuel/timeout/resource bound is introduced.

The final selected inventory is complete: **184 agreements / 2 failures / 0
blocks among 186 fresh fixture runs**, with **365 passing pipeline executions
and 1,464 original observations**. All175 e430 agreements remain agreements;
the five requested failures and four related string/bytes error cases now
agree. No prior agreement regressed. The independently audited inventory is
`tests/upstream/group10-five-results.json`, including exact commands, original
fixture/source hashes, per-mode reports and every observation. Its mixed
fresh/prior437-path inventory is **184 agreements / 93 failures / 160 blocks**;
this is not a fresh replay of the 251 retained reports.

| Repaired exact fixture | Original first difference | Final legacy / viaIR observations |
| --- | --- | --- |
| errors/revert_error_named_parameters.sol | trigger2, call2: words7,2 instead of2,7 | 5 / 5, all agree |
| errors/revert_error_named_parameters_literal_conversions.sol | intWidening, call1: words200,1 instead of1,200 | 8 / 8, all agree |
| arithmetics/addmod_mulmod_zero.sol | f(0), call1 legacy: empty instead of Panic0x12; IR already agreed | 3 / 3, all agree |
| viaYul/exp_overflow.sol | f(255,131), call9: empty instead of Panic0x11 | 20 / 20, all agree |
| viaYul/unary_fixedbytes.sol | r_b25, call5: Panic0x11 instead of retained bytes25 vector | 15 / 15, all agree |

The table uses paths relative to `test/libsolidity/semanticTests/`; complete
unabbreviated expected and observed byte vectors remain in the diagnosis and
raw reports. Every earlier and later observation is retained. The four extra
agreements are require_different_errors_same_parameters,
require_error_multiple_arguments, require_error_string_literal and
require_inherited_error. The remaining two members of the original six
elaboration-failure cohort remain failures: `errors/revert_conversion.sol`
needs dynamic-array custom-error encoding; `errors/using_structs.sol` needs a
named struct capture location plus the aggregate struct error-encoding
interface. The latter currently stops at the generated capture-location gap,
before the unsupported aggregate encoder. Neither is recategorized as an
exclusion or claimed repaired. The85 prior import gaps, six profile refusals,
159 adapter/host/configuration exclusions and enormous-memory resource case
retain their own prior evidence, unmeasured after these changes.

The frozen repair model hash is
`0bcc84d08f447c52b7b579f0e3b4de7fa9829f8fe262655e3574474f3a827990`.
Runner, compiler and archive hashes remain respectively
`dc97568c2597dc4cb65a4a153d21d3389f9fc5c8067b19aa70a2474efb5ea3fc`,
`6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`,
and `9200f2a26b08be5b77faf877c44f5cfbf5ea95f1bccc45dae559d2fbc7cefb2d`.
Fresh fixture wall times were2.245–107.305 seconds (median 4.849), including
compilation, cache/admission and execution; these are not proof benchmarks.
The exact fixture120000ms/1000-fuel limits and existing6GiB worker policy are
unchanged. Final heavy validation uses the preserved12GiB serial policy only
after the fixture worker ends. No extra Lean worker is opened by reviews.

Completed focused checks use configured per-file CLI commands because Lean MCP
is not exposed: FiveControls (including independently varied caller/value),
the preserved upstream Replay, and13 ABI/exception/numeric/source families all
pass. Node runner regressions pass21/21, including the two original named-error
sequences and exact modular/power/fixed-byte vectors. Strict automation reports
491 automatic,61 budgeted,11 refuted and0 pending; reachability reports667
reachable/0 orphaned; layering reports143 core modules/0 elaborator reach.
All ten final lowered entry quotations kernel-recheck with only propext;
headline mathematical controls list only propext, Classical.choice and
Quot.sound. Pinned reference checks separately pass31 ABI vectors plus five
compiler rejections,18 ABI-hex EVM runs plus20 rejections, and34 additional
byte-exact source controls; none is counted as Lean coverage.

Finder and independent skeptic both audited the final fixture evidence without
opening Lean workers or running builds. They verified all437 raw report hashes
(including retained reports), the exact186 selected set,365 passing mode
sequences,1,464 observations and736 raw calldata arrays. The skeptic also
independently recompiled each fresh working ABI with the pinned compiler. Both
confirmed the five exact fixtures, unchanged175 agreements, remaining two
failures and explicit251-report evidence boundary. Confirmed review findings
(storage-alias preservation, resolved identity equality, exact cohort assertion
and retained-report wording) are fixed. Final build/log packaging review is
recorded with the completed validation manifest below.

The reference source controls also initialize the exact short-storage bytes
word for data=hex61 and check storageNamed/storageReverse in both pipelines.
All four return the empty bytes error payload after the later clear, confirming
that early storage-to-memory snapshots would be wrong. The Lean controls
separately check rollback to the original one-byte storage value; reference
runCode output is used only to confirm the payload timing, not rollback.

Final invalidated functional gates pass: the default build 649 jobs, SolKey
TestSuite 249 jobs, standalone check-testsuite, Corpus 257 jobs and frozen corpus
parity. The sort check actually parsed 377 taclets/131 read-bearing entries and
matched all 131 annotations against the configured frozen rules file (SHA256
02b7a995c9aaf1a856019d7071ca3e75a57de91b071c93b24ebf6ae7eef989eb).
TestSuite parity is 564 functions:552 derived,11 refuted,0 pending,0 divergent,
1 excluded and 2 skip. Frozen SolKey 473da8944c corpus parity is 774 obligations:
552 derived,11 refuted,1 excluded,2 skip,70 proved,37 unsupported and 101 unported.
These pre-existing corpus classifications are separate from the 437 upstream
fixture inventory and do not increase its agreement count.

`tests/upstream/group10-five-validation.json` retains exact commands and hashes
for 34 final check logs,5 supporting logs,12 runtime/script artifacts and 20 clearly
separated preliminary experiment logs. 32 checks exit 0. Documentation-paths
exits 1 with exactly the 26 c31 diagnostics (13 underlying references repeated by
preserved M3 evidence); trust exits 1 with exactly the 25 e430 inventory findings.
Both lists match their complete preserved baselines. These two gates remain
known failures, never passes. The first manifest attempt correctly refused a
missing initial verification exit file; a new uniquely named final snapshot
verification completed successfully and supplied its actual exit status.

The single-worker heavy build completed under the unchanged 12 GiB RSS policy;
no new OOM kill occurred. Observed module wall seconds (current/prior) were
Join 93/85, CallbackStrategy 198/211, OpenLoops 492/510, DecisionHashes 309/324,
Decision 760/738 and DecisionArrays 44/43. Scheduling/lock waits can contribute
to these durations; they are not controlled benchmarks. No intrinsic core
representation or proof budget was changed during validation;
fixture fuel/timeout and existing resource caps remain unchanged. The Solidity
model and runner trees remain identical to 8a3d7b6d
throughout the final gates; later changes only strengthen controls and record
evidence/documentation. Previous reports/exports and all historical bytes are
unchanged. Work remains local on codex/group10-abi-vectors; no push or merge.

Final finder and independent skeptic audits approved all 34 final log hashes,
5 supporting logs, 20 preliminary logs and 12 runtime artifacts, the completed
gate outputs and the exact baseline failures. Neither opened Lean workers,
ran builds or edited files. Their confirmed metadata findings are fixed:
nonempty integer exit parsing, exactly exit 1 for known failures, completion
marker and explicit retained-report wording. No confirmed review issue remains.
The final validation record includes both completed approvals.

New exports use group10-five-continuation.patch (from e430f436),
group10-abi-vectors-v3.patch (from 006fcd59), group10-five-evidence.tar.gz and
group10-five-export.json under .lake/upstream. The export manifest records the
exact local commit, sizes and SHA256 values; the writer preserves every earlier
Group 10 patch/archive/export manifest, refuses overwrites and verifies each
archive member by readback. All work remains on the isolated local lane.

## M6: aggregate custom errors and compound decoder metadata (2026-10-27)

This continuation preserves ea43de13, 8a3d7b6d, every earlier report/export and
all 437 upstream inputs and expectations. The two remaining fresh failures
stopped before any runtime observation: revert_conversion at custom-error
array encoding, and using_structs at a generated named struct capture without
a location. Neither was recategorized as an exclusion. New diagnosis artifacts
are under .lake/upstream/group10-aggregate-diagnosis; the original before.json
is preserved, with a separate hashed clarification that its zero-position
sentinel means no observation executed, not a differing call at position zero.
Complete source/AST declarations, argument provenance and all six final typed
entry programs are retained there.

The pinned revert_conversion error is declaration8, E(string a,uint256[] b),
with parameter IDs3 and6. Its f() pushes7 to storage x and reverts with selector
59e4d4df, head offsets64/128, string abc and the one-element array[7]. The
using_structs error is declaration16, E(uint256 a,S s,uint256 b), parameter
IDs9/12/14; S is declaration7. Its true then false call sequence must emit the
same e96e07f0 payload: outer words2,96,7, then struct words9,64,3 and padded abc.
The source and reports preserve every byte, including the complete196-byte
and228-byte payloads respectively. Both required pipelines now execute every
original observation:1/1 for revert_conversion and2/2 for using_structs.

Named custom-error captures now recognize reference structs by their resolved
StructDefinition identity. Locations follow actual storage/calldata operands;
constructed memory values remain memory values. Existing pipeline scheduling,
name permutation and fresh-name checks remain in place. Calldata captures
still fail the existing slice-origin gate where the model lacks an admitted
view; they are never silently converted into memory. The new source controls
pin both refusals explicitly.

Exact custom-error aggregate encoding reuses the existing typed ABI encoder
and existing raw memory-revert statement. Before admitting a reference it
checks the actual RefTy against the declared parameter and checks all declared
width/shape rows. Aggregate marks remain absent so the existing recursive
encoder sees the actual type and place. Storage and memory aliases remain live
until all operands have evaluated, including later mutations. Mappings and
internal-function encodings remain refused; a recursive custom-error admission
guard additionally keeps nominal enum aggregates refused. Ordinary ABI enum
encoding is unchanged. No intrinsic representation, core operation, inference
rule or dependency changed. History was inspected; this is interface reuse,
not reversal of a speed optimization.

AggregateErrorControls checks empty/nonempty arrays, struct field order and
signed words, nested arrays and offsets, source and named ordering, storage
clears, indexed storage aliases, memory-array and memory-struct mutation,
prior assertion failure, caller/value, post-failure storage reads and exact
selectors. Wrong offsets/lengths/order/sign extension, stale snapshots,
empty/truncated/extended payloads and malformed declared reference types are
rejected. AggregateErrorBoundary adds a declared distinct same-layout struct,
nested enum refusal and exact counts for calldata refusals. The mathematical
raw_error_exact theorem instantiates the existing operation-preserving
TRun.revertData_mem theorem: the encoder buffer is forwarded byte for byte.
Its only axioms are propext, Classical.choice and Quot.sound. The six original
entry program quotations kernel-check with propext only. Finite compiled
frontend/replay checks are recorded separately; no universal correctness
claim for the frontend or aggregate encoder is made.

The required next repair was selected from actual retained failure reasons,
not filenames. Three fixtures reproduced missing compound decoder width rows:
memory_arrays_static, arrays_complex_memory_index_access and
nested_array_element_memory_to_memory. exprShape previously recognized only
a bare type or one fixed dimension, while the decoder already used the
recursive abiTyExpr? parser. It now uses that same parser and elabTyW for
compound dimensions, retaining the builtin-shadowing guard and strict shape
checks. All three complete in both required modes with1/1,1/1 and6/6 original
observations respectively. CompoundAbiShape pins metadata, malformed type
arity, wrong widths/byte kinds, shadowing and nominal enum refusal. Since the
type reader is partial elaborator code, those finite metadata checks run as
frontend checks, not kernel computation claims. The Node regression pins all
eight original compound observations and complete output bytes, together with
selected calldata dimensions, lengths and the final calldata word. The final
inventory collector separately audits every raw calldata byte.

Supporting reference-EVM controls independently check32 byte-exact aggregate
source cases. The first indexed-storage reverse-order hypothesis failed in a
preserved preliminary script; the corrected control matches[11] in both modes.
Reference output is supporting source evidence, never Lean coverage or a
rollback theorem. An exploratory global/named struct internal-function
parameter control hit an existing unknown-type import gap; direct source
increments instead isolate memory-struct alias timing without claiming that
separate internal-call gap repaired. Preliminary checks and diagnostics remain
separate from final checks.

Final replay, validation, independent evidence review and immutable exports
are recorded below when complete. The complete437 assignment remains
incomplete while retained failures/blocks remain; passing selected repairs
must not be read as a fully repaired group.

Before the final model freeze, the skeptic compiled a concrete named slice
operand and confirmed solc's additional `calldata slice` type suffix. The
capture detector now recognizes it for bytes and arrays. Pinned
ErrorCaptureLocations controls check both generated declarations remain
calldata in legacy and IR modes, independently of later view admission.
The superseded partial inventories and focused logs remain preliminary
evidence. The slice-corrected intermediate candidate used model
`d8119075d7d2c6d8b53ce4e1909dc6c20220df431e1a0fdbcb3545bd94375b6a`;
the final source-enum audit below establishes the final frozen model.
The independently reviewed implementation is local commit e7f427c9.

AggregateRollback additionally kernel-specializes the existing self-call catch
law to raw aggregate error bytes: catch starts from the original complete
caller state (heap, storage and transaction included), then allocates the
retained bytes. It preserves the nonzero self-address, actual callee failure
and byte-length bound premises. No unconstrained bytes oracle or discarded
callee-failure premise replaces that connection. The finite post-failure
storage controls and caller/value controls remain separate execution evidence.

The final fail-closed audit also found a concrete source enum erasure:
errorMembers uses tyText, whose enum table lowers Flag[] to uint[] before the
typed enum marker guard can run. Admitting that value would use the wrong
E(uint256[]) signature for the compiler's E(uint8[]) and lose cardinality.
The source reader now checks resolved formal array/struct declarations before
that erasure, for both positional and named reverts. A bounded worklist follows
struct and UDVT declarations, visits referenced structs once, and refuses
nominal enums, unknown/ambiguous IDs, malformed struct-member metadata and
unfinished traversal. This is an admission restriction, not a new enum model.
The typed guard remains necessary for directly constructed typed contracts.

The initial pinned EnumErrorControls source/AST controls checked three direct
revert refusals per mode (enum[], named enum[][] and an enum-containing struct)
at the intended nominal-enum boundary; the constructor audit below expands
this to seven cases per mode. Kernel checks pin the report count
and refusal status; compiled helper controls reject missing/duplicate IDs in
both orders, missing/non-array members and members without a type, while a
valid enum-free struct remains accepted. Confirmed finder/skeptic hardening
findings are fixed. No actual upstream expectations or prior reports changed.
The enum-safe guard and rollback regression are local commit32c8d660, after
e7f427c9. The direct-revert guard candidate used model
`d343c06fab202705e18d4eed2f35fd73702a13c50ce74bb45c242140da7ad216`;
its interrupted inventory remains preliminary. The constructor-entrypoint
audit below establishes the final frozen model and output tree.

The entrypoint audit confirmed that require(condition,E(...)) renders its
error constructor through the generic expression reader, so a guard only on
RevertStatement was insufficient. Both entrypoints now call the same source
aggregate-type guard before rendering operands. Generic aggregate constructors
also retain singleton declaration resolution, callee name/visible declaration
identity, formal arity and parameter-kind checks. Compiler metadata identifying
an error constructor requires an actual unique ErrorDefinition before any
identifier-spelling fallback. Eight synthetic AST mutations retain that error
metadata while removing the ID, using an absent/wrong-kind ID or duplicating
the declaration; both modes refuse them at the custom-error boundary.

EnumErrorControls now pins seven source refusals per mode, including false and
true require conditions, named nested arrays and struct error operands. These
are deliberate admission refusals, not passing runtime observations. Positive
RequireAggregateControls separately checks positional enum-free array/struct
payloads, false-path storage rollback, true-path eager operand effects, later
storage clears and stale payload rejection in both modes. Generic named error
constructors inside require remain unsupported because the generic parameter
lookup has no error declaration parameters; no named-require ordering support
is claimed. Source evaluation/capture of named direct reverts remains supported
and retains its existing controls.

The reviewed constructor-entrypoint repair is local commit118bad2c. Final
validation is strictly serial under model
`c580cecf8869a4bd4eaa80b298d640850fe5bab91d6ef651a88a6641a642615e`,
using .lake/upstream/group10-aggregate-reviewed-inventory. Earlier candidate
inventories, build/control failures and diagnosis artifacts remain preserved,
explicitly separate from this final replay and its gates.

The final selected replay and two independent read-only fixture audits pass:
**189 agreements / 0 failures / 0 blocks**, **375 required pipeline executions**
and **1,486 original observations**. All 184 prior agreements remain agreements;
exactly five fixtures improve. Both auditors independently recompiled the pinned
ABI and checked every observation, source/fixture pin, raw calldata byte and all
437 on-disk raw report hashes. The 248 retained report objects and their old
provenance remain unchanged and explicitly marked not rerun. Correct canonical
model hashing uses the runner's lexically sorted path strings; an earlier manual
Path-component checksum in a draft/message was corrected without modifying any
verified report.

| Exact repaired fixture (under test/libsolidity/semanticTests/) | Prior evidence | Final legacy / viaIR observations |
| --- | --- | --- |
| errors/revert_conversion.sol | import/elaboration failure, none executed | 1 / 1, complete exact payloads |
| errors/using_structs.sol | generated reference capture lacks location, none executed | 2 / 2, complete true/false sequence |
| abicoder/calldataDecoding/array/memory_arrays_static.sol | adapter block: missing compound decoder width rows | 1 / 1, exact original returns |
| array/indexAccess/arrays_complex_memory_index_access.sol | adapter block: missing compound decoder width rows | 1 / 1, exact original returns |
| array/copying/nested_array_element_memory_to_memory.sol | adapter block: missing compound decoder width rows | 6 / 6, all original vectors |

The complete mixed 437 inventory is **189 agreements / 91 failures / 157
blocks**, not a fresh 437 replay. Remaining retained classifications are 85
explicit frontend import gaps, six source-profile refusals, 156 adapter/host/
configuration exclusions and one enormous-memory resource block. No retained
case is silently certified against the changed model. Named aggregate require
constructors remain an explicit source boundary; recursive reference copying,
noncanonical/lazy ABI layouts and dependent host/log/gas/configuration behavior
still require their own actual typed interfaces and validation. The complete
Group 10 assignment is not claimed repaired.

The final immutable report is tests/upstream/group10-aggregate-results.json.
Every fresh row records the exact invocation, including its full --filter path,
--batch-size 1, distinct --out directory, required pipelines, complete ordered
observations and raw report SHA256. Source/compiler/runner/archive pins are
checked independently by the collector. The compiler remains SHA256
6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390,
runner dc97568c2597dc4cb65a4a153d21d3389f9fc5c8067b19aa70a2474efb5ea3fc,
and archive 9200f2a26b08be5b77faf877c44f5cfbf5ea95f1bccc45dae559d2fbc7cefb2d.
The representative command is node scripts/solidity-upstream.mjs run --compiler
/workspace/.setup/soljson/soljson-v0.8.38+commit.1835d247.js --filter
<exact fixture path> --batch-size 1 --out <distinct reviewed-inventory directory>;
the report's command array retains the actual separate flag/value arguments.
The original 120000ms process limit and 1000 loop fuel remain unchanged.

Focused final-model checks all pass: the14 ABI/exception/numeric/source families,
existing upstream Replay and M5 controls, RevertData, configured CLI checks for
all four changed modules, and all seven new control modules. All six final
original entry-program quotations kernel-check with propext only. Exact-buffer
and bounded caller-state/heap rollback laws use only propext, Classical.choice
and Quot.sound. No new axiom, sorry, native proof shortcut or raised proof limit
is introduced. Lean MCP is not exposed; actual per-file CLI commands and logs
are retained in the validation record.

Node regressions pass23/23. Strict automation reports491 automatic,61 with a
step budget,11 refuted and0 manual/pending; reachability is667 reachable with0
orphaned, and layering is143 core modules with0 elaborator reach. Supporting
reference checks pass31 pinned ABI vectors plus five compiler rejections,
18 ABI-hex EVM runs plus20 compiler rejections, and the separate32 source
aggregate controls. Reference/diagnostic checks are not counted as Lean coverage.

Final serial integration validation completed on the same model: the default
build completed 649 jobs, SolkeyTestSuite completed 249 jobs, and frozen sort
checking matched 131 read-bearing taclets out of 377 parsed. The TestSuite
checker passed with 564 functions = 552 derived + 11 refuted + one excluded,
zero pending/divergent, and two skips. SolidityCorpus built 257 jobs; its
checker passed all 774 classified obligations (552 derived, 11 refuted, one
excluded, two skip, 70 proved, 37 unsupported and 101 unported). These inventory
categories are preserved; they are not additional upstream runtime agreements.
The final validation manifest is tests/upstream/group10-aggregate-validation.json;
it records each actual command, exit code, log byte length and SHA256.

The documentation scanner remains a known failure (exit 1): its 26 diagnostics
are byte-list identical to c31, including 13 references repeated by preserved
M3 evidence. The trust inventory remains a known failure (exit 1), with the
same 25 inventory-drift diagnostics as ea43de13. Neither is counted as passing.
All functional checks in the manifest exit 0. The baseline cgroup OOM-kill
count stays three: no new OOM kill occurred. Memory-max events increased from
16345 to 17005 during the complete work; pressure is not reported as absent.

Fresh fixture wall times are 2589ms minimum, 4975ms median and 105956ms maximum.
Selected Lake module wall times are Join92s, Recursion309s, CallbackStrategy744s,
OpenLoops509s, DecisionHashes302s, Decision752s and DecisionArrays47s. These
include wrapper/lock queue waits and are not native CPU benchmarks; for example,
the CallbackStrategy native process was sampled at178s/1604284KiB RSS.
OpenLoops was sampled at482s/8237700KiB RSS. Samples are not peak measurements.
The unchanged 6GiB focused/fixture and 12GiB heavy policies, threads2 and serial
scheduling were retained. Expensive checks finished without a retry, raised
heartbeat, timeout, fuel or memory cap.

The implementation commits are e7f427c9, 32c8d660 and 118bad2c, descended from
ea43de13 and all earlier lane work. Final read-only finder and independent
skeptic evidence approval is recorded separately in
 tests/upstream/group10-aggregate-review.json. New exports use
.lake/upstream/group10-aggregate-continuation.patch (since ea43de13),
.lake/upstream/group10-abi-vectors-v4.patch (since the upstream import), and
.lake/upstream/group10-aggregate-evidence.tar.gz, with exact final commit,
SHA256 and archive readback details in group10-aggregate-export.json. The
separate group10-aggregate-export-review.json records independent export audits.
Earlier reports and export files remain unchanged. All work stays local on
codex/group10-abi-vectors; there is no push or merge.

Both final read-only reviews approved the actual fixture and gate evidence,
including all 46 final-log hashes, two supporting logs, 101 preliminary logs
and 11 runtime artifacts. Neither reviewer opened a Lean/build worker. A later
user-requested git pull --ff-only fetched origin/master at a7a35aa5 but exited
128 because the branches diverged; no fast-forward, merge, rebase, reset or
working-file replacement occurred. The evidence remains for this isolated
lane and is not a validation claim about the newly fetched master.
