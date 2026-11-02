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
- **Inherited and renamed function values** keep their source ABI identity:
  `Base.f.selector`, `this.f.selector` of an override, `this.h.selector` and
  `abi.encodeCall(this.h, …)` of an inherited function the importer renames,
  external function values of `f` and `h` (`.selector`), and `abi.encode` of
  the value of `h` all carry the source declaration's selector
  (`Examples/Tactics/InheritedSelectorsImport.lean`, checked against pinned
  solc by `scripts/abi-entry-probe.mjs --inherited`). Calling through an
  external function value is refused by name for inherited and own functions
  alike (function-value dispatch).
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
VM location `.setup/activate.sh` sourced: Lean 4.24.0 (`797c613e`), Lake
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
execution (for ABI coder v2 entries superseded by the typed entry decoder:
see "Entry decoding: lazy and noncanonical layouts" below). This deliberately blocks noncanonical, overlapping, unaligned or
malformed reference layouts: external calldata references can defer checks
that a memory decoder performs eagerly. Dirty unused array elements therefore
cannot certify an expected failure. Primitive v2 entry decoding checks widths,
sign extension, Boolean values, lengths and fixed-bytes padding before the
body. ABI v1 raw replay remains blocked using actual compiler pragma metadata,
including comments between pragma tokens. Native scalar replay remains
available for supported canonical v1 cases. Raw replay with inline assembly
is blocked because physical calldata/memory layout observations need their own
adapter. Nominal enum ranges are blocked recursively before erasure (since
2026-11-01, top-level v2 enum parameters decode at their declared
cardinality: "Next item: nominal enum cardinalities at external entry").

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
VM location `.setup/abi-reference`; the core/package dependencies are unchanged.
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
VM setup: soljson/soljson-v0.8.38+commit.1835d247.js --filter
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

## Entry decoding: lazy and noncanonical layouts (lane CF1, 2026-10-31)

Owner: lane CF1 (`cloud/relocated-20261031/abi-entry-decoding`). Base
`aaa9db5c`. This section replaces, for ABI coder v2 external entries, the
byte-identical decode/re-encode admission of M3 ("Reference/function arguments
require byte-identical decode/re-encode before execution") by a typed model of
solc's generated entry decoder with kernel proofs. ABI coder v1, constructor
arguments, function-valued parameters and nested enums keep the M3 gate
unchanged (top-level v2 enum parameters: see the enum item at the end).

### Baseline (reproduced on the base before editing)

Every fixture whose retained Group 10 reason names lazy/noncanonical ABI
decoding or a compound type expression (`tests/upstream/cf1-abi-entry-fixtures.txt`,
42 fixtures, including all 27 of the "noncanonical ABI input" vector set) was
rerun on the base with the unchanged runner, one exact path per invocation
(`scripts/abi-entry-fixtures.sh`, `--batch-size 1`). The base gives **13
working / 29 blocked**; the documents above were partly stale: the three
compound decoder fixtures of M6 and ten of the 27 noncanonical inputs already
work (v2 primitive entry checks), and most remaining "noncanonical input"
fixtures now block on other named reasons.

| Fixture (under semanticTests/) | Base verdict | Base reason | Classification |
|---|---|---|---|
| abicoder/calldataDecoding/array/calldata_array_length_v2.sol | blocked | noncanonical calldata requires lazy ABI decoder replay | missing typed semantics: v2 lazy/noncanonical entry decoding |
| abicoder/calldataDecoding/array/calldata_array_indexing_1d_2d_v2.sol | blocked | calldata requires lazy/noncanonical ABI decoder replay | missing typed semantics: v2 lazy/noncanonical entry decoding |
| abicoder/calldataDecoding/array/calldata_array_indexing_3d_v2.sol | working | functional runtime vectors match in every required source evaluation mode | already working (stale doc entry) |
| abicoder/calldataDecoding/array/calldata_nested_array_static_reencode_v2.sol | blocked | calldata requires lazy/noncanonical ABI decoder replay | missing typed semantics: v2 lazy/noncanonical entry decoding |
| abicoder/validation/array_exceeds_calldatasize_no_revert_string.sol | blocked | calldata requires lazy/noncanonical ABI decoder replay | missing typed semantics: v2 lazy/noncanonical entry decoding |
| array/calldata_array_bounds_check_nested_bytes.sol | blocked | noncanonical calldata requires lazy ABI decoder replay | missing typed semantics: v2 lazy/noncanonical entry decoding |
| array/concat/bytes_concat_nested.sol | blocked | noncanonical calldata requires lazy ABI decoder replay | missing typed semantics: v2 lazy/noncanonical entry decoding |
| array/copying/calldata_2d_bytes_to_memory_2.sol | blocked | noncanonical calldata requires lazy ABI decoder replay | missing typed semantics: v2 lazy/noncanonical entry decoding |
| array/copying/nested_array_calldata_to_memory.sol | blocked | noncanonical calldata requires lazy ABI decoder replay | missing typed semantics: v2 lazy/noncanonical entry decoding |
| array/copying/nested_array_element_memory_to_memory.sol | working | functional runtime vectors match in every required source evaluation mode | already working (stale doc entry) |
| array/indexAccess/arrays_complex_memory_index_access.sol | working | functional runtime vectors match in every required source evaluation mode | already working (stale doc entry) |
| smoke/bytes_and_strings.sol | blocked | noncanonical calldata requires lazy ABI decoder replay | missing typed semantics: v2 lazy/noncanonical entry decoding |
| strings/concat/string_concat_nested.sol | blocked | noncanonical calldata requires lazy ABI decoder replay | missing typed semantics: v2 lazy/noncanonical entry decoding |
| abicoder/cleanup/enum_v1.sol | blocked | nominal enum ABI range not adapted | runner exclusion: nominal enum range (declaration metadata) |
| abicoder/cleanup/enum_v2.sol | blocked | nominal enum ABI range not adapted | runner exclusion: nominal enum range (declaration metadata) |
| arithmetics/checked_add_v1.sol | blocked | calldata requires lazy/noncanonical ABI decoder replay | runner exclusion: ABI v1 canonical-only gate (v1 decoder not modelled) |
| arithmetics/checked_add_v2.sol | working | functional runtime vectors match in every required source evaluation mode | already working (stale doc entry) |
| cleanup/cleanup_address_types_v1.sol | blocked | calldata requires lazy/noncanonical ABI decoder replay | runner exclusion: ABI v1 canonical-only gate (v1 decoder not modelled) |
| cleanup/cleanup_address_types_v2.sol | working | functional runtime vectors match in every required source evaluation mode | already working (stale doc entry) |
| cleanup/cleanup_bytes_types_v1.sol | blocked | calldata requires lazy/noncanonical ABI decoder replay | runner exclusion: ABI v1 canonical-only gate (v1 decoder not modelled) |
| enums/enum_with_256_members.sol | blocked | nominal enum ABI range not adapted | runner exclusion: nominal enum range (declaration metadata) |
| operators/shifts/shift_right_garbled_signed_v1.sol | blocked | raw ABI replay with physical calldata/memory assembly not adapted | runner exclusion: physical calldata/memory assembly |
| operators/shifts/shift_right_garbled_signed_v2.sol | blocked | raw ABI replay with physical calldata/memory assembly not adapted | runner exclusion: physical calldata/memory assembly |
| operators/shifts/shift_right_garbled_v1.sol | blocked | raw ABI replay with physical calldata/memory assembly not adapted | runner exclusion: physical calldata/memory assembly |
| operators/shifts/shift_right_garbled_v2.sol | blocked | raw ABI replay with physical calldata/memory assembly not adapted | runner exclusion: physical calldata/memory assembly |
| operators/shifts/shift_right_negative_lvalue_signextend_int16_v1.sol | blocked | calldata requires lazy/noncanonical ABI decoder replay | runner exclusion: ABI v1 canonical-only gate (v1 decoder not modelled) |
| operators/shifts/shift_right_negative_lvalue_signextend_int16_v2.sol | working | functional runtime vectors match in every required source evaluation mode | already working (stale doc entry) |
| operators/shifts/shift_right_negative_lvalue_signextend_int32_v1.sol | blocked | calldata requires lazy/noncanonical ABI decoder replay | runner exclusion: ABI v1 canonical-only gate (v1 decoder not modelled) |
| operators/shifts/shift_right_negative_lvalue_signextend_int32_v2.sol | working | functional runtime vectors match in every required source evaluation mode | already working (stale doc entry) |
| operators/shifts/shift_right_negative_lvalue_signextend_int8_v1.sol | blocked | calldata requires lazy/noncanonical ABI decoder replay | runner exclusion: ABI v1 canonical-only gate (v1 decoder not modelled) |
| operators/shifts/shift_right_negative_lvalue_signextend_int8_v2.sol | working | functional runtime vectors match in every required source evaluation mode | already working (stale doc entry) |
| operators/shifts/shift_underflow_negative_rvalue.sol | working | functional runtime vectors match in every required source evaluation mode | already working (stale doc entry) |
| userDefinedValueType/cleanup.sol | blocked | raw ABI replay with physical calldata/memory assembly not adapted | runner exclusion: physical calldata/memory assembly |
| userDefinedValueType/cleanup_abicoderv1.sol | blocked | raw ABI replay with physical calldata/memory assembly not adapted | runner exclusion: physical calldata/memory assembly |
| userDefinedValueType/conversion.sol | working | functional runtime vectors match in every required source evaluation mode | already working (stale doc entry) |
| userDefinedValueType/conversion_abicoderv1.sol | blocked | calldata requires lazy/noncanonical ABI decoder replay | runner exclusion: ABI v1 canonical-only gate (v1 decoder not modelled) |
| userDefinedValueType/parameter.sol | blocked | raw ABI replay with physical calldata/memory assembly not adapted | runner exclusion: physical calldata/memory assembly |
| viaYul/detect_add_overflow.sol | working | functional runtime vectors match in every required source evaluation mode | already working (stale doc entry) |
| viaYul/detect_div_overflow.sol | working | functional runtime vectors match in every required source evaluation mode | already working (stale doc entry) |
| viaYul/detect_mul_overflow.sol | working | functional runtime vectors match in every required source evaluation mode | already working (stale doc entry) |
| viaYul/function_entry_checks.sol | blocked | noncanonical ABI input requires ABI decoder replay | runner exclusion: JS scalar adapter (dirty word / extra data on a scalar signature) |
| viaYul/unary_operations.sol | blocked | raw ABI replay with physical calldata/memory assembly not adapted | runner exclusion: physical calldata/memory assembly |

So the missing typed semantics is the ten v2 lazy/noncanonical refusals
(the "ten noncanonical inputs" and the "lazy aggregate probe refusals" of M3
name the same set as it stands now); the four "compound dynamic type
expressions" are three working fixtures and `calldata_nested_array_static_reencode_v2.sol`,
whose remaining refusal is the lazy one. ABI v1 (7), nominal enums (3),
assembly (6) and the scalar adapter (1) are runner exclusions outside this
lane's decoder.

### What solc's generated decoder does

Evidence: `scripts/abi-entry-probe.mjs` runs `tests/abi-0.8.38/LazyEntry.sol`
with the 57 vectors of `tests/abi-0.8.38/LazyEntry.vectors.json` and every
vector of the 22 fixtures in its `FIXTURES` list (the lane fixtures that
compile with their vectors), with the pinned compiler (SHA-256 `6c74ffba…`),
in four configurations: legacy and via-IR, each with the optimizer off and on
(fixtures in their required pipelines only). The script asserts that the
configurations agree on every vector, that every probe vector has its pinned
outcome and that every fixture vector has its upstream expectation. The
function names below are the Yul functions solc 0.8.38 emits (identical in
both pipelines, since legacy codegen also takes the v2 decoder from
`ABIFunctions`).

* **Head.** `abi_decode_tuple_*` first reverts with empty data unless the whole
  head fits: `slt(sub(dataEnd, headStart), headSize)`, with `headStart = 4`.
  Then each parameter in order. A dynamic parameter's offset word is unsigned
  and reverts above `0xffffffffffffffff`; it is relative to `headStart`.
* **Value parameters** are loaded and validated immediately
  (`validator_revert_t_<k>`: the word equals its cleanup), so a dirty `uint8`,
  `int16`, `bool`, `bytes3` or `address` reverts at entry.
* **Memory parameters** (`abi_decode_t_<T>_memory_ptr`) are decoded eagerly
  and recursively at entry. For `bytes`/arrays: `slt(add(offset, 0x1f), end)`,
  then the length, then **allocation** (`array_allocation_size_*` panics with
  `Panic(0x41)` above `2^64 - 1`, `finalize_allocation` when the free pointer
  would pass `2^64 - 1`), and only then the region check
  `gt(add(src, length * stride), end)`. Probes: a `bytes memory` length of
  `2^64 - 1` or `2^64` gives `Panic(0x41)`; `2^32` and `2^63` give an empty
  revert. Each dynamic element's offset is unsigned, relative to the start of
  its sequence's (or struct's) element region, and reverts above `2^64 - 1`.
  Static arrays check `slt(add(offset, 0x1f), end)` and their whole region;
  structs check `slt(sub(end, headStart), headSize)`. Every word element is
  validated. Overlapping, out-of-order and unaligned tails, unpadded final
  `bytes` and dirty `bytes` padding are accepted; invalid UTF-8 in a `string`
  is accepted.
* **Calldata parameters** get only the outermost object's entry check
  (`abi_decode_t_<T>_calldata_ptr`): `bytes`/arrays check the head slot, the
  length (`≤ 2^64 - 1`, an empty revert, no allocation) and the element region
  `arrayPos + length * stride ≤ end`; a dynamic struct its head; a static array
  of dynamic elements its head region. A static calldata array or struct of
  words is not validated at entry (probe: a dirty `uint8[2] calldata` element
  is accepted unless read).
* **Lazy access.** Reading a calldata element validates it then:
  `calldata_array_index_access` (index check, `Panic(0x32)`), then for a
  dynamic element `access_calldata_tail(base, ptr)`: the relative offset is a
  **signed** word, checked by `slt(rel, sub(sub(calldatasize(), base),
  sub(tailSize, 1)))`, added modulo `2^256`; for `bytes`/arrays the length is
  at most `2^64 - 1` and `sgt(addr + 32, sub(calldatasize(), length * stride))`
  reverts. A word element is validated when it is read. Probes: an inner
  offset out of range, an inner length out of range, a dirty `uint8` element
  and a struct member offset out of range are all accepted until the element
  is read, then revert with empty data; a relative offset of `-32` is
  accepted and read (`calldata_array_length_v2.sol` relies on it).
* **Copying calldata to memory** (`uint256[][] memory m = x;`) re-decodes with
  the memory rules: the probe with an inner offset of `-32` reverts on the
  copy although every element read succeeds.
* Every decoder failure is `revert(0, 0)`: empty data. Trailing calldata is
  ignored.

### The typed model

`Solidity/Semantics/AbiEntry.lean` (core, no imports) states this decoder over
typed shapes and values:

* `Shape` (words of a `Kind`, `bytes`, `T[]`, `T[n]`, tuples) and the
  intrinsically typed `Val : Shape → Type` with length-indexed `Seq e n` and
  member-indexed `Vals ms`. A `Word k` carries its validity proof. There is no
  untyped value layer.
* `mdec`/`mseq`/`melem`/`mmembers`: the eager memory decoder, in solc's order,
  with allocation tracked against an upper bound `free` on the initial free
  memory pointer (the adapter uses `2^32`; solc starts at `0x80`). An
  allocation that may pass `2^64 - 1` yields `Fail.panic`, which is never
  certified (panic production belongs to lane-soundness).
* `cref`: the entry checks of a calldata parameter. `cval`/`cseq`/`celem`/
  `cmembers` with `tailRef` (`access_calldata_tail`): every lazy access, with
  EVM `sub`, `slt` and modulo-`2^256` addresses.
* `entry`: exactly the checks before a body (head, then each parameter).
  `verdict`: `revert`, `run vs` or `blocked reason`. `encodeArgs` is the
  canonical encoding (heads, then tails).

Theorems (`Solidity/Semantics/AbiEntryProofs.lean`, pinned with
`#guard_msgs in #print axioms` and in `TrustAudit.lean`):

* `mdec_cval` (via `mdec_cval_all`, a joint induction over the eight mutual
  readers): if the eager decoder accepts a value at `p`, the lazy reads of the
  same bytes accept it with the same typed value, for calldata below `2^64`
  bytes. `tailRef_of_mdec`, `mdec_bounds`, `tailFits_of` and `regionFits_of`
  are the arithmetic: unsigned offsets below `2^64` are positive signed words
  and no address wraps.
* `eager_cref`: if a calldata parameter decodes eagerly to `v`, solc's entry
  checks for it pass and the lazy value of the resulting reference is `v`. So
  the lazy decoder never fails earlier than the eager one and never observes
  another value.
* `verdict_revert_iff`: a certified revert is exactly an `entry` failure (the
  model's checks before a body); the replay reports it before the body, with
  empty data.
* `verdict_run_entry`: a body runs only after every entry check passed.

The first two theorems are proofs about the model; the last two unfold
`verdict`. That `entry`, `mdec` and `cval` are solc's decoder is evidence, not
proof: the Yul citations above, the pinned probes and an independent
differential fuzz (below, "Review"). No theorem covers the `readsOnly`
admission; its argument is the syntactic one stated with it.

`Solidity/Semantics/AbiEntryChecks.lean` has 40 kernel-evaluated controls
(`decide`, `decide +kernel`) over probe and fixture vectors: positive
(canonical, overlapping, out-of-order, trailing data, unpadded `bytes`, dirty
padding, a lazy-only layout for a read-only parameter) with the exact
canonical bytes the body receives, negative (each entry check, eager element
checks, the first failing parameter deciding) and the named refusals.
`tests/upstream/AbiEntryReplay.lean` replays the same cases through the
upstream `replay` (counters check once-only bodies and rollback), including a
struct with a dynamic member (out-of-order and head-overlapping member tails,
calldata and memory); it and the
changed `tests/upstream/Replay.lean` run from `scripts/test-solidity.test.mjs`.

### Admission (`Solidity/Tools/UpstreamEntry.lean`)

For a v2 entry (not a constructor) whose parameters all have typed shapes and
no nominal enum or function type, the replay decides on the actual calldata,
selector included (`UpstreamEntry.plan`, `AbiEntry.verdict`):

| Decision | Replay |
|---|---|
| `entry` fails with `revert` | the source call is still built (its own refusals apply); then a failure observation with empty data before the body, state rolled back |
| `entry` passes; every calldata parameter decodes eagerly | the body runs on the decoded values, handed to the existing typed decoder as their canonical encoding; the existing re-encode check runs on those bytes as a cross-check (`generated decoder disagrees with the typed entry decoder: …` if it ever failed) |
| a calldata layout only lazy reads accept, for a parameter the body reads only through complete index paths and `.length` (`readsOnly`) | the body runs on the lazily read value |
| the same layout for any other body | blocked: `calldata layout accepted by lazy access but rejected by an eager copy needs calldata references in the source semantics` |
| a calldata element that fails only when read | blocked: `calldata element fails only on access: needs access-time calldata semantics` |
| a possible `Panic(0x41)` | blocked: `possible Panic(0x41) allocation failure in memory decoding` |
| decoded arguments more than four times the calldata (plus 4096 bytes) | blocked: `decoded arguments exceed four times the calldata: gas is outside the model` (overlapping tails can make solc run out of gas) |
| a byte above 255, calldata of `2^64` bytes or more, exhausted decoder fuel | blocked by name (`invalid calldata byte`, `calldata of 2^64 bytes or more`, `ABI decoder fuel exhausted`, `calldata element validation exhausted fuel`) |
| ABI coder v1, constructors, function parameters, nested enums or an enum parameter without its declared bound, all-primitive signatures without an enum parameter | unchanged (the M3 gate, or the primitive path) |
| a top-level enum parameter of a v2 entry (raw vector) | decoded at its declared cardinality (`Kind.enumBelow`); see the enum item at the end |

`readsOnly` holds when the declaration has no modifiers, the parameter's shape
is arrays/`bytes` down to words (no tuple), and every occurrence of its name
in the body is either a complete read `x[i]…[j]` of a word or the `.length` of
a shorter path (index expressions checked in turn). Each such read is one
lazy access in solc (`calldata_array_index_access`, `access_calldata_tail`,
the word validator), which `cval` defines; full lazy validation succeeded, so
none fails, and the body's view of the parameter is the lazy value. Copies,
passing, returning, encoding, slices and aliases mention the name and are
refused.

No input is canonicalized silently: the original calldata stays the reported
observation (`calldataBytes`), and `msg.data` and assembly keep their existing
refusals, so a body cannot read raw calldata. A body that could read
`msg.data` would see the original bytes; the adapter does not admit one.

### Fixture results

Per-fixture before/after evidence, with complete ordered observations, report
hashes and output directories: `tests/upstream/cf1-abi-entry-results.json`
(collected by `scripts/abi-entry-collect.py`). Same compiler, archive, runner
script, timeout and loop fuel before and after; only the model changed. All
42 fixtures: **13 working / 29 blocked before, 21 working / 21 blocked
after** this section's work (21 / 20 / 1 broken after the enum item below);
no fixture regressed, and every one of the 13 kept its verdict.

| Fixture | Before | After | After reason / observations |
|---|---|---|---|
| abicoder/calldataDecoding/array/calldata_array_length_v2.sol | blocked | working | every vector in both pipelines; 34 observations |
| abicoder/calldataDecoding/array/calldata_array_indexing_1d_2d_v2.sol | blocked | working | every vector in both pipelines; 16 observations |
| abicoder/calldataDecoding/array/calldata_nested_array_static_reencode_v2.sol | blocked | blocked | calldata element fails only on access: needs access-time calldata semantics; 6 observations |
| abicoder/validation/array_exceeds_calldatasize_no_revert_string.sol | blocked | working | every vector in both pipelines; 6 observations |
| array/calldata_array_bounds_check_nested_bytes.sol | blocked | working | every vector in both pipelines; 6 observations |
| array/concat/bytes_concat_nested.sol | blocked | working | every vector in both pipelines; 2 observations |
| array/copying/calldata_2d_bytes_to_memory_2.sol | blocked | working | every vector in both pipelines; 4 observations |
| array/copying/nested_array_calldata_to_memory.sol | blocked | working | every vector in both pipelines; 8 observations |
| smoke/bytes_and_strings.sol | blocked | blocked | entry return bridge needs a primitive prefix and one final bytes/string memory result; 6 observations |
| strings/concat/string_concat_nested.sol | blocked | working | every vector in both pipelines; 2 observations |

`calldata_nested_array_static_reencode_v2.sol`: its failing vectors fail inside
`abi.encode(a)` on a calldata element (an access-time failure), so it stays
blocked by name. `bytes_and_strings.sol`: its three noncanonical `e(bytes)`
vectors now agree in both pipelines; the fixture blocks next on `g()`, a
multiple reference return (retained interface, not this lane). The ABI v1
fixtures keep the M3 gate: v1 decoding (cleaning instead of validation) is not
modelled here.

### Review

Read-only, without Lean workers.

* **Skeptic** (model against solc): ported `verdict`, `encodeArgs`, `mdec`,
  `cref` and `cval` to JavaScript and fuzzed them against the pinned compiler
  on the EVM, about 10,400 vectors over 14 shapes in calldata and memory
  (one run in all four configurations), each function returning
  `keccak256(abi.encode(params))`: **0 mismatches**; every verdict class was
  exercised. Confirmed one gap: overlapping tails can decode to megabytes, and
  solc runs out of gas where the model would run the body. Fixed: the
  4×-calldata refusal. Also fixed: stale theorem names in the proofs' module
  docstring, a wrong `Verdict.kind` docstring, unregistered modules.
* **Finder** (integration): no soundness defect in the admission. Fixed: bytes
  above 255 were wrapped on the new path (now `invalid calldata byte`); the
  revert path skipped the source call's own refusals (now built first);
  `AbiEntryReplay.lean` was not run (now in `scripts/test-solidity.test.mjs`);
  the probe script did not assert fixture expectations (now it does); this
  section's admission table and theorem wording (made to match the code).
  Recorded, not changed: calldata slices of dynamic elements copied to memory
  (`#sliceCopy`) predate this lane and are not re-probed here.

### Validation

* Lean: `lean_diagnostic_messages` clean on every touched Lean file; no
  `sorry`, axiom, `native_decide`, `implemented_by` or heartbeat change. The
  four headline theorems are pinned with `#guard_msgs in #print axioms`
  (`mdec_cval`, `eager_cref`: `propext, Classical.choice, Quot.sound`;
  `verdict_revert_iff`, `verdict_run_entry`: `propext`) and registered in
  `TrustAudit.lean` ("trust: 4 ABI entry-decoding theorems use only the
  standard axioms").
* `./run-lean.sh`: the default target builds (1021 jobs, 17m49s wall for the
  whole script on 4 cores, warm). `SolkeyTestSuite` stops on the known
  `TestSuite.Derived17` OOM (exit 137, baseline); `check-solkey.sh` run
  separately reports the baseline 37 mismatches. On the base, the same script
  had the unchanged `Examples/Tactics/OpenLoops.lean` killed by OOM once
  (65m52s); it built here.
* Node: `solidity-upstream.test.mjs` 25/25, `check-abi-vectors.mjs` 31 vectors
  and 5 rejections, `abi-entry-probe.mjs --fixtures --probes` pass, the new
  `test-solidity.test.mjs` entry passes; `check-g07.mjs`: trust, layers
  (183 core modules, 0 reach the elaborator), orphans (1036, 0 orphaned),
  noncircular, grammar and control pins pass; its two "new" items are the
  baseline axiom-pin drift (unchanged 1209 pins, 407 unrecorded) and
  `check-doc-paths` 48 missing (46 baselined + 2), byte-identical to the base
  checkout's output. `check-automatic --strict`: 491 / 61 / 11 refuted / 0
  pending.

### Limitations

* ABI coder v1 entries, constructor arguments, function-valued and
  nominal-enum parameters keep the M3 gate.
* Access-time failures (an element that fails only when read) and lazy-only
  layouts read other than through complete index paths stay refused: they
  need calldata references in the source semantics (lane-soundness).
* `Panic(0x41)` is never certified; gas is not modelled (the 4× bound).
* No theorem connects `entry`/`cval` to solc's bytecode: that is the
  evidence above, and the specification for the compiled-decoder lanes.

### Backfill: ABI identity of inherited renamed function values (2026-11-01)

Taken after the CF1 + CF2 integration (`099bfbe1`, merged into this branch
without rebase). Reproduction first: `tests/abi-0.8.38/InheritedSelectors.sol`
covers an overridden `f`/`g`, an inherited `h` (which the importer renames to
`solcFunction31`), inherited overloads `k(uint256)`/`k(bool)` (both renamed),
`Base.f.selector`, `this.f.selector`, `this.h.selector`, `abi.encodeCall` of
`this.g` and `this.h`, external function values of `f` and `h` (their
`.selector`, and `abi.encode` of the value), `super.f` and calls through
external function values. On the merged master every admitted case already
returns the source declaration's selector and encoding; pinned solc agrees in
all four configurations (`--inherited` asserts each word). The "Left" entry
was stale: it predates source-identity selectors (`declarationSelector`,
`solcMetadataSelector*`). The only refusal is the call through an external
function value (`solidity.functionDispatch: this call needs a finite set of
typed dispatch targets`), and it refuses the derived `this.f` the same way,
so it is the function-value dispatch boundary (lane CF2's area), not an
identity gap. Nothing in `Syntax/Elab/{Values,Stmt,Arms,Context}.lean` or any
other shared file was edited for this item; the change is the fixture, its
pinned regression module (registered in `Solidity.lean`, one module-map row)
and the probe option. Not covered: selectors or values of the renamed
inherited overloads `k` (an overloaded member has no value without a call
context in solc) and `Base.h.selector`. The G03 ledger's `abiEncodeCall`
row took this item from a fixed string in `scripts/roadmap-g03-ledger.py`;
the integration removed it there and regenerated the ledger.

### Next item: nominal enum cardinalities at external entry (2026-11-01)

solc's v2 entry decoder validates an enum parameter against its declared
member count (`validator_revert_t_enum_*`: an empty revert unless the word is
below `n`); pinned by the `EnumEntry` probes (in range, one past the last
member, dirty high bits, an enum before a calldata or memory array; all four
configurations). The import row already carries the declared bound of each
top-level enum parameter (`paramRanges`, `(x, 0, largest member)`, from the
source declaration's `enumBounds`), and the scalar path already enforced it
(`inRanges`). Two refusals remained: the runner refused every enum in the ABI
metadata, and raw (noncanonical-word) vectors refused any nominal range.

* `Kind.enumBelow n` (`Semantics/AbiEntry.lean`): a word valid below `n`. The
  agreement theorems are generic in `Kind.valid` and are unchanged; six
  kernel controls cover enum values alone and before calldata/memory arrays.
* `UpstreamEntry.params`/`plan` take the declared bound per parameter
  position: a top-level enum parameter becomes `.word (.enumBelow (hi + 1))`.
  An enum parameter without its bound, and every enum nested in an array, a
  static array or a struct, stays outside (`legacy`, then the existing
  `nominal enum ABI range needs a declaration adapter`).
* `Tools/Upstream.lean`: a raw vector whose only nominal ranges are top-level
  parameter ranges goes through the typed plan (also for all-primitive
  signatures); constructors, ABI coder v1 and element ranges keep the
  refusal. `ABI.validate` reads exactly those enum parameters (and returns
  marked `#enum`) at their ABI type `uint8`; nested enums still throw.
* `scripts/solidity-upstream.mjs`: `checkAbiMetadata` admits a top-level enum
  parameter or return of ABI type `uint8`; nested enums are refused as before
  (`solidity-upstream.test.mjs` pins both).
* `tests/upstream/EnumAbiRanges.lean`: its raw-vector control, which pinned
  the old refusal, now pins the typed outcome in both pipelines (in range runs,
  `2` and `2^256 - 1` revert before the body, wrong expectations are broken).

Fixtures (`tests/upstream/cf1-abi-entry-results.json`, final model, all 42
rerun): **21 working / 20 blocked / 1 broken**. The 21 working are those
above, unchanged. `enum_with_256_members.sol` moved from the runner's enum
metadata refusal (blocked) to an explicit frontend import gap (broken, no
runtime mismatch): its `decodeEnum` uses `abi.decode` of an enum
("ABI decoding of enum values requires nominal cardinality checks"), which
lane-soundness owns; its 256 members also make the enum range byte-wide.
`enum_v1.sol` and `enum_v2.sol` read the enum through inline assembly and
stay blocked on that. ABI coder v1 keeps every enum refused: the review
observed that v1 legacy masks an enum word to `uint8` at entry and panics
(`0x21`) only on use, unlike v2.

Review (one read-only reviewer acting as finder and skeptic, no Lean worker;
it reran `--inherited --probes` and probed v1 on the EVM): confirmed and fixed
the v1 leak above (the runner had admitted v1 enums, which the scalar path
would have range-checked at entry, turning e.g. `types/mapping_enum_key_v1.sol`
into a wrong broken verdict); confirmed that `paramRanges` holds the largest
member (`enumBounds = members - 1`, so `enumBelow (hi + 1)` is the
cardinality), that nested enums, constructors, missing bounds and position
mismatches stay refused, and the backfill's pinned selectors on the EVM.
Fixed doc gaps (stale M3/admission lines, this section). Recorded: a function
whose only enum is a return still meets the refusal on the raw path (safe),
and `inRanges` treats an argument-count mismatch as a revert (pre-existing).

### Validation after the CF1 + CF2 merge, the backfill and the enum item

* `./run-lean.sh` (64m52s): default target "Build completed successfully
  (1041 jobs)"; `SolkeyTestSuite` "Build completed successfully (286 jobs)"
  (the `Derived17` OOM did not recur); `check-solkey.sh` the baseline 37
  mismatches.
* Lean server, clean: `AbiEntry`, `AbiEntryProofs` (axiom pins),
  `AbiEntryChecks`, `UpstreamEntry`, `Upstream`,
  `Examples/Tactics/InheritedSelectorsImport.lean`, `TrustAudit.lean`, and
  `tests/upstream/{AbiEntryReplay,Replay,EnumAbiRanges,EnumBounds,EnumErrorControls,CompoundAbiShape}.lean`.
* Node: `solidity-upstream.test.mjs` 25/25; `abi-entry-probe.mjs --fixtures
  --probes --inherited` pass; `check-abi-vectors.mjs` 31 + 5;
  `test-solidity.test.mjs` "typed ABI entry decoding" passes, while "canonical
  nominal ABI matching preserves enum input ranges" cannot run here: it first
  compiles with the solkey-pinned 0.8.34 compiler, absent from this container
  (its Lean half, `EnumAbiRanges.lean`, is clean above); `check-g07`: trust,
  layers (184 core, 0 reach the elaborator), orphans (1078, 0 orphaned),
  noncircular, grammar, control pins pass, its two "new" items are the
  baseline axiom-pin drift and `check-doc-paths` 48 (46 + 2);
  `check-automatic --strict` 491 / 61 / 11 refuted / 0 pending.


Integration review (round 2, 2026-11-01; read-only finder and skeptic on the
merge with lane CF2): enum bounds are `members - 1` from the declaration
metadata, and ABI v1, constructors, nested enums and missing bounds stay
refused on the raw-calldata path. On the scalar `args` path a v2 constructor
or return with a top-level enum is now range-checked (`inRanges`) rather than
refused, which is correct for v2. Open: no Lean control pins the raw path's
refusals (constructor, `canonicalOnly`, element ranges) since the
`EnumAbiRanges.lean` raw control moved to working/broken; the "v1 masks enum
words" rationale is recorded from the EVM run but was not rechecked here (v1
stays refused either way); `cf1-abi-entry-results.json` was generated before
CF2 and was not regenerated on the combined tree.

### Lane FU1 (followup-20261101): enum decoding and the raw-path controls

* **`abi.decode` of a top-level enum** (`enum_with_256_members.sol`'s
  frontend gap, lane-soundness checkpoint 4): `abiDecodeWith`
  (`Syntax/Elab/Lower.lean`) reads the word as a `uint8` (31 zero high bytes)
  and `require`s it below the member count, then converts (`E(w)`): ABI coder
  v2's `validator_revert_t_enum_*`, an empty revert for every other word
  (including `256`). The import (`SolcJson/Body.lean`) admits an `Identifier`
  or member access naming an enum definition as a component, at its native
  enum name; an enum inside an array or a struct keeps "ABI decoding of enum
  values requires nominal cardinality checks", and ABI v1 `abi.decode` is
  refused at admission (`solidity.abiCoderV1`). Pins: `EnumDecode` in
  `Examples/Tactics/AbiFeatures.lean` (`2` decodes, `3` and `256` revert, an
  `(E, uint)` tuple). Inside `sol{}` (not the import) `AbiTy.of` still ignores
  `#enum` rows for nested enums (pre-existing; recorded).
* **Top-level enums at the replay** (`ImportRow.retEnums`,
  `ImportRow.paramEnums`: positions of the source declaration's enum-typed
  returns and parameters, since a return may be unnamed): a v2 entry's enum
  return is read at its ABI type `uint8` even when no parameter carries a
  nominal range (the case CF1 recorded as "a function whose only enum is a
  return still meets the refusal"), and a declared enum parameter is nominal
  even when its range is a byte range: an enum of 256 members (`0..255`)
  previously counted as a plain `uint8` and would have taken the legacy
  path, which reads the word without validating it (`256` decoded, where
  solc reverts; found by the rerun below before it was fixed). It now goes
  through the typed entry decoder (`enumBelow 256`). Constructors and
  `canonicalOnly` vectors keep the refusal (now also for 256-member enums).
  Result: `enums/enum_with_256_members.sol` is **working** in both
  pipelines (`getMinMax`, `intToEnum`, `enumToInt` with `256` failing,
  `decodeEnum` with `256` failing).
* **Raw-path controls** (`tests/upstream/EnumAbiRanges.lean`, integration
  review round 2): a constructor's nominal range and a `canonicalOnly`
  vector keep "nominal enum ABI range needs a declaration adapter" in both
  pipelines. An element range is not pinned: no fixture has an enum-array
  parameter beside only admitted functions (`EnumInputRefusal` stops at its
  other functions' import gaps).
* **`calldata_nested_array_static_reencode_v2.sol`** stays blocked: its
  failing vectors fail inside `abi.encode(a)` on a calldata element, which
  needs access-time calldata reads in the elaborated model (not started).

Fixtures (`tests/upstream/cf1-abi-entry-results.json`, all 42 rerun on lane
FU1 with `scripts/abi-entry-fixtures.sh SOLJSON fu1final`, collected with
`abi-entry-collect.py --keep-before`, which keeps CF1's before column):
**22 working / 20 blocked / 0 broken** (CF1: 21 / 20 / 1). The only change
is `enum_with_256_members.sol`, broken (frontend gap) → working; every other
fixture keeps its status and reason.

Review (lane FU1; read-only finder and skeptic on the enum decode and the
raw-path controls, a second skeptic on the replay change, no Lean worker):
confirmed and fixed: the control comment called `canonicalOnly` "ABI coder
v1" on v2 fixtures (reworded); the element-range control used a fixture that
stops at other import gaps (dropped, recorded above); a declared enum
parameter whose position could not be matched (import and model parameter
lists of different lengths, not reachable today) would have decoded as a
plain word: now refused. Recorded, not changed: a 256-member enum carried in
a struct (`uint8` carrier) beside a parameter the typed entry plan cannot
shape (an external function type) is now refused where the legacy path
accepted it (fail-closed); enum returns of `canonicalOnly` vectors stay
refused although v1 encodes them alike; public enum getters keep
`retEnums = []` and stay refused.

### Lane FU2-D (fu2-20261102): enums nested in ABI types

* **`abi.decode` of an array of enums in `sol{}`** (`(E[])`, `(E[k])`,
  nested arrays). Before, `sol{}` refused it with "abi.decode at E[]: a value
  type, a byte string, an array or a struct" (`abiDecodeTy?` dropped every
  flat type and `decodeKind?` knows no enum element), so nothing decoded
  unchecked. Now `abiDecodeTy?` routes an array whose element is a contract
  enum to the nested decoder, and `abiReadGen`'s value case, at a declared
  enum element, reads the word as a `uint8` and `require`s it below the
  member count before `E(w)`: solc's `validator_revert_t_enum_*`, an empty
  revert. Pinned by `EnumArrayDecode` in `Examples/Tactics/AbiFeatures.lean`
  (`#run`, five vectors) against the EVM observations below.
* **The import keeps the refusal** — superseded by the second pass below.
* **Public enum getters** (`SolcJson/Contract.lean`): a synthesized getter
  whose value, past its mapping keys and array indexes, is an enum gets
  `retEnums := [0]`, so the replay reads its return at the ABI type `uint8`,
  as a source function's top-level enum return.
* **EVM observations** (`scripts/enum-abi-probe.mjs`, solc 0.8.38 at the
  repository's pinned SHA-256, `@ethereumjs/vm` 10.1.3, four configurations,
  all agreeing; `tests/abi-0.8.38/EnumArrays.{sol,vectors.json}`):
  `decodeArr(2, 1)` returns 21, `decodeArr(0, 3)` and `decodeArr(256, 0)`
  revert with empty data; `decodeFixed(1, 2)` returns 12, `decodeFixed(3, 0)`
  reverts empty; at the external entry `entryArr([2, 0])` returns 202,
  `entryArr([2, 3])` and a raw element word `256` revert empty;
  `entryStruct((2, 5))` returns 2005, `entryStruct((3, 5))` reverts empty;
  the getter `stored()` returns 0, then 2 after `setStored(2)`, and still 2
  after `setStored(3)` reverted with `Panic(0x21)`.

#### Second pass (coordinator follow-up, same lane)

* **A carrier-preserving decode marker.** The import declares every
  enum-typed local at a carrier (`uint`, `uint8` for an enum a struct uses),
  so `sol{}`'s nominal `E[]` cannot be its target. `abi.decode` components
  with nested enums are now printed as `solcEnumBelow(T, "k", n, …)`
  (`abiEnumBelowName`, `Syntax/Elab/Values.lean`): `T` at its carriers,
  each enum position `k` (`""` the value, `k[]` an element, `k.f` a member,
  at any depth: `abiEnumPositions`, `SolcJson/Body.lean`) with its member
  count `n`. `abiTyExpr?` reads through it (shapes and types are `T`'s), and
  `abiReadGen` decodes the word at its carrier kind and `require`s it below
  `n` before the element or member is stored: solc's validator, an empty
  revert. Enum arrays and structs with enum members, nested, are admitted.
* **The external entry.** Import rows carry `paramEnumPositions` (the same
  keys, per parameter); the replay (`Tools/Upstream.lean`) spells those
  positions `uint8` in the ABI check (`ABI.shapeEnum`) and the typed entry
  decoder reads them as `Kind.enumBelow n` words (`UpstreamEntry.shapeAt`),
  so an out-of-range element or member is an empty revert before the body.
  The import's "an ABI composite parameter requires recursive enum
  cardinality checks" refusal now applies only where a position is not
  readable (a mapping, an unknown declaration).
* **Getters.** An enum-valued public getter is admitted at its carrier
  (`SolcJson/Getters.lean`, `getterValueType`) with `retEnums := [0]`. Its
  enum mapping keys keep the membership guard of the getter body
  (`getterWalk`'s `enumSize`) and get no `paramEnums`: the review found that
  a nominal row blocks the ABI v1 replay (`canonicalOnly`), which such a
  getter passes today through the legacy path.
* **No position is dropped.** Every listed position must name a word of the
  decoded type (`AbiTy.valKeys`): `abiDecodeWith` refuses "an enum position
  outside the type", and the replay's `UpstreamEntry.params` falls back to the
  refused legacy path, so a key mismatch (a renamed member) fails closed.
* **Pins changed with the boundary**: `tests/upstream/RemainingDeclarations.lean`
  (`EnumDecodeRefusal.decode` and `EnumInputRefusal`'s `direct`, `records`,
  `nested` now elaborate, the latter with `paramEnumPositions`),
  `tests/upstream/Entrypoints.lean` (the enum getter is admitted with
  `retEnums = [0]`), `scripts/test-solidity.test.mjs` (EnumArrayDecode).
* **Replay control** (`tests/upstream/EnumArrays.lean`, checked through the
  Lean server): `tests/abi-0.8.38/EnumArrays.sol` imported with
  `testing entrypoints` from its 0.8.38 AST (`EnumArrays.ast.json`), each
  sequence of `EnumArrays.vectors.json` replayed on its raw calldata against
  the EVM's bytes (return or revert data, `Panic(0x21)` included): all five
  `working` (enum arrays in `abi.decode`, `E[]` and an enum struct member at
  the entry with their reverts, the getter before and after a failed
  `setStored(3)`); with every expected outcome flipped, all five `broken`
  (pinned, `#guard_msgs`). This is the lane's own results file; the CF1
  fixture file was not edited.
* **Not done**: proof obligations do not yet assume the nested enum ranges
  at entry (`Problem.callPre` reads `paramRanges` and `elemRanges` only), so
  a claim that needs them stays open (incomplete, not unsound); the replay
  control covers `E[]`, `E[2]`, a flat struct and a getter, not nested
  structs, arrays of structs or `E[][]` (the import admits them; the key
  guard above fails closed on a mismatch); the CF1 fixture set
  (`tests/upstream/cf1-abi-entry-results.json`, `scripts/abi-entry-probe.mjs
  --fixtures`) was not rerun, since it needs the upstream snapshot
  (`.lake/upstream/solidity`); `sol{}` written by hand still reads a struct's
  enum member as a plain `uint` (the struct table has no enum identity), so a
  hand-written `abi.decode(b, (S))` there checks only the carrier's range.
* **Reviews and gates of the second pass.** Read-only finder and skeptic:
  confirmed and fixed four pins still asserting the old refusals (listed
  above), the ABI v1 getter regression (enum-key `paramEnums` dropped), and
  the missing key-consumption guard (`AbiTy.valKeys`); the skeptic confirmed
  the control's encoding, that the replay compares return and revert bytes,
  and the carrier-width equivalence (`require(w < n)` after a `uint8` or a
  full-word read is solc's `lt(value, n)`); its suggestion to corrupt one
  return byte in a further negative control is not done. Recorded: obligations
  lack the nested ranges (above). Gates: `./run-lean.sh` default 1041 jobs;
  `EnumArrays.lean`, `RemainingDeclarations.lean`, `Entrypoints.lean`,
  `EnumAbiRanges.lean` clean through the Lean server; `enum-abi-probe.mjs`
  all vectors agree; `check-g07` at its baselines; `check-automatic --strict`
  0 pending; ledger regenerated.

### Lane FU2-C (fu2-20261102): access-time calldata reads

Owner: lane FU2-C (`cloud/fu2-20261102/fu2-calldata-access`). Base
`84a2a4be`. CF1 refused, by name, every input whose calldata parameter has an
element that fails only when read ("calldata element fails only on access").
This item models those reads in the layer the upstream replay runs.

**Evidence first** (`tests/abi-0.8.38/AccessEntry.sol`, 20 vectors in
`AccessEntry.vectors.json`, `scripts/abi-entry-probe.mjs --access`; pinned
solc, legacy and via-IR, optimizer off and on, all agree):

* `abi.encode(x)` / `abi.encodePacked(x[0])` of calldata go through the lazy
  accessors: a relative offset of `-32` is accepted and encoded, an inner
  offset or length out of range, an inner length of `2^64` (not a panic), a
  dirty `uint8` (also nested) and a short `uint256[][3]` all revert with
  empty data.
* A read is path dependent: `encIf` returns 7 when it does not reach the
  encoding, and reverts when it does; `encAt(x, i)` encodes `x[0]` and
  reverts on `x[1]`; `require(i != 0, "m")` before the encoding reverts with
  `Error("m")` first.
* A copy to memory decodes with the eager rules: `uint256[][] memory m = x`
  with an inner length of `2^64` is `Panic(0x41)`; `uint256[] memory m = x[0]`
  reaches `x[0]` lazily (a `-32` offset is read) and copies its words.

**Model** (`Solidity/Semantics/AbiAccess.lean`, core, imports only
`AbiEntry`):

* `cpart`/`cseqP`/`celemP`/`cmembersP`: CF1's lazy reader `cval` with the
  same checks, order and fuel, recording each failing node by its access
  path (element and member indices) and putting a substitute value of its
  shape there (`Shape.dflt?`: zero words, empty arrays) instead of stopping.
* `cat`/`catSeq`/`catElem`/`catMembers`: one access along a path, as solc
  performs `x[i]…[j]` (index access, `access_calldata_tail`, the word
  validator), with `Fail.panic` for an index out of range.
* `bodyValuesA`/`verdictA`: CF1's `bodyValues`/`verdict`, except that a
  calldata parameter the body reads only by admitted accesses (`acc k`)
  whose eager copy fails takes `cpart`'s value and paths.

Theorems (all kernel-checked, pinned with `#guard_msgs in #print axioms`
and in `TrustAudit.lean`):

* `cpart_agree`: `cpart` and `cval` agree on every reference: no recorded
  path and `cval`'s value, some path and `cval`'s empty revert, or both fail.
  Corollaries `cval_of_cpart`, `cval_revert_of_cpart`, and the converse
  `cpart_of_cval`. With the probes above this is the encoding case: an
  `abi.encode` of the parameter reverts exactly when a path is recorded.
* `cat_cpart`: for a reference `cpart` reads, an access along any path
  reverts with empty data exactly when a recorded path is a prefix of it.
* `verdictA_off`: with no access-time parameter, `verdictA` is CF1's
  `verdict` (conservative extension); `verdictA_revert_iff`,
  `verdictA_run_entry` as CF1's.

`Solidity/Semantics/AbiAccessChecks.lean` has 20 kernel controls (both
outcomes: covered accesses revert, others read) on the probe vectors and on
`calldata_nested_array_static_reencode_v2.sol`'s.

**Admission and replay** (`Tools/UpstreamEntry.lean`, `Tools/Upstream.lean`):
a calldata parameter is read at access time when the declaration has no
modifiers, its shape has no tuple, and every mention of it in the body is a
complete word read `x[i]…[j]`, the `.length` of a shorter path (index
expressions without calls, writes or mentions of `x`), or an argument `x` of
`abi.encode`/`abi.encodePacked` (also as a statement); loop annotations may
not mention it. The replay then runs the declaration with its reads guarded
(`guardDecl`), in that call's elaboration scope only: the index at depth `m`
becomes `accessGuard__calldata(ok, i)` (`require(ok); r = i;`), `ok` saying
no recorded path of length `m` equals the indices so far (by `cat_cpart`,
when solc's access at that level does not revert); an encoding of `x` with a
recorded path gains a last argument `accessGuard__calldata(false, 0)`, which
reverts after the other arguments are evaluated, where solc's encoder
reverts. Each index level is guarded where solc checks it, so an earlier
level's failure precedes a later index's evaluation. Copies, aliases,
passing, slices, returns, member paths and modifiers keep CF1's refusals;
the guard name is reserved; constructors and the typed multi-return adapter
refuse guards by name.

**A local of the parameter's name** (legal in solc, a shadowing warning) is
not admitted: `accessOnly` refuses a body that declares or binds the name
anywhere, since the guards are placed by name (review finding, below).

**Changed controls.** CF1's replay controls that pinned "fails only on
access" for bodies that never read the failing element now run, as solc does
(`LazyEntry` probes "not accessed"): `outer`, `narrow` in
`tests/upstream/AbiEntryReplay.lean`, `unused(uint8[])` in
`tests/upstream/Replay.lean` (an expected failure there is now `broken`).
New replay controls: indexed and length reads of a failing element (revert,
counter rolled back) and of the others (read); `abi.encode` of a failing,
a lazy-only and a `2^64`-length array; `encIf` both ways; the fixture's
`f(uint256[][3])`; the operand-order split `x[0] + 1 / k` (legacy
`Panic(0x12)`, via-IR empty revert, as pinned solc); a shadowing local
(refused). Copies keep the lazy-only refusal.

**Fixture results** (`tests/upstream/cf1-abi-entry-results.json`, all 42
rerun with `scripts/abi-entry-fixtures.sh SOLJSON fu2c`, collected with
`abi-entry-collect.py --keep-before`): **23 working / 19 blocked** (FU1:
22 / 20). The only change: `calldata_nested_array_static_reencode_v2.sol`
blocked → working in both pipelines. Of item 2's rows, every calldata row is
working except `smoke/bytes_and_strings.sol`, still blocked on "entry return
bridge needs a primitive prefix and one final bytes/string memory result"
(`g()` returns two references: the retained typed return adapter, not
calldata); the memory rows were already working.

**974dd1de reapplied** (calldata parameters as slice origins of obligation
bodies, `Frontend/Import.lean`), with the error-encoding evidence recorded in
`docs/assurance.md` (test 31) and pinned in
`tests/upstream/AggregateErrorControls.lean`.

**Review** (read-only finder and skeptic, no Lean server). Skeptic: about
110 vectors over 8 probe contracts against pinned solc in all four
configurations (dirty `uint8`/`int16`/`bool`/`bytes3`/`address` at every
depth, `bytes[]`, fixed arrays of dynamic arrays, negative and huge offsets,
`2^64 - 1` lengths, encoder ordering after other arguments, level-by-level
index order, short-circuit, ternary, `require` with error arguments,
assignments): no counterexample. It found the pipeline split of binary
operand order (legacy right-first, via-IR left-first) unexercised: added the
`order` probe (`expectByPipeline`) and replay controls in both orders.
Finder: no unsound admission; confirmed and fixed: the aggregate pins lacked
a recorded solc probe (now `--aggregate`), stale docs (`assurance.md`, this
section, `UpstreamEntry`'s docstring), `abi.encodePacked(x)` of a whole
array unprobed (`encPw`), nested lazy-only layouts unprobed (`enc8nL`,
`encBL`, with kernel controls). Both raised parameter shadowing as a doubt;
solc accepts a shadowing local, so the refusal above was added with a
control. Recorded, not changed: the guard condition grows with the number of
failing paths (one conjunct each); a narrow index compared with a recorded
index above its range may not elaborate (blocked, not unsound); several
access-time parameters at once and guards under `&&`/`?:` have no replay
vector (the skeptic's EVM probes cover the solc side).

**Validation** (lane head before this record):

* `./run-lean.sh` (43m50s wall, warm after a container restart interrupted
  the first run, so no clean before/after timing): default target "Build
  completed successfully (1043 jobs)", `SolkeyTestSuite` "Build completed
  successfully (286 jobs)", `check-solkey.sh` the baseline 37 mismatches.
  No core module changed (`AbiAccess` is a new leaf importing only
  `AbiEntry`); `Frontend/Import.lean` rebuilds its importers.
* Lean server, clean: `AbiAccess`, `AbiAccessChecks`, `UpstreamEntry`,
  `Upstream`, `tests/upstream/{AbiEntryReplay,Replay,AggregateErrorControls,AggregateErrorBoundary}.lean`.
  No `sorry`, axiom, `native_decide`, `implemented_by` or heartbeat change;
  seven headline theorems pinned and registered in `TrustAudit.lean`.
* Node: `solidity-upstream.test.mjs` 25/25, `finite-dispatch.test.mjs`
  34/34, `abi-entry-probe.mjs --probes --access --aggregate` pass;
  `check-automatic --strict` 491 / 61 / 11 refuted / 0 pending; `check-g07`
  at its baselines (axiom-pin drift, `check-doc-paths` 48 = 46 + 2); G03
  ledger regenerated (line numbers of `Import.lean`).

**Limitations.** Copies of a failing calldata parameter to memory, aliases,
passing it, slices, struct members and modifiers keep the refusal (copies
decode with the eager rules, `Panic(0x41)` included). `Panic(0x32)` and the
other panics are produced by the existing model, not certified here. The
agreement theorems are about the model; that it is solc's decoder rests on
the probes. Gas is outside the model (CF1's 4× bound, on the substituted
value).

### Lane FU2-C, item 4 and backfill

**Item 4 (test 31 `sliceRead`)**: the view index lowering checks the view's
bound where solc does (`#sliceIndex`, `Syntax/Elab/Arms.lean`; record and
evidence in `docs/assurance.md`, test 31). `slicePast` now proves;
`sliceRead` and `sliceOfSlice` stay pending on closer cost (valid at ten
times the heartbeats; not committed). This is a lowering change, not a new
rule: no rule-map row, closer clause or soundness proof was needed, since
the check is an ordinary `require`/`Panic(0x32)` statement.

**Backfill: ABI coder v1 value parameters** (`UpstreamEntry.v1Plan`). v1
cleans a value word instead of validating it; pinned solc, legacy with the
optimizer off and on (`tests/abi-0.8.38/V1Entry.sol`, 14 vectors (trailing data and a lone `address` included),
`scripts/abi-entry-probe.mjs --v1`, whose expectations are an independent
port of the cleanup): `uintN` masked, `intN` sign-extended from its low `N`
bits, `bool` 1 for any nonzero word, `bytesN` its high `N` bytes, `address`
its low 160 bits; calldata shorter than the head is an empty revert;
trailing data ignored. A v1 entry whose parameters are all such values runs
on the cleaned words (the byte-identical cross-check on them); enums (v1
masks them to `uint8`), function values and reference parameters keep the
gate. Replay controls: `tests/upstream/AbiEntryReplay.lean` (`checked_add_v1`
shape, `Panic(0x11)` after cleanup, short calldata, `int8`/`bool` cleanup, a
`uint256[]` parameter gated), `tests/upstream/Replay.lean` (`narrow(uint8)`
256 reads 0; expecting 256 is `broken`).

**Backfill: the runner's scalar adapter** (`scripts/solidity-upstream.mjs`,
`scalarArg`): TestFileParser writes a negative literal as its two's
complement word, which for a 256-bit unsigned type is canonical (`-2` is
`2^256 - 2`); the adapter refused it as noncanonical.
`viaYul/function_entry_checks.sol` now passes `g(uint256,uint256): 1, -2`
and blocks next on `h(), 1 ether -> 0` (a call value in the runtime
expectation, outside this lane).

**Remaining blocked rows and their reasons** (all 42 rerun,
`cf1-abi-entry-results.json`):

| Fixture | Reason | Kind |
|---|---|---|
| `smoke/bytes_and_strings.sol` | entry return bridge needs a primitive prefix and one final bytes/string memory result | retained interface: `g()` returns two references (`EntryReturn`) |
| `abicoder/cleanup/enum_v1.sol` | nominal enum ABI range not adapted | exclusion: v1 masks enum words, nominal range refused for v1 |
| `abicoder/cleanup/enum_v2.sol`, `operators/shifts/shift_right_garbled{,_signed}_v{1,2}.sol`, `userDefinedValueType/{cleanup,cleanup_abicoderv1,parameter}.sol`, `viaYul/unary_operations.sol` | raw ABI replay with physical calldata/memory assembly not adapted | exclusion: inline assembly building raw calldata |
| `viaYul/function_entry_checks.sol` | unsupported runtime expectation: `h(), 1 ether -> 0` | runner: call values in runtime expectations |

### Handoff (withdrawn: closed in FU2-C round 2, see `docs/assurance.md`, test 31)

(History.) Before round 2, test 31's slice rows after FU2-C: `slicePast`
proved; `sliceRead` and `sliceOfSlice` reached `sol_close` with valid leaves
but exceeded its budget.
The cost appears with a calldata view at a nonzero offset read at a
symbolic index through the view's base alias (`#slice$t$view$base := xs`,
`ie := 1 + se`): offset 0, literal indices, or the same reads on the
parameter directly close within budget. Reproduction: import
`tests/solc/Calldata.sol` (`scripts/solc-ast.mjs --source …`), then
`sol_prove; all_goals sol_leaf; all_goals sol_close` on
`Solc.Calldata.sliceRead.problem`. FU2-C did not edit `Calculus/**`.

**Review of item 4 and the backfill** (read-only finder and skeptic, no Lean
server). Skeptic: v1, a differential test against pinned solc (legacy,
optimizer off and on): 547 vector pairs per setting over 47 functions,
each dirty input against the same input with every head word cleaned by
the rule above, comparing success, return data and logs; uses covered
include checked and unchecked arithmetic, shifts by and of dirty words,
`**`, bitwise operations, comparisons, conversions, all encodings and
`keccak256`, packed storage, mapping keys, memory arrays, internal and
external self-calls, events, modifiers with parameters, assembly reading
the parameter, UDVTs (a `bool` UDVT included), `uint248`/`int248`/
`bytes31`: 0 disagreements; a short head reverts, trailing data is ignored.
It confirmed both exclusions: a v1 constructor does not clean at entry
(assembly reads the raw word), and a v1 enum is masked to `uint8` with no
range check. Slices: `t[k]` with `k >= t.length` is `Panic(0x32)` in all
four configurations, after its own index and before any operand the
pipeline evaluates later (legacy right-first, via-IR left-first, as
`Contract.evalOrder`), and a bad slice bound reverts first. No
counterexample. Finder: no code defect (evaluation order, `len` hoisting,
`off + x` overflow, panic/revert choice, ternary/short-circuit placement,
loop conditions, slices of slices, constructors/enums/function types/
contract types/UDVTs/`address payable` in `v1Plan`, the cross-check,
`scalarArg`). Confirmed and fixed: the probe count (now 14 vectors, with a
trailing-data and a lone `address` vector added), the "outcomes unchanged"
wording in `assurance.md` (per mode), `v1Plan`'s docstring (cleanup at
decoding). Recorded, not changed: a zero-parameter v1 entry runs on `[]`
(trailing data dropped; not observable under the `msg.data` refusal); a
slice read directly in a failure-retaining body outside the entry call
would now carry `Panic(0x32)` data (closer to solc; no producer found).

**Fixtures, final** (`tests/upstream/cf1-abi-entry-results.json`, all 42
rerun with `scripts/abi-entry-fixtures.sh SOLJSON fu2c3`, one runner hash,
collected with `abi-entry-collect.py --keep-before`): **30 working / 12
blocked / 0 broken** (FU1: 22 / 20). Changes against FU1: the access-time
fixture and the seven ABI v1 rows blocked → working; `function_entry_checks`
blocked on its next reason. `enums/enum_with_256_members.sol` ended once
with "Lean process ended before checkpoint" while other Lean tests ran on
the same machine; rerun alone into the same directory with the same runner
it is working, as before.

### Lane FU2-C, round 2 (coordinator follow-up)

* **Test 31 slice rows prove** within the default budget: `#sliceIndex`
  reads a literal or `uint256` name index without a copy, and `sliceOpen`
  drops the always-true `len <= len` check of a view to the end; record in
  `docs/assurance.md` (test 31). Lowering only; outcomes unchanged (the
  dropped check holds by construction; nothing is evaluated between the
  view's check and its read, and a later operand's effect captures the
  read first, `captureBefore`; control `sliceK` in
  `tests/upstream/AbiEntryReplay.lean`, both operand orders).
* **`smoke/bytes_and_strings.sol` works** (both pipelines): the entry return
  adapter (`Tools/EntryReturn.lean`, `admitted`, `byteRets`) admits any mix
  of primitive and `bytes`/`string` memory returns, each with its byte
  markers; `serialize` already encoded every return local in order
  (`(string, string)`, `(string, uint, string)`).
* **Fixtures after round 2** (all 42 rerun, `fu2c4`, one runner hash,
  collected with `--keep-before`): **31 working / 11 blocked / 0 broken**;
  the only change from round 1 is `smoke/bytes_and_strings.sol` blocked →
  working. The 11 left are the exclusions in the table above (assembly ×8,
  v1 enum, a call value in `function_entry_checks`).
* **`sliceHashed`** (test 31's last failing row) predates this lane
  (bisected on the base commit) and is recorded with its cause in
  `docs/assurance.md` (test 31): a symbolic slice-copy loop the walk unrolls
  past its budget, reported as a heartbeat error rather than `pending`.
* **Review of round 2** (read-only finder and skeptic). Skeptic, pinned solc
  in four configurations: slice bound checks over 1694 cases × 4 configs
  (`xs[i:]`, `xs[i:j]`, nested views, `bytes`, huge and empty bounds), 0
  mismatches, a view to the end checks only its start; several
  `bytes`/`string` returns in any order, aliased, unassigned or swapped are
  `abi.encode` of the return locals in declaration order. It showed that an
  operand reassigning the index (`t[k] + (k = 5)`) is pipeline-dependent;
  the model captures the read before a later operand's effect
  (`captureBefore`), pinned by the `sliceK` replay control in both orders.
  Finder: no semantic defect; fixed: `EntryReturn` docstrings, stale
  present-tense notes. Recorded, not changed: `intTyOf` defaults a
  non-integer name (a `bytes32` local) to `uint256`, so such an index (which
  solc rejects at compile time) would skip the copy; a literal index above
  `2^256` likewise (also rejected by solc).
