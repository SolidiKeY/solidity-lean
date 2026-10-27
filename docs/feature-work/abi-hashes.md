# ABI, hashes and concatenation

Integration status (2026-10-26): included in the shared checkout. Current
combined validation is tracked in [integration.md](integration.md).
Worker handoff statuses and isolated validation results below are historical;
they neither report the current combined checks nor establish full source support.

## M1: computed recovery and ABI boundary repairs (2026-10-25)

`ERC7201.root` implements the namespace formula over bytes: Keccak-256,
subtract one modulo 2^256, ABI-encode that word, hash again and clear the low
eight bits. Literal calls fold at elaboration; runtime calls use the same
existing hash, encoding and wrapping arithmetic operations. `root_aligned`
proves the low-byte invariant for every identifier; empty, UTF-8 and the
OpenZeppelin ERC20 namespace have kernel-checked value proofs. Source fixtures
exercise both constant declarations and runtime strings, including whitespace.
The resulting integer gives no access to physical storage layout.

`abi.encodeWithSignature` now hashes the literal's original UTF-8 bytes;
it previously encoded each byte as a Unicode character a second time.
External function values retain their ABI `bytes24` type before their address
and selector become arithmetic: standard encoding is right-padded to 32 bytes,
packed encoding occupies 24 bytes. Internal function markers are refused where
the existing metadata retains them.

`abi.encodeCall` obtains parameter spellings before dispatch canonicalization
erases source widths. It checks the tuple's arity, primitive kinds and integer
width conversions, fixed-byte widening and function parameter/return components,
then applies contextual encoding conversions. Fixed-byte literals align to their
parameter type; an implicit narrowing is refused. Bare local function values
and explicit `this.f` members retain their own identities when a local shadows
`f`. A computed receiver is evaluated before the arguments even when its
selector folds to a constant; its failures and effects remain observable.
Discarded builtin calls pass through the same whole-expression validation
and lowering as used values. `bytes.concat` and `string.concat` validate their
source argument kinds, including nested concatenations and explicit casts.

Recursive decoder offsets and lengths are checked against remaining input
before addition, multiplication, traversal or allocation. This prevents a
maximum-size encoded length from overflowing the check or starting an enormous
allocation. Integer range and fixed-byte padding failures remain failures.
Unaligned and overlapping offsets accepted by solc remain accepted; a decoder
must not impose the encoder's strict canonical layout on every input.

`Secp256k1` replaces recovery's executable zero placeholder with a bounded
256-bit modular exponentiation/scalar walk. Coordinates and group scalars have
`Fin` types; points carry their curve equation and every constructed result
is checked. The boundary uses natural numbers to admit malformed ABI inputs,
then validates and enters those bounded types. Recovery accepts high-s
signatures, v=27/28, and 0<r,s<n; a missing square root or infinity fails.
The existing hash symbol and taclet read its `@[irreducible]` interpretation,
so symbolic proofs do not unfold the recovery computation by default.

No collision-freedom, authorization, primality, group-law or recovery axiom
was added. The vector proofs establish concrete reductions, not modular
inversion/group-law correctness or a general equivalence theorem for an
external EVM precompile. Existing semantic and calculus proofs continue to
refer to the executable interpretation. Concrete recovery costs more than
returning zero; three compiled valid recoveries took 16 ms locally. History
`7d57d9c0` introduced opacity as an unimplemented recovery boundary, not as a
previous computational optimization.

### Reproduction and review

`tests/abi-0.8.38/Features.sol` is compiled by exact solc
`0.8.38+commit.1835d247`, SHA-256
`6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`.
The separate AST and importer hash do not repin the frozen SolKeY compiler or
fixtures. `scripts/solc-ast.mjs` accepts an explicit compiler only together
with its checksum, source and output. The standard invocation still uses
SolKeY's compiler/checksum. Regenerate this fixture with:

```sh
node scripts/solc-ast.mjs --compiler-file /path/to/soljson-v0.8.38+commit.1835d247.js \
  --compiler-sha256 6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390 \
  --source tests/abi-0.8.38/Features.sol --out tests/abi-0.8.38/Features.ast.json \
  --wrapper Solidity/Examples/Tactics/AbiFeaturesImport.lean
```

`node scripts/check-abi-vectors.mjs COMPILER_FILE EXTERNAL_NODE_MODULES` checks
that same compiler and executes its Cancun bytecode with EthereumJS
VM/common/util 10.1.3 and ethers 6.17.0. Those are optional reference-test
dependencies, installed outside this dependency-free Lean package. The suite
passes 31 ABI, namespace and recovery vectors and five compiler rejection cases, including invalid values,
nonresidue, infinity, digest reduction, high-s and three different private keys.
`Examples/Tactics/AbiFeatures.lean`, `AbiFeaturesImport.lean` and `Recovery.lean`
pin matching Lean runs, rejected source conversions and kernel proofs. The
false source namespace assertion must panic; it is never reported as proved.

The read-only finder and skeptic reviewed ABI lowering and recovery without
calling Lean. Confirmed fixes cover UTF-8 selector hashing, implicit conversion
checks, discarded builtin statements, explicit-member shadowing, nested string
concatenation type preservation, and frozen-fixture safety of compiler overrides.
They found no concrete arithmetic defect in recovery or remaining decoder-bound
overflow in the reviewed paths. Both reviewers also confirmed the final computed
receiver evaluation order. Final validation results are recorded below.

### Remaining interfaces and proof limits

The feature catalog keeps general ABI coverage partial. Struct enum members
lose nominal identity/cardinality in `Contract.spellTy`/`enumRows`; function
mutability and some aggregate function markers are also absent. Exact legality
and enum decoding require the declarations/type metadata group to preserve them.
The source reader now consumes exact-width hex evidence at direct fixed-byte
`abi.encodeCall` parameters (M2 below). The handwritten `sol{}` DSL still erases
numeric literal spelling and requires an explicit `bytes2(0xabcd)` argument.
It does not accept decimal `43981` as an implicit fixed-byte argument. Arrays
of numeric hex literals and other aggregate contextual coercions remain open.
Inherited renamed function values still need their source ABI identity.
Recursive-type work must supply its agreed graph representation before ABI
traversal can cover those graphs. No second graph representation was introduced.
External reference-valued return decoding needs the calls/world group's typed
return/response interface; the current primitive-word `ExtResult` cannot carry
such decoded values. Dynamic recursive roundtrip proofs and the general
recovery/precompile equivalence theorem remain open. Source/compiler/EVM
conformance tests do not replace a frontend-equivalence proof.

### Final validation

The final `./run-lean.sh` returned success with the frozen rules entry file:
584 library jobs, 243 TestSuite jobs, and 377 taclets/131 read-bearing
annotations with zero mismatches. The existing decision example took 819 s
(the prior group's successful build recorded 890 s). Focused per-file MCP
error diagnostics passed for the computational modules, heap, elaborator and
regression modules. The source namespace assertion and guarded-byte roundtrip
are kernel-checked proofs.

The frozen corpus gate passes all 774 pinned obligations without verdict or
generated-output drift. The TestSuite audit records 552 derived, 11 refuted,
zero pending and one excluded obligation (plus two skips). The automation audit
records 491 automatic and 61 budgeted obligations, 11 refuted and zero pending.
The existing declaration-metadata Node regression also passes. Its subprocess
launcher needs execution outside the PID sandbox (`EPERM` inside); its test
expectations were not changed here.

The namespace/alignment value proofs depend only on `propext`/`Quot.sound`;
the byte and source proofs add only `Classical.choice`. `recover_generator`
uses no axioms; `recover_address` and `ecrecoverKey` use only `propext`.
No new axiom, native-decision proof or external Lean dependency was introduced.
The temporary axiom-audit source was removed.

The optional reference suite passes 31 pinned-solc/EVM vectors and five source
rejection cases. Three compiler-option rejection checks pass, and reproducing
the default frozen TestSuite AST with its original source-header path yields
byte-for-byte identical bytes. The original fixture and wrapper remain intact.

The feature audit covers 211 features/783 upstream symbols. The layer audit
covers 126 core modules with no path to the elaborator. Orphan checking retains
the 33 pre-existing scratch modules; documentation checking retains 13 existing
missing vendor/external references. No new finding was added to either list.
`git diff --check` is clean. Changes are uncommitted; the shared checkout's
other feature-group edits and unrelated logs were preserved.


## M2: source hex-width boundary (2026-10-26; worker handoff was patch_ready_unvalidated)

The source importer resolves an `abi.encodeCall` target by retained solc
`referencedDeclaration`, then reads fixed-byte widths from its public/external
function declaration or external function-variable signature. Before generic
constant normalization, a direct numeric hex literal can acquire `bytesN`
context only when its original token has exactly `2*N` hex digits and its
compiler type is a numeric constant. Leading zeros, mixed case, legal digit
separators and parentheses around individual scalar arguments survive this
check. The admitted result is `Fin (2^(8*N))`; no new core value or statement
representation is introduced. The raw AST is importer evidence only.

Decimal numerals, short/long hex tokens, arithmetic expressions, typed numeric
locals, missing evidence and address-typed 40-digit literals get no new
coercion. Existing type checking handles their rejection. Ordinary
`abi.encode(0xabcd)` keeps its numeric word layout. Byte-typed metadata such as
`this.f.selector` retains its established kind when this contextual path is
used. Tuple arity is preserved: extra parentheses around an entire
multiargument tuple create one component and must not be flattened into a
compiler-accepted call. No decoder, crypto implementation, frame or loop API
changes are included; solc's accepted noncanonical decoder layouts remain
unchanged.

`tests/abi-0.8.38/HexCall.sol` and its independently pinned 0.8.38 AST exercise
eight positive source cases and one deliberately false assertion.
`Examples/Tactics/AbiHexCall.lean` supplies exact-width/rejection proof scripts,
declaration-identity and malformed-input guards, concrete imported executions,
a universal exact-width property and a refutation of the false property. These
Lean scripts have **not** been elaborated or kernel-checked in the patch worker.
The primary integrator owns those checks and the axiom audit after merging.
No axiom, admitted proof, unsafe/native proof shortcut, raised heartbeat limit
or external Lean dependency is introduced by the patch text.

Regenerate only the new fixture (the frozen TestSuite pin remains intact):

```sh
node scripts/solc-ast.mjs --compiler-file /path/to/soljson-v0.8.38+commit.1835d247.js \
  --compiler-sha256 6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390 \
  --source tests/abi-0.8.38/HexCall.sol --out tests/abi-0.8.38/HexCall.ast.json --no-wrapper
node scripts/check-abi-hex-call.mjs /external/node_modules \
  /path/to/soljson-v0.8.38+commit.1835d247.js /path/to/soljson-v0.8.34+commit.80d5c536.js
```

The optional reference checker pins both compiler bytes and versions, then
executes legacy and via-IR Cancun code with the M1 external Node dependencies.
In the patch worker it passed 32 positive executions, four assertion panics
with code 1, and 40 compiler rejections across the four configurations.
Rejections cover decimal/width/type/arithmetic/address mismatches, tuple
shape, omitted components and invalid separators. These are concrete vectors,
not a general compiler/frontend or cryptographic correctness theorem.

Read-only finder/skeptic review covered declaration resolution, lexical width,
scalar parentheses, function-variable targets and preserved selector kinds.
Pinned compiler rejection of whole-tuple grouping prompted a correction to
keep direct components. The final review found no further concrete blocker.
The group remains incomplete for enum/cardinality decoding, inherited renamed
ABI identity, recursive ABI graphs, external reference-valued returns and the
general recovery/precompile equivalence theorem. The site manifest is left to
the primary integrator under the patch-only workflow.


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
base at least2 an exponent at least256 emits0x11; otherwise at most255 loop
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
observation. Final hash-consistent inventory replays all175 prior agreements,
the five repairs, and six directly affected reference-error elaboration cases.
The other251 explicit import/profile/host/configuration/resource cases retain
their original evidence and are explicitly marked not rerun; they are not
silently certified against the changed model. Final gate and inventory results
follow below once complete. The full source trust scanner's25 unrelated
inventory findings reproduce exactly at e430f436; only the new override site
is added to its inventory. The c31 documentation failure also remains a known
failure. No new axiom, sorry, native proof shortcut, dependency or raised proof
heartbeat/fuel/timeout/resource bound is introduced.
