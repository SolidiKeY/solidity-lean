# Source admission

Which compiler output the solc importer accepts, and what it refuses before
lowering. Inventory status: partial (admission is checked; extraction
completeness and lowering correctness are not proved).

## Supported

- **Compiler provenance.** `scripts/solc-ast.mjs` records the compiler file,
  version and SHA-256, the source SHA-256, the accepted pragma tokens, the AST
  analysis stage, and the pipeline, EVM target, optimizer and output settings.
  The pinned 0.8.34 and 0.8.38 compilers are both supported. The record is
  `N.report.provenance` (`Frontend/Source.lean`). `--via-ir` selects
  source-order operand scheduling; a requested ABI-v1 under via-IR records the
  effective ABI-v2. Modern fixtures default to Osaka.
  `Provenance.compilation` distinguishes historical inputs from analysed
  pipeline/settings records. `legacyFixture`, `pipeline`, `settings` and
  `effectiveCoder` are derived observations: they cannot be updated separately.
  Settings text is validated by `Source.read`; constructing a provenance record
  directly is not a validation certificate.
- **Static compiler-code inputs.** `Source.readCompilerCode` accepts bounded,
  linked hex artifacts only with matching modern compiler/source/settings
  provenance and declaration identity. These supply static creation/runtime
  constants; they do not model deployed-account code or prove compiler
  correctness. Historical fixtures cannot acquire these observations.
- **Historical fixtures.** Four-field fixtures still load with
  `admissionChecked = false` (`legacyFixture`); regenerate them with
  `--legacy-fixture` only to keep that boundary. They keep their pinned legacy
  statuses.
- **Admission scan** (`Frontend/SolcJson/Admission.lean`). It covers known
  nodes, semantic type metadata, call options, arguments, selected modifiers,
  execution dependencies and lexical specifications. Declaration references
  follow headers by compiler identity. Mutable initializers and base-constructor
  arguments execute only at deployment. Metadata-only selectors pull in no
  function bodies. Possible self-calls include cast and aliased receivers.
  `ScopeScan.within` proves that every feature of a successful result is in the
  selected profile. Scope decisions never depend on inventory status.
- **Names.** Source names keep their raw spelling: emitted Lean quotes
  identifiers, including `$` names and keywords. Positive declaration IDs
  separate user functions and fields from builtins. Specification and loop
  scans use syntax and lexical binders, so words inside strings and comments
  do not match.
- **Literals.** Rational remainder, signed bit operations, arithmetic right
  shift, evaluated outer array bounds, exact string/Unicode/hex bytes, zero
  scientific constants with extreme exponents and degenerate powers. Address
  literals and conversions keep their ABI kind through captures, arrays,
  conditionals and lazy expressions.
- **Stored external function members.** `.address`/`.selector` keep their
  `address`/`bytes4` casts until the native `fnPure` pass, so packed addresses
  take 20 bytes and packed selectors four. This needs matching result metadata,
  an outer external function type and a stable pure receiver place
  (`Examples/Tactics/SourceAdmissionImport.lean`).
- Operator aliases: [numeric-operators.md](numeric-operators.md). Function-value
  dispatch: [finite-dispatch.md](finite-dispatch.md) and
  [finite-dispatch.md](finite-dispatch.md#getter-targets).

Regressions: `Examples/Tactics/SourceAdmissionImport.lean`,
`SourceLiteralsImport.lean`, `SourceIdentifiersImport.lean`.

Unsupported state initializers retain a refused constructor row, including an
implicit constructor; initialization failure cannot become a default deployment.
Pipeline-specific inheritance scheduling is documented in
[the declaration repairs](declarations-metadata.md#group-08-source-lowering-repair-2026-10-26).
[The resumed repairs](declarations-metadata.md#group-08-resumed-remaining-declarations-2026-10-27)
cover static compiler-code artifacts, enum struct dependencies and restricted
mixed storage-return projections. Direct enums and one-dimensional enum arrays
retain exact range premises; composite ABI inputs containing enums remain
refused until recursive cardinality checks exist.

Function-value calls follow [finite dispatch](finite-dispatch.md), including
[getter candidates](finite-dispatch.md#getter-targets) and the restricted
zero-argument internal memory-byte return. Other reference signatures and
renamed inherited external values retain their explicit refusal boundaries.

## Refused, and why

- Unknown modes or settings, mismatched pragma records, incomplete modern
  headers, and a manual `evalOrder` override on a modern import.
- Unknown node kinds, literal/operator/location shapes, missing type or prefix
  metadata, and duplicate or missing declaration identities. The declaration
  index is finite, and depth and traversal are bounded.
- Payment dispatch that needs an inherited receive or fallback, or receive
  modifiers, until that dispatch is implemented.
- An effectful receiver of a stored function member (a call, an assignment, an
  increment, a compound index): the native selector lowering reads its receiver
  twice, which would duplicate effects or callbacks.
- An inherited builtin observation that the executing contract shadows gets an
  implementation diagnostic instead of a silent change of meaning.
- Canonical assembly rethrow only in its exact shape, with the matching
  memory-bytes declaration identity; ordinary integer pointers do not qualify.
- Legacy ABI-v1 decoding is an implementation diagnostic.

## Decisions

- Provenance records an external solc analysis. It does not authenticate
  handwritten JSON or validate bytecode, and it is no theorem of
  compiler/lowering equivalence.
- Representation-limit failures of modern fixtures are implementation gaps,
  reported separately from elaboration status.

## Left

- General constant-materialization bounds.
- Function-value target sets outside the checked finite-dispatch fragment.
- Recursive nominal types ([recursive-types.md](recursive-types.md)) and the
  ABI-v1 decoder.

## Reference check

`node scripts/check-source-admission.mjs SOLJSON SHA256 MODULES_DIR` compiles
and runs the cases for each pinned compiler, legacy and via-IR, under Cancun,
and checks the invalid sources and pragma combinations.

## Source scope and selector integration

Clashing local bindings use fresh declaration-ID names, preserving outer initializer
reads and restoring the surrounding scope after a block. Source parameters,
loop annotations and certified witness positions retain their compiler identity.
Specification binders retain their nearest lexical scope; the finite-filter
omitted-state check inspects parsed free root reads instead of bound names.

Declaration selectors resolve by compiler ID. Error/event selectors receive no
`.address` exemption; missing identities and same-named local variables cannot
be folded as error declarations. Stable stored external values use the separate
typed ABI projection path. Malformed and effectful projections remain refused.
The integrated source checks require the complete 26-row FunctionTypes roster:
16 proofs, seven internal helpers and three pending false claims. See
[dafny-verification.md](dafny-verification.md#integration-with-current-origin)
for the focused build, source tests and independent merge reviews.

## Coverage step 2: compilation units (2026-10-28)

Work starts at origin/master f4dee4a29c2e208b36db4a4161a4723c735cd775,
on the isolated branch feature/source-units-step2. The original work checkout
and the historical cloud reports are preserved.

The current-master reproduction retains all 39 historically provenance-blocked
fixtures. Every one still reached the explicit multi-source refusal before this
change. The new schema stores the complete original SourceUnit AST set,
compiler source IDs, declaration IDs, per-source SHA-256 and accepted pragmas,
and one shared compiler/settings record. The selected main source is explicit.
There is no concatenated SourceUnit or fabricated single-source header.
N.report.provenance.sources exposes the complete per-file metadata.

The SHA-pinned compiler resolves import paths, remappings, aliases and cycles
from explicit standard-JSON source contents; URL/import callbacks are not used.
The reader checks source-set identities, original source locations and each
resolved import path/source-unit-ID pair. Missing, duplicate and foreign
metadata fail closed. Schema-1 modern imports require regeneration with
compilation-unit provenance; historical four-field inputs keep their existing
unchecked boundary. Schema 2 currently requires multiple source units.

Declaration lookup and dependency admission use all original compiler IDs.
Language-mode checks use each node's own source pragma, while pipeline settings
remain shared by the compilation. Imported free functions, namespace aliases,
transitive/circular imports, constants and existing using-for/operator lowering
reuse the intrinsic elaborator. Namespace calls do not acquire a receiver
argument. A discarded type selected from the same static module preserves its
condition's effects and failures exactly once.

Qualified and renamed error references retain the original short error name
and signature, including an import alias named Panic. Native error names keep
the original selected/file signature. Additional identities share it only for
matching elementary parameter types and validated equal selectors. Conflicting
references retain an explicit rendered-scope refusal instead of poisoning an
otherwise supported local constructor. Error byte encoding itself is unchanged.

### Reproduce a compilation unit

Use the dependency-free external helper with an exact supported compiler file:

~~~sh
node scripts/solc-unit.mjs \
  --input tests/solc/source-units/SourceUnits.input.json \
  --compiler /path/to/soljson-v0.8.38+commit.1835d247.js \
  --main-source app/Main.sol --out /tmp/source-units.ast.json
node --test scripts/source-units.test.mjs scripts/solidity-upstream.test.mjs
~~~

The input is Solidity standard JSON with explicit content for every source,
AST-only output selection, and the recorded supported settings. The helper
checks the compiler digest before loading it and rejects invalid UTF-8 input.
Empty remapping targets and equals signs inside targets are preserved and
tested against real compiler output.

### Deliberate remaining refusals

- Multi-source NatSpec containing @custom:key and any loopSpec field:
  solidity.compilationUnitSpecifications. Source comments are checked before
  solc can discard loop NatSpec. Strings and ordinary comments remain data.
  A file-local specification namespace adapter is required before admitting
  these claims; foreign constants/enums must not silently change a claim.
- Inheritance in a legacy-pipeline unit with mixed requested ABI coders:
  solidity.compilationUnitAbiModes. The declaring-source entry decoder needs
  an adapter; viaIR keeps its effective ABI-v2 behavior.
- Conflicting or nominal custom-error signatures sharing a native short name,
  and general module-valued expressions outside the checked discard shape,
  remain explicit lowering refusals.
- Schema-2 static compiler-code artifact inputs and one-source self-import
  provenance remain unfinished. No foreign code artifact is invented.
- Existing host, log, assembly, delegatecall, gas and layout policies are
  unchanged. Their refused observations are not dropped to obtain a pass.

### Validation and review

The compiler fixtures cover both pinned compilers (0.8.34 and 0.8.38) and
legacy/viaIR. Nine axiom-pinned kernel theorems check 28 finite outcomes:
normal return, false-assertion panic, receiver and module-condition effects,
prior failure, exact qualified/aliased error bytes, and preservation of local
error signatures despite a conflicting foreign error. Their axioms are only
propext, Classical.choice and Quot.sound. Ordinary calculus reverts still
abstract data; byte certificates use the existing external-entry API.

The preserved upstream replay reports 31 working, one broken and seven blocked
fixtures, with all 64 prepared pipeline jobs checkpointed. The remaining broken
fixture requires excluded assembly/codesize semantics. The blocked fixtures
retain their host-behavior or fixture-format refusals. These are typed-model
observations, not compiler-generated EVM observations or a compiler/lowering
equivalence proof. Digest checks record external analysis; they do not
authenticate handwritten JSON.

The focused Node tests, existing source-provenance regression, trust,
reachability, layering, strict automation and generated-inventory checks pass.
Per-file dependency checks and kernel guards run sequentially with one Lean
thread and -j1. This VM lacks systemd/delegated cgroups: a hard 12 GiB address
space limit plus a seccomp no-fork filter bounds each Lean process group, with
an available-memory reserve. The original default Lake attempt was blocked
because that filter prevents Lake spawning compilers; it is not passing
evidence. The runtime follow-up below records a separate aggregate-capped attempt. The documentation audit retains missing references in unchanged
historical/vendor citations. Exact commands, per-fixture results, hashes,
timings, memory measurements and remaining refusals are recorded in the
[per-fixture results](../../tests/upstream/step2-source-units-results.json) and
[validation record](../../tests/upstream/step2-source-units-validation.json).
The sealed replay takes 27.972 seconds, with 834,044 KiB sampled peak Lean
RSS and 1,091,784 KiB peak across its process tree. The sealed kernel file
takes 6.044 seconds. There are 78 required variants: 64 executed jobs retain
86 observed calls from 62 working jobs. The two excluded-assembly jobs retain
their two unexecuted expected calls; the 14 pre-preparation refusals remain
unexecuted.

Independent read-only finder and skeptic reviews used no Lean server.
Confirmed fixes include compiler-pin-before-execution, fatal UTF-8 decoding,
valid remapping forms, missing import targets, per-source modes, source/loop
specification refusal, lexical error aliases, preservation of original error
scope, and all-source raw-ABI assembly policy. Counter-once and prior-panic
controls cover the module-condition rewrite. No new dependency, axiom, sorry,
raised heartbeat/fuel/search limit, changed upstream expectation or core rule
is introduced.

### Runtime audit follow-up (2026-10-28)

Audit dc0ac441-6aee-4c01-b8db-2087d739208b rechecked the same VM and
implementation commit da933e15. Actual Lean 4.24.0 and Lake
5.0.0-src+797c613 commands work. The already running managed Docker daemon
provides a kernel 12 GiB aggregate cap and zero swap while allowing Lake
children; no daemon, security, credential or environment configuration changed.
A task-local wrapper serializes Lean with -j1 and the unchanged 180-second
per-file timeout, under the documented writer lock.

KeySort passes. The default build reaches job 246 of 688, then the available
memory guard stops only this task container: exit 137, OOMKilled=false,
1205.596 seconds. It remains **blocked**, not passed. The no-fork obstruction
is resolved; the remaining validation needs usable VM capacity for the 12 GiB
task cap plus the documented 12 GiB available-memory reserve and OS overhead.
A conservative budget is 24 GiB usable memory plus overhead, not a measured
minimum: the observed run does not establish its exact peak requirement.
The last pre-stop minimum available memory is 12,590,648 KiB; the exact crossing
value and task peak were not persisted before kill. They are not inferred
from the cap. The live monitor JSON predates the stop, and its false stop flag
is superseded by the terminal monitor output and container exit.

The [runtime audit record](../../tests/upstream/step2-source-units-runtime-audit.json)
and [retry log](../../tests/upstream/step2-source-units-runtime-audit.log) preserve
commands, failed cache-path attempt, limits, timing and measurement limitations.
No interrupted check is passing evidence. This command does not run TestSuite,
the frozen sort comparison or run-lean.sh. The nine theorem guards, 79 direct
module checks, 64 replay jobs and 86 observations remain unchanged: 31 working,
one excluded-assembly broken and seven blocked fixtures. All feature refusals
remain separate from the missing combined validation.

The final independent read-only finder and skeptic reviews used no Lean workers.
Their confirmed packaging fixes scope the original digest list to da933e15,
record follow-up documentation digests separately, and label the memory budget
as conservative rather than a measured minimum. No other defect remained.

### Isolated-VM headroom continuation (2026-10-28)

The runtime audit above applied the shared-checkout 12 GiB reserve to an
isolated 16 GiB cloud VM. That scope was incorrect for this task: coverage-plan
budgets a hard 12 GiB process group with measured OS headroom. The prior failed
runs and hashes remain intact; the earlier larger-VM requirement was not
established by those stops. User authorization explicitly clarified this scope.

The continuation keeps the kernel 12 GiB aggregate cap, zero swap, serial
LEAN_NUM_THREADS=1 and -j1, and unchanged 180-second compiler timeout. A 2 GiB
guard monitors host available RAM and the enclosing cgroup's free charge margin.
It reuses valid Lake artifacts, with no cold full rebuild or feature changes.
The default build terminates exit 1 after 5936.634 seconds: CallbackStrategy,
Recursion, OpenLoops and DecisionHashes each time out at 180 seconds. No OOM
or headroom stop is observed; maximum recorded task peak is 9,569,771,520 bytes,
with minimum sampled parent headroom 7,228,592,128 bytes. These are observed
counters, since the failure path does not emit a terminal kernel footer.

The independent suite first stops during Derived17 when the parent margin
falls below 2 GiB, with task charge still below 12 GiB. The parent retains
about 4.17 GB of clean file cache from this clone's generated build and artifact
files. POSIX_FADV_DONTNEED on those owned files reduces the measured idle parent
charge from 4,419,555,328 to 643,207,168 bytes, without deleting or changing files
or system configuration. This concrete changed baseline supports resuming only
the unfinished suite and sort checks under identical limits.

TestSuite then passes all 260 jobs, and the explicit pinned SolKey sort check
passes: 377 taclets parsed, 131 read-bearing, 131 covered. The resumed run exits
0 after 518.146 seconds. Its exact terminal task peak is 12,213,141,504 bytes
(11.37 GiB); minimum sampled parent headroom is 4,108,681,216 bytes (3.83 GiB),
and terminal memory-limit/OOM events are zero. No target demonstrated exceeding
the hard cap. The four default-build timeouts remain blocked, not passing; no
run-lean.sh pass or full feature coverage is claimed.

The [isolated validation record](../../tests/upstream/step2-source-units-isolated-validation.json)
retains commands, scripts, samples, all stops, exact cache-hint code, hashes and
measurement precision. Baseline snapshots precede launch; polling starts
immediately after docker start, not before it. Fixture results remain exactly
31 working / 1 excluded-assembly broken / 7 blocked, 64 jobs and 86 observations,
with 14 required-but-unrun variants and all named feature refusals preserved.

Final independent read-only finder and skeptic reviews verified the saved
commands, hashes, samples and gate results without Lean workers. Confirmed
evidence fixes distinguish baseline from polling start, observed failed-run
counters from the exact successful footer, and retain the precise cache-hint
code and owned path whitelist. Both reviews found no outstanding defect.

### CallbackStrategy timeout diagnosis (2026-10-28)

Audit 39481496-2ddb-4956-a5b9-43cdfa5a677e follows the first default-build
timeout without repeating the full build or passed suite/sort gates. The saved
Lake setup lists 229 local imported modules; every source, plus CallbackStrategy
itself, is byte-identical to starting master f4dee4a2. No source-unit change is
in this closure. The setup has no plugins or option overrides, and every
referenced dependency artifact is hashed in the diagnostic record.

One controlled baseline probe bind-mounts the exact baseline source at its
original canonical path and uses that saved setup with source-identical checked
current dependency artifacts. It is a warm reused-artifact diagnostic, not a
cold independent baseline build. With the same 180-second compiler limit,
-j1, LEAN_NUM_THREADS=1, hard 12 GiB aggregate cap, zero swap and 2 GiB
headroom guard, it also times out: exit 137, outer elapsed 180.266 seconds.
Exact terminal peak is 662,904,832 bytes; limit/OOM counters are zero, and
minimum sampled enclosing-cgroup headroom is 14,084,960,256 bytes. Baseline
snapshots precede launch; polling starts immediately after container start.

This reproduces a pre-existing callback proof-cost blocker under the fixed
budget and demonstrates no source-unit-induced regression. No semantic fix,
general closer/step-13 work or budget increase is justified in this lane. The
required separate action is investigation of the existing callback proof or
elaboration cost within unchanged premises and budgets. Recursion, OpenLoops
and DecisionHashes retain their earlier timeouts; no baseline claim is made
for those three, and none was retried here. The assigned default gate remains
blocked and the feature is not complete.

The [callback diagnostic](../../tests/upstream/step2-source-units-callback-diagnostic.json)
retains the exact saved invocation, wrappers, source/artifact comparison and
terminal measurements. Prior successful 260-job TestSuite and pinned sort, all
31/1/7 fixture statuses, 86 observations, 14 unrun variants and named refusals
remain unchanged. No historical failed result is promoted to passing evidence.

Independent read-only finder and skeptic reviews verified the closure, source
and artifact hashes, all 719 samples and terminal counters without Lean workers.
The final record corrects polling-start wording and limits the baseline inference
to this one reused-artifact target. No outstanding review finding remained.

### 2026-10-28 proof performance repair and original acceptance

The later user-authorized repair supersedes the blocked default-library status
above. It does not change the historical failed results. Inspection established
that the 180-second compiler timer belonged to our private exploratory wrapper;
the original repository acceptance script has no per-file wall timer. The
original proof, heartbeat, fuel, search and stack settings remain unchanged.

A declaration profile found duplicate search in CallbackStrategy.withdrawSafe:
the theorem and following guarded search prove the same goal. Replaying existing
rules in the theorem reduces focused elaboration from 16.957288 to 4.332872
seconds (same-prefix module 20.330759 to 6.534937 seconds). The statement,
premises, program, invariant and guarded automation test are unchanged. The
kernel audit reports only propext, Classical.choice and Quot.sound. No tactic or
core representation changed. Earlier speed choices in 7a6120d3 and 1a7d5b0e
were inspected and preserved.

Profiles of Recursion, OpenLoops and DecisionHashes did not justify applying the
same optimization blindly. A private DecisionHashes coverage-helper candidate
was slower and fully reverted; its failed/interrupted attempts remain archived.
Global profiling adds messages to guarded output, so those exploratory full-file
runs are not acceptance evidence. Uninstrumented original sources subsequently
passed the real gate, including their unchanged guards.

The original run-lean.sh completed exit 0 in 2117.921652 seconds: default 688
jobs, TestSuite 260 jobs and frozen sorts 377 parsed / 131 read-bearing / 131
covered. The run reused valid warm artifacts and a read-only Lake scheduling
overlay adding only -j1; LEAN_NUM_THREADS=1, hard aggregate 12 GiB, zero swap and
the isolated-VM 2 GiB headroom guard remained enforced. Exact terminal peak was
10,556,030,976 bytes; minimum sampled enclosing-cgroup headroom 3,472,637,952
bytes. There were no memory-limit events, OOM or resource stop. Whole-second
compiler timings were 207 / 401 / 541 / 277 seconds for CallbackStrategy /
Recursion / OpenLoops / DecisionHashes. These are new passes, not relabeled
180-second probes.

Fresh source replay retained 31 working / 1 excluded-assembly broken / 7 blocked,
64 prepared jobs, 86 observations and 14 required-but-unrun variants. Its global
model hash changed because the proof example is included in that hash; the
source-unit interpreter closure is unchanged. All 32 focused Node tests,
layers, orphan, strict automatic, generated inventory and trust checks passed.
The first trust attempt lacked Git in the minimal container; the preserved
retry with the existing binary mounted read-only passed. Documentation paths
remain nonpassing with the exact historical 20 missing references and 6
ambiguities. No source refusals or feature statuses were promoted.

[New terminal evidence](../../tests/upstream/step2-source-units-proof-performance.json)
and [fresh per-fixture results](../../tests/upstream/step2-source-units-proof-performance-results.json)
preserve provenance, failed candidates, measurements and commands. Kernel proof
checks establish the stated theorems; compiler AST and model observations establish only
the recorded finite fixtures. Unsupported shapes listed in the earlier record
remain unsupported. The bounded step-2 implementation remains partial.

Independent read-only finder and skeptic reviews verified the actual terminal
pass, artifact hashes, sample minima, fresh fixture counts and source proof.
Their packaging findings were fixed: observations are described as compiler AST
and model evidence, historical profile polling wording is qualified, and every
retained failed-candidate input/wrapper/log has an export hash in the
[artifact manifest](../../tests/upstream/step2-source-units-proof-performance-artifacts.json).
Neither review ran Lean or the server. No confirmed proof defect remained.
