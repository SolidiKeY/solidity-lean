# Resolved operator aliases

User-defined operators (`using {f as +} for T global`) on scalar UDVTs. The
numeric-operators group is otherwise incomplete.

## Supported

- solc records the resolved pure free function in the `function` field of a
  `UnaryOperation`/`BinaryOperation`. The reader checks that identity against
  the declaration table and emits a direct call to the unique
  `solcFunction<ID>` helper. It never resolves by name and never falls back to
  the builtin. All sixteen signatures: unary `-`, `~`; binary `&`, `|`, `^`,
  `+`, `/`, `%`, `*`, `-`, `==`, `>`, `>=`, `<`, `<=`, `!=`.
- `operatorAlias?` (`Frontend/SolcJson/Body.lean`) validates the annotation,
  positive identities, a pure free definition, arity, the UDVT declaration,
  identical nominal operand identities and the result (bool for comparisons,
  the same UDVT otherwise). Admission calls the same validator, records
  `operatorAliases` and adds the aliases to the call graph, so an alias body's
  features and callees are scanned.
- A call elaborates to the ordinary `Stmt.call`. Aliased operands are captured
  left to right in both pipelines; builtin binary operations keep the
  pipeline's order. Calls stay inside lazy boolean and conditional branches,
  the callee keeps its own checked/unchecked body, and a discarded result still
  runs the call. `pureExpr` treats an alias as a call.
- `hoistArgs` holds an earlier non-simple argument before hoisting a later
  one, so a later cast, bounds check or narrow/modular guard cannot fail first.
  Captures keep byte/address/enum/function metadata and width.
- Scalar UDVTs over narrow integers, fixed bytes, bool, address and payable
  address. Entry bounds use the underlying type.

Regressions: `tests/operators-0.8.38/OperatorAliases.sol` (meanings that
disagree with the builtins), `Examples/Tactics/OperatorAliasesImport.lean`
(every signature, distinct UDVTs over one primitive, nested aliases, lazy
branches, division by zero accepted by a custom alias, failure priority, a
universal `customZero` proof and the refuted `falseBuiltin`).

## Refused, and why

- Null, malformed, missing, nonpositive, foreign or signature-mismatched
  annotations, in admission and in lowering. Equal underlying primitives do not
  make two UDVTs equal: modern fixtures keep the `typeIdentifier`, and
  historical fixtures without it must be regenerated.
- Conditional function callees with aliased or effectful arguments (the
  conservative rewrite).
- UDVT compound assignment and ambiguous same-scope overloads in a `using`
  directive: solc rejects them, and the reference pins that.

## Cost

Extra captures enlarge elaborated programs and change output pins. The design
keeps `1a7d5b0e` (one callee body elaborated once) and `63ac4b63` (split Elab).

## Left

- UDVT fields and aggregate shapes, nominal enums, general function dispatch.
- General signed shifts and complements, contextual literal promotion, nested
  numeric positions.
- Failure order outside argument lists (other hoist policies are unchanged).

## Reference check

```sh
node scripts/check-operator-aliases.mjs SOLJSON_FILE NODE_MODULES_DIRECTORY
```

Runs the EVM vectors and upstream rejection cases against the pinned solc
0.8.38, comparing actual revert bytes (`Panic(0x01)`, `Panic(0x11)`, empty).
Ordinary Lean runs assert only failure, not the panic code.

## Group 03 upstream revalidation (2026-10-26)

This independent repair starts from `origin/master` at
`006fcd593f5beeb540e7adf2bc76de4638566924` on branch
`codex/group03-operators`. The managed executor is `/workspace/solidity-lean`;
`/workspace/.setup/activate.sh` supplies Lean 4.24.0 and Lake
5.0.0-src+797c613. `lake build Solidity.KeySort` succeeded both before and after
switching to the requested base. The runner verified all 11,622 pinned archive
files. The first runner invocation hit its five-minute cold dependency-build
limit before executing a fixture; a separate logged build of
`Solidity.Tools.Upstream` completed, without changing execution/proof limits.

All fourteen assigned paths were reproduced individually with `--batch-size 1`
and separate output directories before editing. Seven already matched every
required pipeline on current master. The old corpus results remain historical
observations on `cadb628c`, not current failures.

The patch reuses existing declaration-indexed alias/call machinery:

* Scalar constant substitution now admits the same supported resolved scalar
  types as UDVT registration. Its existing ID lookup and source cast retain
  narrow widths, bytes padding and address kind. This fixes constants such as
  `Int constant ONE` with underlying `int8`, previously omitted as storage.
* Builtin signed complement at the source boundary becomes `intN(-1) - x`.
  Aliased operators are resolved first and keep their original callee. The
  operand occurs once and the exact signed width remains explicit. The checked
  integer identity `~~~x = -1 - x` and signed-range closure prove that the rewrite
  handles both endpoints without an intermediate negation overflow. Intrinsic
  operator definitions, runtime rules and their soundness proofs are unchanged;
  this does not extend native signed `~` syntax.
* Replay selects the canonical ABI signature attached to the imported function's
  source declaration, requiring a selected external entry. It no longer compares
  a nominal source name such as `Fixed` against ABI `int128`. Internal helpers
  cannot capture an ABI call. Rows without a source declaration retain the
  existing signature fallback used by native controls. A present declaration
  without a canonical signature does not fall back. Imported canonical
  signatures compare exactly. Native fallback normalizes parameter types only,
  preserving function names containing text such as `uint256` or `int256`.
* An inconclusive runtime call retains the completed observations, the current
  blocked vector and the precise fuel/panic/return diagnostic. It remains blocked
  before expectation comparison. This repairs reporting, not runtime semantics.

`tests/upstream/Operators.lean` checks source constants, signed 8/64/256-bit
endpoints, checked single-evaluation operands, unchecked minimum boundaries,
byte padding, a false assertion and nominal overloads colliding with an internal
ABI-shaped signature, in both pipelines. Its ten printed theorem axiom sets are
subsets of `propext`, `Classical.choice`, `Quot.sound`. The new fixture was produced
with the SHA-checked 0.8.38 compiler; its source SHA-256 is
`a611b835995d4beda5a9dbc666c26b59f52b1a465de3d2dd7e2eff01bc186e25`.
The final two replay regressions additionally pin observation retention after a
successful stateful call followed by fuel exhaustion or generic panic.

The source/expectation archive, snapshot manifest and historical results are
unchanged. No dependency, axiom, `sorry`, heartbeat override, representation
refactor, spelling-based operator dispatch or Bridge change was added. General
inline assembly remains excluded: these cleanup fixtures need dirty-word and
machine-memory semantics, not another alias lookup. Huge recursive failure
vectors cannot pass merely because execution exhausts resources.

### Final assigned-fixture outcomes

Every filename below has prefix
`test/libsolidity/semanticTests/operators/userDefined/`. Historical status was
broken for all fourteen; “before” is the fresh current-master reproduction.

| Fixture | Before | Final legacy / viaIR | Disposition |
| --- | --- | --- | --- |
| `all_possible_operators.sol` | broken | working / working | repaired |
| `all_possible_user_defined_value_types_with_operators.sol` | working | working / working | already fixed on master |
| `attaching_and_defining_operator_with_same_function.sol` | working | working / working | already fixed on master |
| `consecutive_operator_invocations.sol` | working | working / working | already fixed on master |
| `fixed_point_udvt_with_operators.sol` | broken | working / working | repaired |
| `multiple_operator_definitions_different_types_different_functions_separate_directives.sol` | working | working / working | already fixed on master |
| `multiple_operator_definitions_same_type_same_function_same_directive.sol` | working | working / working | already fixed on master |
| `operator_definition_shadowing_builtin_keccak256.sol` | working | working / working | already fixed on master |
| `operator_parameter_and_return_cleanup_between_calls.sol` | broken | excluded / excluded | expected exclusion: inline assembly |
| `operator_parameter_cleanup.sol` | broken | excluded / excluded | expected exclusion: inline assembly |
| `operator_precendence.sol` | broken | working / working | repaired |
| `operator_return_parameter_cleanup.sol` | broken | excluded / excluded | expected exclusion: inline assembly |
| `recursive_operator.sol` | broken | blocked / blocked | ABI repaired; loop fuel exhausted |
| `unchecked_operators.sol` | working | working / working | already fixed on master |

The three assembly cases retain raw runner status `broken` with every
`variants[].gaps[].status` equal to `excluded`; the table labels their actual
admission boundary rather than claiming Lean support. The recursive report
retains both completed `testUnary` observations in each pipeline and the
`99999999999` input at which loop fuel is exhausted. Subsequent vectors remain
unexecuted, so the complete fixture is blocked. No expected failure is inferred
from exhaustion.

The broad value-type fixture already passed on master. An intermediate rerun
timed out under concurrent verification; that evidence is retained. Its pre-canonical
serial rerun passed both modes with the original 120,000 ms per-process timeout
and 1,000 loop fuel (238.135 seconds including both modes and setup).

Full before/intermediate/final reports, per-source SHA-256 values and exact
argument lists are saved in [group03-results.json](../../tests/upstream/group03-results.json).
The final model SHA-256 is
`ea3cf959ff9eaee92b01f4aa6f36a4b799440607f5c43662a236d016143d9796`.
The current-master before hash is
`c86945ed62a18ffccf0b72b291c6271f44462f7b1d60b101e73fd2ec565c8699`.
Historical model hashes remain in the original results. All stages use compiler
SHA-256 `6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`,
archive SHA-256 `9200f2a26b08be5b77faf877c44f5cfbf5ea95f1bccc45dae559d2fbc7cefb2d`,
and unchanged runner SHA-256
`c860ec034b8dbf26c632f45a0c52c215df9eda9fc2fd10e3c3f8b84f4a37d468`.

### Reproduction and review

```sh
cd /workspace/solidity-lean
source /workspace/.setup/activate.sh
lean --version
lake --version
lake build Solidity.KeySort
node scripts/solidity-upstream.mjs verify
node scripts/solidity-upstream.mjs run \
  --compiler /workspace/.setup/soljson/soljson-v0.8.38+commit.1835d247.js \
  --filter test/libsolidity/semanticTests/operators/userDefined/all_possible_operators.sol \
  --batch-size 1 --out .lake/upstream/group03-recheck/all_possible_operators
node --test --test-isolation=none scripts/solidity-upstream.test.mjs
lake --no-build lean tests/upstream/Replay.lean -- --tstack=131072
lake --no-build lean tests/upstream/Operators.lean -- --tstack=131072
node scripts/check-automatic.mjs --strict
node scripts/check-orphans.mjs
node scripts/check-layers.mjs
scripts/check-testsuite.sh --complete --solkey tests/migration/solkey/keyext.solidity.examples
scripts/check-solkey.sh --key tests/migration/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key
```

Each of the other thirteen exact filters and its distinct output directory is
recorded as an executable argument list in the evidence file. Do not reuse
`tests/upstream/results` for retries. Fixture generation uses
`scripts/solc-ast.mjs --compiler-file FILE --compiler-sha256 SHA --source
tests/operators-0.8.38/OperatorBoundaries.sol --out FILE --no-wrapper`
with `--via-ir` for the IR fixture.

Lean MCP diagnostics were not exposed. Configured per-file commands checked
Body, Contract and Upstream with `lake --no-build lean FILE -- --tstack=131072`.
The earlier wall times were 32.920 s, 32.471 s and 3.073 s respectively.
Final canonical operator controls took 6.935 s and replay controls 5.067 s. No heartbeat
limit was raised. The 14 adapter tests, strict automation (491 automatic,
61 budgeted, 11 refuted, zero pending), reachability (667 modules, zero orphans),
layering (143 core modules, zero frontend reach), frozen TestSuite audit and
frozen sort check (377 taclets, 131 read-bearing annotations) passed. The
documentation-path check retains its 13 baseline missing references outside
this patch.

Independent read-only finder and skeptic reviews inspected the actual patch,
metadata hashes, nominal lookup, signed range/effects and native fallback. The
skeptic required the selected-external-entry guard, which is implemented and
covered by the internal/external overload collision. A final skeptic pass
confirmed that observation retention cannot turn inconclusive execution into
a matching expected failure. Neither reviewer opened a Lean worker. No
confirmed review issue remains.

The shared integration dependencies are limited to the scalar constant filter
in Contract, signed source complement in Body, and declaration-bound ABI lookup
plus blocked-prefix evidence in Upstream. No unpublished group patch is required.
Runtime fixture agreement is observational evidence; only the stated algebra
and concrete regression claims are kernel proofs, not a universal solc/model
correspondence theorem. Compiler acceptance is reference-solc evidence.

### Canonical function-name identity control

A final read-only review exposed a separate adapter bug: global replacement of
`uint256`/`int256` also changed function names. `route_uint256()` incorrectly
selected an earlier `route_uint()`, returning 11 instead of 22; a deliberately
wrong expectation of 11 falsely passed. Both compiler pipelines and native
replay reproduced the defect before the repair. Imported declaration signatures
are canonical already and now compare exactly; native signature compatibility
normalizes only the parameter suffix. The selected-external-entry guard remains.

`tests/upstream/AbiIdentity.lean` now checks four distinct function identities and
rejects the former false-passing output in legacy, via-IR and native replay.
All six checks pass. The independently reviewed implementation is commit
`49ce97cb`, following `663a6113`; neither commit was pushed or merged.

### Broader validation and executor resource limits

The first cold `run-lean.sh` was interrupted by an environment restart after
542/649 jobs, with no errors reported. Its complete log is retained at
`.lake/upstream/group03-full-build.log`. Runtime versions and the successful
`Solidity.KeySort` gate were rechecked after reconnection.

The resumed broad library run reached 643/649 jobs. The unchanged
`Solidity.Examples.Decision` regression did not finish within a declared
900-second per-file validation budget and was stopped after 918 seconds. Its
297-module transitive import closure contains none of the three changed model
files. This broader gate is **resource-blocked**, not passing and not an observed
semantic regression. The full resumed log and dependency evidence are retained
at `.lake/upstream/group03-full-build-resumed.log` and
`.lake/upstream/group03-decision-independence.json`. No proof limit was raised.

The first frozen-corpus build lost `TestSuite.Derived17` with exit 137.
`/sys/fs/cgroup/memory.max` reported 16 GiB, and `memory.events` confirmed one
out-of-memory kill. Its complete build log was retained before the existing
check script deleted its temporary output. An isolated
`LEAN_NUM_THREADS=1 lake build Solidity.TestSuite.Derived17` passed in
256.844 seconds with no additional OOM event. `lake build SolkeyTestSuite` then
passed. The frozen-corpus rerun passed with `check-corpus: ok` against
SolKey `473da8944c`; the 774-obligation partition is unchanged. This changes
build concurrency, not statements, premises, proof budgets or expected results.

The final frozen sort rerun passed (377 taclets, 131 read-bearing annotations).
`#print axioms` for the existing `custom_zero_valid` and
`false_builtin_invalid` headline results also reports only the allowed standard
axioms. Final task-specific commands additionally include:

```sh
lake --no-build lean tests/upstream/AbiIdentity.lean -- --tstack=131072
LEAN_NUM_THREADS=1 lake build Solidity.TestSuite.Derived17
LEAN_NUM_THREADS=1 lake build SolkeyTestSuite
LEAN_NUM_THREADS=1 scripts/check-corpus.sh --solkey tests/migration/solkey/keyext.solidity.examples
```

### Final handoff evidence

Final canonical-identity revalidation again gives ten working fixtures in both
required pipelines, three explicit assembly exclusions and one fuel block. The
largest value-type fixture completed both modes in 193.933 seconds, with the
same 120-second per-process limit and 1,000 fuel. Earlier reports are retained
as separate attempts; none was overwritten or merged into historical results.

[group03-validation.json](../../tests/upstream/group03-validation.json) records
exact commands, exit statuses, complete-log hashes, timings, all twelve checked
axiom sets, executor memory evidence and the unchanged decision dependency
closure. [group03-results.json](../../tests/upstream/group03-results.json) embeds
all per-fixture observations and hashes, including the final canonical attempt.
The implementation is `49ce97cb` on `codex/group03-operators`, based on the
requested `006fcd59`; the preceding repair is `663a6113`. No push or merge was
performed. The broader library gate remains explicitly resource-blocked at the
unchanged decision regression; TestSuite, frozen sort, frozen corpus, affected
modules, source controls and structural gates passed. The documentation-path
gate retains only its thirteen baseline missing references.

The final read-only finder and independent skeptic verified all 57 report hashes,
17 validation-log hashes, fourteen archived source hashes, control fixture hashes,
the final model digest and all twelve standard axiom sets. Neither opened a Lean
worker or ran a build. The skeptic's timing-label correction is applied above;
no confirmed implementation, proof, fixture-status or resource-classification
issue remains.

## Group 03 continuation: bounded machine replay and Decision validation

This continuation preserves `c247c849`, its three preceding lane commits, patch,
and all earlier historical inputs/results. It uses the same managed executor,
activation script and branch. Lean 4.24.0, Lake 5.0.0 and the cached
`lake build Solidity.KeySort` gate passed again. Lean MCP diagnostics remain
unavailable; checks use the configured per-file commands with `--tstack=131072`.

The recursive fixture has **no loops**. Its Lean run reaches
`recUnroll Prog.recBase … recDepth` at 1,024 frames; `Prog.recBase` is
`assume(false)`, producing `.exhausted`. This differs from the artificial loop
budget's `.diverge`. Replay now distinguishes those diagnostics while keeping
both blocked. The extended stateful replay control pins each blocked cause and
its completed observation prefix. No model exhaustion becomes expected FAILURE.
The fixed recursion depth is a source-model over-approximation, not an exact
machine exception; changing its label cannot repair that semantic boundary.

The working alternate method is [the optional reference EVM replay](../../scripts/evm-reference/README.md).
It executes creation code and every original scalar vector on pinned
`@ethereumjs/evm` 10.1.3, Osaka, separately compiled legacy/viaIR bytecode from the
SHA-checked Solidity 0.8.38 compiler. It uses the upstream
`ExecutionFramework.h:275` message-execution gas allowance of 100,000,000,
without subtracting transaction intrinsic gas. Contract/initcode size caps are
explicitly disabled to match the pinned `EVMHost.cpp:418–441` test host's
code-deposit rule. No expectation, source byte, pipeline or vector is removed.
The Lake core and optional Bridge are unchanged by this separate npm package.

A five-million-instruction host limit and a 120-second per-fixture process cap
bound reference work; either exhaustion stays blocked. The recursive failure
observations are actual EVM stack overflows at 1,024 words, with empty return
data: legacy uses 29,131 / 28,963 instructions and viaIR uses
263,515 / 395,733. All eight vectors execute in each mode, including the calls
after the first failed call. This repairs executable fixture validation through
an explicit alternate method; it does not claim Lean coverage or a universal
compiler/model theorem.

The three cleanup fixtures require full dirty words across Yul local writes,
operator calls and return values. The existing source frontend only supports
canonical byte-buffer rethrow, which cannot express those operations. Their
Lean imports remain explicit exclusions. Reference execution retains and checks
all their observations, including `0x42`, `0x84`, and `0xffff`; truncating these
at a nominal uint8 boundary would change the actual expected results.

| Fixture (same `userDefined/` prefix as above) | Lean continuation | Reference legacy / viaIR |
| --- | --- | --- |
| `all_possible_operators.sol` | working / working | working / working |
| `all_possible_user_defined_value_types_with_operators.sol` | working / working | working / working |
| `attaching_and_defining_operator_with_same_function.sol` | working / working | working / working |
| `consecutive_operator_invocations.sol` | working / working | working / working |
| `fixed_point_udvt_with_operators.sol` | working / working | working / working |
| `multiple_operator_definitions_different_types_different_functions_separate_directives.sol` | working / working | working / working |
| `multiple_operator_definitions_same_type_same_function_same_directive.sol` | working / working | working / working |
| `operator_definition_shadowing_builtin_keccak256.sol` | working / working | working / working |
| `operator_parameter_and_return_cleanup_between_calls.sol` | excluded / excluded | working / working |
| `operator_parameter_cleanup.sol` | excluded / excluded | working / working |
| `operator_precendence.sol` | working / working | working / working |
| `operator_return_parameter_cleanup.sol` | excluded / excluded | working / working |
| `recursive_operator.sol` | recursion-resource blocked / blocked | working / working |
| `unchecked_operators.sol` | working / working | working / working |

Reference reports never overwrite or merge into Lean `working` lists. Their
stage is `evm-reference`, with source/archive/compiler, engine/lock/adapter,
compiler-input and creation/runtime-bytecode hashes; every vector, exception,
return byte string, instruction count and maximum stack height is retained.
Transaction-local warmth/original-storage caches reset between vectors while
successful account/storage changes persist and failing calls roll back.
Unsupported host reads, logs, settings, opcodes and unknown engine exceptions
remain blocked. Constructor failure bytes and earlier completed pipeline results
survive a later unsupported observation. Independent extraction directories
prevent verification races with the Lean runner.

The Decision investigation found the kernel reduction of
`sortedLe_covered`'s earlier exact-fragment branch, not an error in a changed
runtime rule. Its statement is unchanged. A local generic Boolean bridge proves
`Covered` from the already sufficient `quantCovered` disjunct, whose concrete
claim is still proved by `decide +kernel`. Keeping that bridge generic prevents
`simp` from reducing the closed expensive alternative. The isolated complete
coverage proof probe passed in 11.179 seconds.

Declaration-level flushed diagnostics then identified a separate expensive
native walk at `#eval verdict sortedLe` (20 arithmetic variables). The original
search was allowed to run beyond the former 900-second wall budget while its
exact input was inspected; no heartbeat, fixture process/fuel, or reference
instruction limit was raised. The broad validation wall budget was relaxed. Rather than
repeat that search at every build, `sortedLe_valid` proves the original formula
for every typed state by instantiating its premise at `2` and `5`.
`sortedLe_decision` combines that proof with the existing decision theorem and
checked no-hash reduction to prove the **exact equality**
`decideGoal sortedLe = .proved`. A subtype-certified string carries
`s = verdict sortedLe`, and the original `"proved"` output pin now evaluates its
value. The opposite `"refuted"` output is rejected by a kernel theorem. This is
cheap certified replay, not a claim that the native arithmetic search became
faster. Its isolated complete probe passed in 18.425 seconds, with only standard
axioms. No answer-existence claim replaces the exact verdict equality. The
module's opening documentation explicitly identifies this one replay exception;
all other compiled positive/negative verdict controls remain.

All original formulas, expected results and coverage statements remain, as does
`Elab.async false`: git history records that serial
setting in `20e30b13` as a stack-overflow fix. No representation, dependency,
semantic premise, heartbeat limit, axiom or `sorry` changes.

### Completed continuation validation (2026-10-27)

The real `lake build Solidity.Examples.Decision` passed in 1,228.830 seconds
(1,227 seconds reported for its module), beyond the old 900-second cutoff.
The original compiled `verdict sortedLe` also passed independently in 18.147
seconds when loading native code for the unchanged arithmetic implementation.
The same normalization probe measured 41.313 seconds in the interpreter and
3.914 seconds with native loading. This is a backend measurement, not a changed
arithmetic algorithm or proof budget.

[`scripts/check-native-arithmetic.sh`](../../scripts/check-native-arithmetic.sh)
reproduces that optional mode: it builds native code from the existing
`LinearDecision`/`VisitedSet` sources, generates an ignored alternate TOML with
only additional weak native-loading arguments, and schedules builds on one
thread. The ordinary configuration stays unchanged. The three dependent
example modules passed serially: Arrays 195.901 s, Memory 46.716 s, KInt
13.558 s. Arrays had an observed RSS of 12,250,688 KiB; the executor's memory
limit is 16 GiB. The cgroup OOM-kill count remained at its pre-existing value
of one: no additional OOM kill occurred.

The ordinary `LEAN_NUM_THREADS=1 ./run-lean.sh` then passed in 3.928 seconds,
reusing those checked artifacts. This is a **cached full gate**, not a claim
that all interpreter evaluations execute freshly in four seconds. It includes
the default library, TestSuite and frozen sort check. The frozen corpus also
passed (`check-corpus: ok`, unchanged 774-obligation partition).

One-thread and concurrently loaded reruns of the largest UDVT fixture hit the
unchanged 120-second process cap. Those blocked attempts are retained. Its
final fully isolated rerun with the environment's configured four-thread
scheduling passed both pipelines in 164.908 seconds, with the same 1,000 fuel,
120-second per-process cap, exact expectations and eight observations per mode.
Final Lean coverage is ten working fixtures, three assembly exclusions and one
abstract recursion-resource block. The separate reference EVM passes all
fourteen fixtures, 28 pipeline variants and all 78 observations.

All fourteen original adapter tests and fourteen optional reference controls
pass. Focused Lean replay/operator/ABI controls pass. Strict automation reports
491 automatic, 61 budgeted, 11 refuted and zero pending; reachability reports
667 reachable and zero orphans; layering reports 143 core modules and no
frontend reach. The four new Decision theorem axiom sets contain only
`propext`, `Classical.choice`, `Quot.sound`, as do the twelve earlier checked
sets. No new axiom, recovery site, `sorry`, heartbeat override or dependency of
the core was added.

Two unrelated audits retain baseline findings. The trust comparison reports
the same 25 inventory findings on `c247c849` and this continuation, with no
forbidden sites. The documentation-path check reports the **same nineteen**
missing references on a detached `c247c849` checkout and this branch, with
identical findings. The earlier thirteen-reference figure predates diagnostic
quotations embedded in the previous handoff's machine evidence; none is a new
missing reference introduced here. The baseline audit worktree was removed.

The final model SHA-256 is
`8c57f8874c6370ce6824a34ce9b47de18f8dcb3ef75dc547adb91e3e208ddaa4`.
The reference runner SHA-256 is
`54f60f857c89d3ff78a30ba61c60399c4214ac21c113ce1713254b5f130fe384`.
Compiler, archive and original adapter hashes remain those recorded above.
[group03-continuation.json](../../tests/upstream/group03-continuation.json)
contains every selected final report, retained retry reports, exact commands,
source/model/compiler/bytecode hashes, native library/source hashes, timings,
all sixteen axiom sets and check-log hashes. Logs remain under
`.lake/upstream/group03-resume/`. The previous handoff and its exported patch
remain preserved; implementation commit `0cd7a473` extends the existing lane.

Useful exact commands, after activation, include:

```sh
source /workspace/.setup/activate.sh
LEAN_NUM_THREADS=1 lake build Solidity.Examples.Decision
scripts/check-native-arithmetic.sh build Solidity.Examples.DecisionArrays
scripts/check-native-arithmetic.sh build Solidity.Examples.DecisionMemory
scripts/check-native-arithmetic.sh build Solidity.Examples.DecisionKInt
LEAN_NUM_THREADS=1 ./run-lean.sh
LEAN_NUM_THREADS=1 scripts/check-corpus.sh --solkey tests/migration/solkey/keyext.solidity.examples
node --test scripts/evm-reference/replay.test.mjs
```

Each exact upstream `--filter`, `--batch-size 1`, distinct `--out`, required
pipeline and original vector is recorded in the evidence. Native helper
artifacts are built from the same checked sources; their loading introduces
no proof oracle or `native_decide` axiom. No existing model or source-input
representation was refactored.

Independent read-only finder and skeptic reviews confirmed the final source,
constructor data, rollback/transaction boundaries, bounded-resource distinction,
all 78 reference observations and their hashes, exact Decision replay proof,
and the native helper's scope. Neither opened a Lean worker. Confirmed harness
issues were fixed and covered by positive/negative controls. The remaining
intrinsic scope is explicit: exact machine-resource failures and dirty scalar
Yul local-word/cleanup semantics. Reference agreement does not claim those Lean
features or a universal compiler/model correspondence theorem.

### Recursive operator diagnosis after be1e471f (2026-10-27)

This investigation retains the existing branch, five commits, all previous
reports, and both previous patch exports. The same connected managed executor
runs Lean 4.24.0 / Lake 5.0.0; the cached KeySort gate passed. No Lean MCP is
exposed, so per-file checks use the activated executor and `--tstack=131072`.
There is **no new Lean fixture pass**: ten fixtures remain working, three remain
assembly exclusions, and the recursive fixture remains blocked. Reference EVM
coverage stays separate. The large UDVT retry, Decision and completed broad
gates were not repeated.

The exact entry in `group03-continuation.json`, the earlier preserved reports,
and a new exact-filter rerun agree on required pipelines: legacy and viaIR.
Both current imports elaborate both public functions with no gaps. There is
**no raw Lean exception** in the current run: the error is the interpreter
outcome `.error .exhausted`, which replay reports as
“execution reached a model resource bound (including recursive unrolling); not
an EVM failure”. Each full sequence retains its first two successful unary
observations and blocks at the unchanged third vector,
`testUnary(uint256): 99999999999 -> FAILURE`.

The exhausted stage is **typed interpreter execution of the recursive bottom
frame**, not import dependency expansion, operator/call lowering, Lean elaborator
recursion, decision computation, or the loop-fuel limit. The immutable numeric
bounds are `recDepth = 1024`, replay loop fuel 1000 and fixture process cap
120000 ms. Neither heartbeat nor any other proof/resource limit changed.

The SHA-checked compiler's original AST identifies nominal `Uint#3`, pure free
functions `unaryCountdown#42`, `binaryCountdown#97`, `eq#119`, and public wrappers
`testUnary#132` / `testBinary#149`. Unary operator nodes 129 and 39 target 42;
binary nodes 146, 81 and 94 target 97; equality nodes 23, 59, 65 and 78 target
119. Thus the cycles are 42 → 42 and 97 → 97, with nonrecursive equality 119.
`Contract.callees` includes the resolved operator ID; its bounded `reach` stops
path cycles. `Body.expr` lowers that ID through the existing name map to an
ordinary function call. `isRecursiveC` recognizes those self-cycles.

`Arms.elabCallRet` checks one frame, then constructs the already-lazy
`recUnroll Prog.recBase step recDepth`. Recursive calls hold the next frame
behind a typed thunk (`RecFrame` / `Stmt.callRec`); quoting does not eagerly
expand 1024 bodies. `Prog.recBase` is `assumeFalse`, and `runF` / its compiled
twin map it to exhaustion. `TRun.call` propagates that error. The `callRec`
depth annotation is read by quotation, not runtime machine stack accounting.
The new [kernel controls](../../tests/upstream/RecursionResource.lean) prove
bottom exhaustion for every typed state and loop-fuel value, distinguish it
from revert, and pin recursive/ordinary call equality and depth-label
irrelevance. All four axiom sets contain only `propext`, `Classical.choice`,
`Quot.sound`; they prove no EVM stack-overflow claim.

For a direct comparison, an isolated diagnostic source removes the using
directive and replaces every alias with its explicit resolved free-function
call. It keeps nominal Uint, guards, checked subtraction, operands, returns,
and wrappers. Both sources are compiled with the same pinned compiler in both
pipelines and imported through the normal frontend. All four models import
both wrappers successfully. Each full sequence is blocked at the same third
vector. Separately, all eight original vectors are retained and run individually
for each model: statuses are working, working, blocked, working, working,
working, working, blocked. All six successful results are zero. These **32
individual diagnostics are not sequential fixture passes**; the fixture is
pure, so they isolate the binary obstruction without claiming to bypass the
blocked unary call. No observation is removed from the full rerun's input.

This comparison rules out an operator-specific cycle, wrong overload, missing
nominal identity or accidental eager host recursion as the cause of this
failure. Memoization can reduce elaboration work but cannot change the abstract
bottom's meaning; unary recursion also visits a different argument each time.
The unary input needs 100,000,000,000 countdown-function frames to reach zero
in an unbounded source evaluation. A closed-form return-zero proof would not
establish the expected machine failure. Existing `RecContract.base` accepts
exhaustion under both modalities, so a recursive source contract cannot provide
that runtime observation either.

A safe Lean pass requires additional **machine-resource semantics and a checked
connection to the compiled execution** (or Lean execution of the relevant
bytecode). The present `Evm.Machine` explicitly has no gas or stack-depth limit;
`Evm.Compile.inFrag` returns none for `callRec`, and `Evm.Correct` marks it
outside the simulation fragment. There is no typed stack-word accounting for
these pipeline-specific compiled frames or proof that a chosen source-unrolling
bottom is that concrete machine failure. The existing typed machinery safely
represents recursive source execution and inconclusive truncation; it cannot
safely manufacture the expected stack-overflow observation. Adding a distinct
machine halt and the corresponding accounting/correspondence proofs is new
semantic infrastructure, rather than an alias-lowering repair. No representation
refactor was undertaken. History was inspected: `1a7d5b0e` introduced shared
callee elaboration for size/checking costs; that infrastructure remains intact.

Exact commands (after activation):

```sh
node scripts/solidity-upstream.mjs verify
node scripts/solidity-upstream.mjs run --compiler /workspace/.setup/soljson/soljson-v0.8.38+commit.1835d247.js --filter test/libsolidity/semanticTests/operators/userDefined/recursive_operator.sol --batch-size 1 --out .lake/upstream/group03-recursion-trace/exact
node .lake/upstream/group03-recursion-trace/prepare.mjs
LEAN_NUM_THREADS=1 lake env lean --tstack=131072 .lake/upstream/group03-recursion-trace/Trace.lean
LEAN_NUM_THREADS=1 lake env lean --tstack=131072 .lake/upstream/group03-recursion-trace/Graph.lean
LEAN_NUM_THREADS=1 lake env lean --tstack=131072 tests/upstream/RecursionResource.lean
LEAN_NUM_THREADS=1 lake env lean --tstack=131072 tests/upstream/Replay.lean
node --test --test-isolation=none scripts/solidity-upstream.test.mjs
node scripts/check-automatic.mjs --strict
node scripts/check-orphans.mjs
node scripts/check-layers.mjs
```

The exact fixture command exits 1 for its blocked result; it did not timeout.
The diagnostic generator's two initial setup errors (missing optimizer-runs
provenance and a namespace whose final component was not original contract C)
are preserved as failed logs, then corrected. The actual source comparison and
kernel/replay checks pass. All 14 runner tests pass; strict automation remains
491 automatic, 61 budgeted, 11 refuted, zero pending. Reachability remains 667
reachable / zero orphans; layering remains 143 core modules / no frontend reach.
The documentation-path audit retains the same nineteen missing-reference lines
as the preserved baseline; no new missing path. At most two Lean processes ran,
with no Lean workers opened by reviewers.

No model, runner or previously checked source was modified; the model hash is
still `8c57f8874c6370ce6824a34ce9b47de18f8dcb3ef75dc547adb91e3e208ddaa4`.
The completed default library, Decision, TestSuite, frozen sort and corpus gates
above remain applicable and are deliberately reused. No historical source,
expectation, archive, result or previous evidence file changed. The new evidence
[group03-recursion-trace.json](../../tests/upstream/group03-recursion-trace.json)
retains exact reports, all eight input vectors, all 32 individual diagnostics,
source/compiler/model/AST hashes, diagnostic source/generator, kernel axiom
output, commands and check logs.

Independent read-only finder and skeptic reviews both traced the declarations,
ordinary-call comparison and machine-fragment boundary without opening Lean
workers. Neither found a safe local operator repair or a confirmed issue in the
controls. The skeptic specifically checked that the 32 independently initialized
diagnostics are not counted as full-sequence success. The remaining scope is
concrete machine-resource semantics/correspondence for the two failure vectors;
this milestone records diagnosis and controls, **not full Lean repair**.
