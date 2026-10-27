# Declarations and metadata

Integration status (2026-10-26): included in the shared checkout. Current
combined validation is tracked in [integration.md](integration.md).
Worker handoff statuses and isolated validation results below are historical;
they neither report the current combined checks nor establish full source support.

## M1: compiler-resolved metadata (2026-10-25)

`Frontend/SolcJson/Body.lean` resolves `type(C).name` from the contract
declaration's name and produces its UTF-8 string literal. `type(I).interfaceId`
XORs exactly the selectors of ordinary external/public functions declared in
`I`, including its own overloads and overrides. Inherited methods and
receive/fallback declarations contribute nothing.

Error selectors are four bytes; non-anonymous event selectors are 32 bytes.
Both come from solc's exact canonical ABI metadata and are resolved by
declaration ID, including qualified declarations with the same short name.
The parser returns `Fin (2^(8*bytes))`, carrying the ABI bound in its result.
Malformed widths/non-hex digits fail closed. Anonymous event selectors are
refused independently of the compiler's source validation. The source compiler
continues to reject invalid contexts such as an ambiguous overloaded method
reference or a public function's declaration-selector access inside its own
contract. No selector uniqueness or hash injectivity is assumed.

The compiler helper retains selector fields and additional declaration IDs
only where the source observes metadata. The frozen TestSuite fixture stays
byte-for-byte unchanged. Metadata inherits the frontend's existing validated
compiler/fixture boundary; this milestone adds no compiler-correctness theorem.
The source fixture uses the repository's SHA-pinned solc 0.8.34; the metadata
rules were checked against `Types.cpp` at the inventory's pinned 0.8.38 commit
`1835d247de183f23e7b0e2bc4a50732af525b77c`.

Static declaration selectors and `this.f.selector` fold directly. A dynamic
function selector uses a fresh pure helper consuming its receiver argument;
the existing typed call elaborator evaluates that argument exactly once in
its original expression position. Boolean and conditional arms remain lazy.
Unnamed input parameters now receive collision-avoiding names derived from
declaration IDs, so otherwise supported unnamed signatures elaborate. Unnamed
returns retain the existing return-frame naming convention.

The fixture covers contract-name bytes, interfaces with inherited methods,
selectorless entries and overloads, enum/value-type error parameters, tuple
event parameters, qualified errors, function selector/address projections,
overload calls and receiver effects. Its deliberately false interface-ID
assertion must remain pending. The Lean example retains kernel-checked
interface-ID and receiver-evaluation proofs and malformed/anonymous metadata
rejection cases.

### Review and validation

The read-only finder and skeptic reviewed importer metadata, compiler-field
retention and renaming. Confirmed fixes exclude selectorless interface entries,
preserve effectful receiver evaluation, and keep lazy receiver expressions in
their arms. An attempted rewrite of aliased function values was removed:
the existing function-value packer hashes model names, so renamed inherited
values need a separate source-signature representation change. Their suggested
overloaded-pointer example is rejected by the pinned compiler; inherited
aliases remain a relevant unsupported boundary. Neither review called Lean.
The follow-up finder also found that helper names could collide with a
generated local alias. Freshness now avoids generated local/state names as
well as original names; a shadowed-local regression is also tested through
an inlined call.
Only selectors with dynamic receivers add helpers. Static `this.f.selector`
keeps the existing literal form used by function-value proofs.
Generated helpers carry an `#internalEntry` marker in the existing width
metadata table, whose `#` separator cannot be a Solidity identifier. Internal
and external function-value construction, dispatch, and dynamic call-graph
analysis exclude them while direct generated calls still work. Filtering
preserves the original function-tag indexes. Kernel tests reject helper tags
and selectors. This is importer metadata, not a second state representation.
The `1a7d5b0e` history entry introduced body memoization for checking speed;
that memoization and segmented contract compilation are retained.
The final read-only skeptic confirmed that value construction, indirect
call-graph analysis and both dispatch forms respect the marker, while direct
generated calls remain available.

The final `./run-lean.sh` completed successfully: 579 library jobs, 241
TestSuite jobs and the frozen SolKey sort gate (377 taclets, 131 read-bearing
annotations). The three headline proofs depend only on `propext`,
`Classical.choice` and `Quot.sound`. Per-file MCP error diagnostics passed
for every edited Lean file. The frozen TestSuite AST is byte-for-byte
unchanged, and its no-Lean report/automation audits pass (491 automatic,
61 budgeted, 11 refuted, zero pending). The generated feature audit is current.
The final frozen corpus gate also passes: 774 obligations with no verdict or
generated-output drift. Detailed logs are recorded in the shared group status.
The documentation-path check retains its 13 pre-existing missing vendor/external
references; `git diff --check` is clean.
The existing function-type source suite still leaves `externalValue` pending.
It also stays pending with compiler selector fields removed, no generated
helpers, and original unnamed-return conventions; its expected `proved`
verdict remains unchanged. The contract reader at `3f5f3f4b` was also replayed
in a separate namespace against that original-selector AST: every lowered
contract/function field matched the current reader exactly. All other selected
function-value rows pass.
The new source suite has 13 proved rows, one internal helper row and one
deliberately pending false property. The modifier, inheritance and free/library
source tests pass. The metadata example built in 16 seconds both before and
after helper isolation. The no-build metadata source suite took 70.7 seconds
before isolation and 75.6 seconds after, while the final rebuild also ran;
this is not an isolated performance comparison.
The unfiltered orphan check reports 33 pre-existing scratch modules; the new
example is reachable. Layering remains clean. Existing artifact-cache hardlinks
for `KeySort.ilean` and `KeyTaclets.ilean` were read-only; their local build
copies were detached without changing the shared cache.

### Remaining declaration work

This milestone does not close the whole declaration group. Import/remapping
resolution across source units, exact synthesized public getters (including
struct omissions and interface overrides), inherited external function values
with renamed model declarations, broader `using for` forms, and remaining
constructor/immutable/entry-visibility distinctions still require dedicated
implementation and validation. Existing C3, base-body, modifier continuation
and constructor implementations were inspected but are not claimed as new
work here. Abstract-contract `.interfaceId` metadata is also still refused;
the implemented inventory family is `type(I).interfaceId` for interfaces.
Raw fallback bytes and observable event logs retain their declared exclusions.
The auxiliary contract-wide `#verify`/`#counterexample` tools may still display
synthetic helper obligations when invariants are present, and `#difftest` may
enumerate helpers. The source testing API uses source import rows and does not
include these helpers. This reporting cleanup remains separate from runtime
dispatch isolation.

The next getter milestone needs one shared ABI identity for source declarations
and renamed model functions: both getters beside storage roots and inherited
external function values need it. The pinned compiler's
`FunctionType(VariableDeclaration const&)` consumes mapping keys and ordinary
array indexes, returns bytes/string whole, and omits struct mapping/ordinary
array members. Getter functions returning references also need the world's
return-value interface; the existing external-call elaborator currently
accepts primitive returns there. These interfaces should be coordinated with
contract-world before adding a second getter-only representation.

## M2: public getter and source ABI patch (2026-10-26)

Worker handoff (historical): `patch_ready_unvalidated`. This milestone was produced outside the
checkout. No Lean, MCP, source prover runner or repository build was run by
the implementation worker. That is the historical preparation boundary;
current combined checks are tracked in integration.md. Feature inventory upgrades
still require the corresponding source-support evidence.

Public state variables synthesize ordinary function members beside their
storage roots. Mapping keys and ordinary array indexes become parameters;
terminal elementary values become results. A terminal struct keeps its
non-mapping/non-array fields in declaration order. Unsupported returned fields
cause refusal of the whole getter: bytes/string are **not** incorrectly
omitted as ordinary arrays. The implemented return/input subset is elementary
Boolean, address, integer and fixed bytes types. Nominal enum/UDVT/contract and
function-typed inputs/results, dynamic bytes/string keys/results, and nested
aggregate results remain unsupported. Existing `uint` constant/unwritten
immutable expression inlining is reused; narrow or fixed-byte constants not
recognized by that collector remain unsupported.

Getter members participate in the same dependency ordering, intrinsic
elaboration and self-call inlining as source functions. Scalar, mapping,
fixed/dynamic/nested array getters work through ordinary external self calls;
primitive struct tuples work through `try ... returns (...)`. Ordinary tuple
assignment from an external call and reference ABI returns remain separate
interfaces. Public variables overriding interface functions resolve through
solc's `baseFunctions` identity relation. Mapping key names are retained in
modern compiler fixtures so named arguments reorder into their declared order.
Bare identifiers retain storage identity: the separate external-member alias
table never turns a state read into a getter call or function value.

Array bounds need a distinct wrapper: the pinned compiler's public getter
reverts with **empty data** out of bounds, while an ordinary array read panics.
Each generated array step checks its index before reading or descending.
`require(index < path.length)` preserves the empty-data failure; a subsequent
ordinary indexed read is reached only in bounds. This was checked against
both pinned compilers and both pipelines. The source regression catches the
empty bytes and deliberately leaves a false panic-length property pending.

`FunDecl.sourceDecl` is defaulted source metadata. Its sums distinguish local
and ABI functions, selected and retained base bodies, getters, special entries
and implementation helpers. ABI selectors are `Fin (2^32)`. Canonical source
signatures are computed before enum/UDVT/contract/struct lowering; generated
model names are never selector inputs. Modern AST serialization retains all
public/external source selectors; legacy trimming stays unchanged and may use
an exact source signature when the selector is absent. Malformed selectors
fail closed. No hash injectivity or selector uniqueness is assumed. A public variable's
getter is recognized only as an external member (`this.x`/`c.x`): a bare
function-valued slot `x.selector` must not fold to its getter's selector.
The paired function-slot regression admits getter metadata and keeps a false
comparison with the actual stored selector pending. The rebased upstream's
typed stored-function projection path is preserved. Dynamic getter selectors
use the receiver-consuming helper, preserving an indexed receiver's bounds
panic even though the selector itself is constant.

Internal function values exclude external declarations, getters and special
entries. External values exclude source-local/free/library helpers. Selector
dispatch and direct self-body lookup admit only selected ordinary entries and
getters; retained overridden base bodies remain available to direct internal
calls. This metadata records declaration mutability but does not claim to fix
the existing erasure of mutability in function types. Foreign-world linking
must still consume source identity rather than a model alias; this patch does
not build the contract world or complete receive/fallback dispatch.

All generated function/getter/constructor aliases avoid source names, generated
local/state aliases and printed struct renamings. Constructor body declarations
and calls share one allocated name. Emitted constructor helpers join selector
helpers in `internalFuns` and receive implementation roles, so they cannot be
exposed as source function values or ABI entries. Regressions collide with the
actual getter/constructor IDs and with a printed struct-constructor alias.

### Review and validation handoff

The read-only finder and skeptic inspected the implementation without Lean.
The finder confirmed a dependency regression, fixed in the patch: adding getter IDs to
the call graph must not count bare state references as getter function values,
or ordinary bytes/nominal reads would depend on unsupported getters. Bare
identifier callees of stored function values also exclude getter identities.
`GetterReferences.localBytes` pins the ordinary-read case. The skeptic required
an inherited-function ABI encoding regression because `.selector` alone folds
compiler metadata before reaching the new function-value packer; the fixture
now uses `abi.encodeCall(this.inherited, ...)` and pins the alias's selector.
The patch was rebased onto the primary's `c48c52e7` merge, preserving its
new operator-alias and finite function-dispatch admission analysis. Stored
getter function-value dispatch is not claimed; its synthetic candidates need
integration with that separate analysis if it refuses such calls.
The independent compiler/EVM oracle found the getter bounds distinction above,
which is reflected in the generated guards and true/false source cases.

The standalone JavaScript oracle runs entirely in memory with optional
external reference dependencies; none are added to Lake. The worker ran it
with SHA-pinned Solidity 0.8.34 and 0.8.38, legacy and IR pipelines, including
three compiler rejection cases (missing array indexes and omitted struct
outputs). Its final results are recorded in the patch manifest. Those runs
validate Solidity reference behavior, **not** the Lean implementation.

Integrator checks:

- Run per-file Lean error diagnostics on Raw, Getters, Body, Contract, Import,
  Values, Stmt, Admission and the example, then review its theorem axiom sets.
- Run `node --test scripts/public-getters.test.mjs` and the existing declaration,
  inheritance/constructor, function-value, modifier and source-admission suites.
  The false getter, getter-panic-length, stored-selector comparison and constructor
  properties must stay pending.
- Run the existing layer/orphan, frozen AST, TestSuite, corpus and frozen SolKey
  gates. Keep unrelated pending source-admission or frame changes intact.
- Register `Solidity/Examples/Tactics/PublicGetters.lean` in `site/examples.json`.
  The patch worker was explicitly forbidden from editing that manifest.
- Measure import/check time before/after applying the patch. The new defaulted
  field touches low syntax and causes a broad rebuild; the metadata table is
  compiled once and existing segmented compilation/body memoization remains.
  It does not undo `1a7d5b0e`'s one-body-per-callee optimization.

This remains one connected milestone of an incomplete declaration group.
Imports/remappings and multi-source scope, broader using-for/operator linking,
reference-valued getters and tuple external returns, nominal getter types,
qualified custom-error reverts, receive/fallback/world registration and other
constructor/immutable/visibility distinctions still need dedicated work.

## Getter lowering follow-up

Public getter indexes now canonicalize explicit `uint256`/`int256`, including
synthetic array-index declarations without redundant compiler type descriptions.
Zero-argument member calls in local declarations and assignments use the normal
call expansion; the special push-result path remains reserved for `push()`.
The source ABI encodeCall reader consumes a getter's direct tuple of arguments
even though its declaration is a VariableDeclaration. It preserves actual byte
metadata and leaves exact signature/implicit conversion checking to the typed
native encoder; nested tuples are not flattened.

Narrow primitive external returns are supported for a statically `this` receiver
only after its typed self frame resolves. Success locals retain their widths and
ABI marker rows; explicit range checks reject invalid returned values before the
success body. These decoder failures revert the caller with empty data and are
outside that call's catch clauses. Unknown-address narrow returns remain refused:
world ABI bytesN words have padding/alignment that differ from typed self values.
No core run or proof rule changes, range-check removal, or verdict changes are
part of this follow-up. Existing getter bounds guards still precede storage reads
and use empty revert data. Enum getters remain explicitly unsupported, while
ordinary explicit enum conversion retains its membership/Panic(0x21) check.

Added regressions execute signed/unsigned/bytes self returns and byte layouts,
and show a failed narrow decode cannot be caught as a successful return. These
patch-worker changes have not run Lean diagnostics or builds; integration must
validate the changed frontend, grammar and elaborator, then PublicGetters.

### Self-return ABI representation review

The skeptic found that erased primitive agreement did not imply equal ABI
representation: a bytes2 self return bound as bytes4 must not reuse compact
0x1234, and a uint8 self return must not masquerade as bytes1. The typed-self
path now checks the callee's retained source result kind and the requested
result kind before inlining. Fixed byte widths must match exactly and byte/
integer crossings are refused. Numeric widths with the same signedness retain
the existing caller-side range checks, including safe widening. Function result
markers are compared before their signature information is erased.

Regressions reject bytes2-to-bytes4, bytes2-to-uint16 and uint8-to-bytes1 native
try bindings, preserve exact bytes2 layout, and execute uint8-to-uint16 widening.
The worker did not run Lean diagnostics or builds; current checks belong to
the combined integration recorded in integration.md. The change does not replace ABI encoding/decoding with casts.

### Caller modalities, prefix conversions and concrete execution

The initial getter examples incorrectly expected default diamond obligations to
close across external calls. The existing calculus deliberately returns false
for every try diamond, including self calls. These new source caller cases now
request explicit `@custom:key box`, as the existing FunctionTypes examples do;
this proves safety rather than termination. Diamond automation across external
calls remains missing. Separate kernel-checked concrete runF successes are
transported to the actual typed run via runF_approx for every positive caller.
Both false assertions retain concrete panic controls.

The frontend drops an unused bare scalar identifier only when its declaration
identity resolves to a VariableDeclaration and its scalar type is known. Calls,
unknown names and bounds-bearing expressions retain their evaluation. Dynamic
bytes-to-fixed-bytes casts evaluate the receiver once, extract at most N guarded
bytes and right pad short inputs with zero. Storage operands are materialized
first, so the N-byte extraction bound does not bound the preceding full copy. This bounded lowering uses existing typed
statements and checks the exact bytes marker; arbitrary uint8 arrays and direct
string conversions are refused. Explicit bytes(string) conversion remains valid;
both branches of a conditional must retain the bytes kind.
The converter stays under its original lazy branch.

The fixture was regenerated with the SHA-pinned Solidity 0.8.38 compiler and
retains real generated-name collisions after its new NatSpec declarations.
Additional concrete/independent EVM cases cover empty/short/leading-zero/long
prefixes, effectful receivers evaluated once and skipped lazy receivers.
The patch worker ran no Lean diagnostics or builds. The primary records combined
Lean and independent-oracle validation in integration.md.

### Getter catch-data and native run review

Getter self frames retain their generated empty-revert bounds checks. Ordinary
functions still receive withPanics instrumentation; applying that pass to a
generated getter had added unreachable Panic(0x32) alternatives to the syntactic
catch-data analysis, although its explicit bounds require already reverted
empty. Preserving the getter body's empty-revert convention removes those
invented alternatives without deleting any bound or changing the run rules.

The native NarrowSelf demonstrations now start at an explicit nonzero self
address. Their former default state used address zero and therefore reverted
before reaching either the callee or its decoder. The failedDecode example
now exercises its intended caller-side range check. The selector-receiver proof
uses the existing scoped leaf/closer replay for its remaining Boolean guard.
These patch-worker changes have not run Lean diagnostics or builds.

### Capturing prefix results

A fixed-byte prefix is a lowering builtin, including when it is the whole
initializer or assignment RHS. These two capture sites now hoist that builtin
whole rather than treating it as an ordinary callee and independently hoisting
its explicit bytes-kind witness. The prefix's own path validates the witness
before stripping it, then evaluates the receiver once. Exact byte-kind checks
remain in force. A native execution regression retains the valid explicit
`bytes4(bytes(text))` conversion from a string-backed memory reference.
No Lean diagnostics or builds were run by the patch worker.

## Upstream Group 06: finite library struct identity (2026-10-26)

This section records commit `615bd3fa`; the continuation below records the resumed repair.

Status: **partial repair**, on `task/group06-structs-libraries` from
`006fcd593f5beeb540e7adf2bc76de4638566924`. All 15 assigned fixtures were
reproduced first on that current master: all were broken in both required
pipelines, so none is an already-fixed case. The older imported results remain
historical evidence on `cadb628c`; they were not overwritten.

[Complete before/after evidence](../../tests/upstream/group06.json) retains each
exact fixture path, source SHA-256, original report hashes, both pipeline reports
and all observations, commands and wall times. Five fixtures now work in both
legacy and viaIR; ten remain broken, with no final adapter/resource block:

| Fixture basename | Before | After (legacy / viaIR) |
| --- | --- | --- |
| `internal_call_attached_with_parentheses.sol` | broken / broken | working / working (`10`) |
| `internal_library_function_attached_to_enum.sol` | broken / broken | broken / broken |
| `internal_library_function_attached_to_struct.sol` | broken / broken | working / working (`2`) |
| `internal_library_function_return_var_size.sol` | broken / broken | working / working (`7`) |
| `library_enum_as_an_expression.sol` | broken / broken | broken / broken |
| `library_struct_as_an_expression.sol` | broken / broken | broken / broken |
| `using_for_storage_structs.sol` | broken / broken | working / working (`7, 7`) |
| `array_of_recursive_struct.sol` | broken / broken | broken / broken |
| `lone_struct_array_type.sol` | broken / broken | broken / broken |
| `memory_structs_nested.sol` | broken / broken | working / working (`1, 2, 3, 4`) |
| `recursive_structs.sol` | broken / broken | broken / broken |
| `struct_reference.sol` | broken / broken | broken / broken |
| `mapping_contract_key.sol` | broken / broken | broken / broken |
| `nested_tuples.sol` | broken / broken | broken / broken |
| `tuple_assign_multi_slot_grow.sol` | broken / broken | broken / broken |

Called-function signature checks now include the final contract's existing
struct/enum declarations. They still exclude storage and initializers from that
temporary check and retain dependency-failure propagation. A bounded worklist
follows compiler-resolved function, modifier, operator-function and struct
references to discover foreign library layouts. It retains the previous lexical
ordering and does not traverse all members merely because a library is named.
Thus an unrelated mutually recursive library cannot poison a scalar contract.
All layouts still pass the existing validation and intrinsic elaboration.

Struct constructors and declared types retain declaration-ID lookup. Pushed
member and discarded native-member receivers now use canonical type names;
older fixtures may use an unambiguous short-name fallback. Equal short names
are not interchangeable. Generated struct names also avoid every declared or
renamed struct name: a real library declaration ID `4` must not capture a
source-declared `Box_4` and replace its `uint8` layout with `uint256`. The
`StructNameCollision.sol` regression returns `0` after unchecked increment of
`255` in both interpreter modes. Its false `256` property remains in the proof
controls. Redundant parentheses around a callee use the existing
`unparen` reader before attached-call classification, preserving the implicit
receiver argument and its single evaluation.

No core representation, rule, interpreter, callback semantics, proof limit or
external dependency changed. The existing soundness theorems remain in use;
this importer repair adds no compiler-correctness theorem or universal source
execution theorem. Runtime agreement below is observational evidence. No new
axiom, `sorry`, native proof or heartbeat override was added. The history's
`1a7d5b0e` shared-callee memoization and existing encoded struct representation
are retained; no representation refactor was undertaken.

The new `tests/solc/LibraryStructCalls.sol` controls retain storage/memory frame
ownership, distinct equal-name and equal-layout declarations, direct pushed
member writes, discarded pop references, nested parentheses, an operator's
library-type dependency and an unused mutually recursive library. Nine positive
calls complete with all assertions true in both interpreter modes, using the
repository source-test compiler 0.8.34. These controls are separate from the
assigned upstream tests, all of which use SHA-checked 0.8.38. The separate collision control returns zero in both modes. All twenty
mode-specific call observations are retained. Both false postconditions remain
in the source-proof controls.

### Reproduction and provenance

Source `/workspace/.setup/activate.sh` in `/workspace/solidity-lean`. The managed
runtime gate passes with Lean 4.24.0, Lake 5.0.0-src+797c613 and
`lake build Solidity.KeySort Solidity.Tools.Upstream`.
`node scripts/solidity-upstream.mjs verify` verifies all 11,622 archived files.
For each full path recorded in the evidence, the exact pattern is:

```sh
node scripts/solidity-upstream.mjs run \
  --compiler /workspace/.setup/soljson/soljson-v0.8.38+commit.1835d247.js \
  --filter "$fixture_path" --batch-size 1 \
  --out ".lake/upstream/group06-reviewed/$fixture_name"
```

Before reports are in `.lake/upstream/group06-before`; the intermediate broad
collection experiment is in `.lake/upstream/group06-after`; the first final
attempt in `.lake/upstream/group06-final` preceded the collision correction.
The reviewed reports in `.lake/upstream/group06-reviewed` are the final patch's
evidence and all have the same model hash. SHA-256 pins:

- compiler: `6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`
- archive: `9200f2a26b08be5b77faf877c44f5cfbf5ea95f1bccc45dae559d2fbc7cefb2d`
- runner: `c860ec034b8dbf26c632f45a0c52c215df9eda9fc2fd10e3c3f8b84f4a37d468`
- historical model: `c042a72f4d864a780a366ad4f27d148df0d7e213d33c37d4b6a51f0ad33710df`
- reproduced master model: `c86945ed62a18ffccf0b72b291c6271f44462f7b1d60b101e73fd2ec565c8699`
- final model: `c776b32765d9f61c86cd96337d1946debe06c7111f5efa5de8886beae5e88070`

Per-fixture reviewed wall times are 10.335–17.630 s, including archive
verification, compiler work and source import/replay. These are not isolated
interpreter benchmarks. An earlier first command took 180.479 s including a
frontend rebuild under a simultaneous cold source-proof build; it is not a
performance baseline. No speedup or history-scaling result is claimed.

### Validation, review and remaining work

Final upstream JavaScript regressions pass (14 tests). The five existing Lean
replay checks pass after refreshing their imports; an earlier concurrent attempt
reported an out-of-date target and was rerun. Strict automation passes with 491
automatic and 61 budgeted proofs, 11 refuted and zero pending. Reachability is
667 modules with no orphan; layering has 143 core modules with no elaborator
reach. The frozen TestSuite audit passes with 552 derived, 11 refuted and zero
pending. Frozen SolKey sort checking passes: 377 taclets, all 131 read-bearing
annotations covered. The source trust audit has 25 findings; comparing the
complete lists against unchanged `006fcd59` gives identical findings. Its
inventory was not refreshed.

Lean MCP diagnostics are unavailable in this thread. Configured per-file Lean
checks use `lake env lean --tstack=131072 FILE`: all three edited files pass,
and the final changed `Body.lean` was rechecked after the collision correction
(32.443 s). The nine library assertion controls prove; the collision assertion and its
returning function prove too. Both false postconditions remain `pending` with
open proof goals. These are kernel-checked declarations under the framework's
existing `cleanTail(storage) = true` reading, not a new all-state source theorem.
The framework checks that every public entry elaborates, takes no storage
reference and exposes no reference before using the reachable clean-tail
invariant, and rejects proof dependencies outside `propext`, `Classical.choice`
and `Quot.sound`. The exact readings/statuses/timings are in the evidence.
All final affected-source checks pass: file-level structs, own structs, free/
library calls, the updated hidden-library width case and both new control suites
(six selected JavaScript test cases). The final source controls contain eleven
proved obligations, two deliberately pending false properties and one internal
frame; all proved obligations report the clean reading. Long build/check logs
are retained under `/tmp/group06-*` and copied to
`.lake/upstream/group06-validation/` in the managed executor. The documentation
path checker retains the 13 pre-existing missing vendor/external paths; the new
milestone paths resolve. The reviewed
`lake build SolidityCorpus` hit the 600 s process limit at 233/257 jobs without
reported errors; its result is **inconclusive/resource-blocked**, and the parity
probe depending on that build did not run. The earlier broad attempt was stopped
as superseded when review found the width collision. The reviewed full
`run-lean.sh` gate also reached its 600 s limit at 246/649 jobs with no reported
errors. Its default library build is incomplete; the script's subsequent
TestSuite build was not reached. These broad checks are **resource-blocked**,
not passing or demonstrated semantic regressions. Neither an interrupted build
nor a timeout is counted as proof coverage or a passing corpus gate.

The required independent read-only finder and skeptic opened no Lean workers.
They confirmed the missing temporary type context and library layouts, then
identified unused-cycle pollution, ambiguous short receiver names, the operator
reference edge and the missing direct-push control. The final patch addresses
those findings. The skeptic subsequently confirmed a generated-name collision
that could collapse member widths; freshening and the real-ID wrapping control
fix that defect, and its independent follow-up found no remaining code issue.
The existing hidden-library overflow control now exposes its real false property
as `pending`, replacing the verified obsolete `unsupported` coverage expectation;
its source assertion is unchanged. The initial multi-function new proof-control
batch timed out at 300 s. It was not counted as passing and is retried one
function per batch with unchanged process and heartbeat budgets. The combined
push control was still expensive in isolation, so its alias/discard assertions
and two direct-push result assertions were split into three smaller controls.
Every original assertion and the sequential runtime observations are retained;
the final two new source suites pass.

Remaining scope is explicit: enum conversions require identity-safe enum model
names and bounds; type-only expression statements require structural validation
before no-op lowering; contract mapping keys require nominal ABI ranges and
source dispatch identity; nested tuple lowering must preserve simultaneous
snapshots, discarded RHS evaluation and pipeline ordering. The two recursive
array fixtures and recursive mapping fixture remain ordinary-model exclusions,
reported as broken import gaps rather than passing tests. The standalone graph
storage foundation does not establish ordinary source/interpreter agreement;
see [recursive-types.md](recursive-types.md). Source bytes, expectations, archive
pins and historical results are unchanged. No push or merge to master was made.

## Upstream Group 06 continuation from 615bd3fa

The resumed implementation preserves the original branch, commit and historical
reports. **Twelve of fifteen assigned fixtures now pass in both required
pipelines**, compared with five at `615bd3fa`. The seven repaired finite cases
are attached enum calls, library enum and struct type statements, the lone
struct array type statement, contract mapping keys, nested tuples and nested
byte tuple assignment. Their original sources, expected values, stateful call
order and every observation are unchanged. None was already fixed on the base
master. The full before, first-patch and continuation reports are preserved in
[Group 06 evidence](../../tests/upstream/group06.json).

Enum conversions now resolve the compiler declaration ID to a fresh model name,
so another enum with the same short name cannot supply its bound. Fresh names
reserve source names and explicit import renamings; the regression uses the real
`FiniteEnum.E` ID `4` with `Pair => enumType4`. Existing lexical enum declarations
remain available to specifications. Packed static enum members retain their
byte-kind conversion. Type-only statements are erased only after a structural
check accepts validated declaration references and literal array dimensions;
calls, ordinary variable members and runtime indexed reads are not erased.

Contract type nodes resolve by validated declaration ID to the existing address
lowering (a word with address metadata). The upstream JavaScript adapter checks
160-bit ABI-vector bounds; Lean replay also checks the address parameter marker
before dispatch, rejecting noncanonical inputs as blocked. Source declaration and ABI metadata remain attached.
The runtime adapter recognizes the canonical ABI signature as well as its
existing source spelling, and excludes internal/private functions and retained
base bodies before matching. A real source control distinguishes an internal
`f(FiniteAddress)` returning `1` from public `f(address)` returning `2`.
The maximum 160-bit contract key is included in the runtime controls. This is
compiler-validated lowering into the existing representation, not a claim that
distinct nominal source types become assignable.

Explicit nested tuple trees are matched and flattened together. Discarded
subtrees retain their leaves, and the existing intrinsic elaborator captures
all RHS values before any target write. New nested admission is limited to
literal and identifier leaves: calls/failing reads remain refused until their
nested evaluation order is established. Existing flat-tuple admission is
preserved. Tuple reference destinations now undergo the same exact shape check
as their temporary aliases before narrow whole-reference use is admitted.
Both incompatible width directions have pinned rejection diagnostics. Existing
alias restrictions, memory/storage ownership and calldata checks remain in force.

`FiniteTypeLowering.sol` supplies six positive source obligations, one false
property that remains pending, two intentionally unsupported failure/admission
controls, the explicit rename control and the internal/public overload control.
The final source reports record eight proved rows (including the repeated rename
control), one pending false property, two unsupported controls and one internal
function. The separate SHA-checked 0.8.38 runtime checks retain eighteen
observations across legacy and viaIR. The source proof runner uses its repository
0.8.34 pin. Runtime observations are not universal source-correctness theorems;
proofs use the existing kernel-checked clean-tail framework and its standard
axiom whitelist. No semantic rule, representation, proof premise, proof fuel,
heartbeat limit, dependency, axiom or `sorry` was added.

Independent read-only finder and skeptic reviews opened no Lean workers. The
finder requested reservation of explicit renamed type names and verified the
real-ID regression. The skeptic found that unrestricted canonical matching
could select the internal nominal overload; transaction dispatch now checks
selected ABI ownership first, and both synthetic replay and real-source runtime
controls distinguish the correct result. Their final admitted-shape review
found no remaining execution defect. The broad validation gates run serially
with `LEAN_NUM_THREADS=1`; exact final outcomes are recorded below after they
finish. Lean MCP diagnostics are unavailable; configured per-file Lean checks
and build invocations use `--tstack=131072`.

The six concrete enum-bound execution theorems in
`tests/upstream/EnumBounds.lean` use SHA-checked 0.8.38 ASTs for both pipelines.
They prove that the foreign two-member enum rejects `2`, its `1` returns `1`,
and the same-named local three-member enum accepts `2`. Their axiom prints use
only `propext`, `Classical.choice` and `Quot.sound`. The ordinary unbounded
`foreignRead(uint)` normal-return obligation remains pending, correctly: some
inputs fail the cast. This is not reported as a successful ABI panic-code check.
Together with the earlier new controls, source testing records nine proved rows,
two deliberately open rows, two unsupported admission controls and one internal
helper; the six concrete execution theorems are counted separately.

All four final configured per-file Lean checks pass (Body 8.515 s, Contract
16.085 s, Arms 52.222 s, Upstream 2.223 s, under concurrent serial build load).
The final replay passes nine checks, including canonical-overload ownership,
both width mismatches and exact blocking of the address `2^160`. Assigned
fixtures finish in the wall-time range recorded in the evidence; these include
compiler/import/replay and are not isolated performance benchmarks. The new
address guard refreshed the model hash and all fifteen fixture reports in the
separate `.lake/upstream/group06-resumed-address-final` directory.

Eleven of thirteen broader affected-source suites passed on the first run. The
narrow-width suite hit its 300 s aggregate process limit while a single existing
`pushArithInRange` proof took 156 s. Retrying one function per process passes the
whole narrow suite with unchanged limits and assertions. The byte suite finishes
but `Bytes.indexOutOfRange` stays pending. An isolated, unchanged `615bd3fa`
worktree reproduces that same pending result with no tool error: this is a
baseline automation gap, not a demonstrated new execution mismatch. Its test
still requires `proved`; no expected result was weakened. Both heavy suites now
use `batchSize:1`, retaining the existing 300 s per-process and proof budgets.
Earlier superseded builds, the out-of-date no-build attempt and a draft enum
control that incorrectly asked for a safety proof of a failing cast are retained
in logs; only the corrected final checks count as passing.

The assessment of a separate graph source fragment re-read the speed-related
history (`323951dd`, `3929cbc2`, `01dd890d`, `d0c13aba`, `2f41a68a`). Existing
encoded table certificates and recursor/match optimizations are unchanged.
The graph API's guarded declaration layout does not yet give an ordinary memory
heap or operation-preserving source-fragment correspondence; neither finite
unrolling nor an unproved alternate evaluator was added.

The three recursive fixtures still fail ordinary source admission in both
pipelines: `array_of_recursive_struct.sol`, `recursive_structs.sol` and
`struct_reference.sol`. They require recursive memory allocation/deletion or
schema-indexed storage aliases, plus operation-preserving correspondence. The
existing graph storage API and finite-layout bridge do not supply these ordinary
interfaces. No finite-depth unrolling, dropped observation or fixture-specific
substitute is used to report them passing. This lane therefore remains an
incomplete repair of the full fifteen-fixture assignment. No representation
migration was undertaken; the speed-related history and warning requirements
for such a migration remain applicable.
