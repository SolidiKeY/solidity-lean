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


## Group 05: upstream function values and dispatch (2026-10-26)

Task branch `codex/group05-function-dispatch` starts at `origin/master`
`006fcd593f5beeb540e7adf2bc76de4638566924`. The historical corpus results
remain unchanged: their model hash belongs to the adapter on `cadb628c`,
not this branch. The attached managed executor passed Lean 4.24.0, Lake
5.0.0-src+797c613 and `lake build Solidity.KeySort` after sourcing
`/workspace/.setup/activate.sh`. The archive verifier checked all 11,622
files. Reproductions use the runner's SHA-checked Solidity 0.8.38 compiler;
no source, expected output, archive, frozen AST or historical result is edited.

### Changes and boundaries

Replay resolves synthesized getters by their retained source signature and
getter role when no specification/report row exists. It preserves source names
exactly while canonicalizing scalar parameter spellings. A local function or
implementation helper with the same signature is not a getter. Constructor
initialization, call order, rollback, typed ABI arguments and all expected
observations continue through the existing replay path.

Nested function-return calls retain the function type from a named function
value or a captured call-value expression. Base-qualified and `super` internal
function values use the same declaration-identity maps as direct calls. A
base value therefore retains its base implementation rather than acquiring
the most-derived override. Discarded scalar member/index/parenthesized values
are captured at their lowered type, retaining supported operand evaluation and
bounds failures instead of printing a value as an invalid statement. Capture
names advance beyond source declarations and model aliases, so a source local
named `discarded1` is not shadowed. A replay control preserves that local and
checks an array operand side effect occurs once; wrong counter/output vectors
are rejected. Effectful `C(receiver()).f.address` projection remains an explicit
frontend exclusion with its expected observations retained in a separate control.

The four deployed-code fixtures' depth failures reproduce independently with
one 720-byte literal and no function dispatch. The import profiler took about
0.25 s before reporting that failure; it was construction depth, not divergent
runtime recursion. Grammar quotation now builds ordered byte-list leaves of at
most 32 bytes joined by a balanced, explicit `List.append` tree. The raw representation is
unchanged. Kernel proofs in `tests/upstream/ByteLiterals.lean` pin all 720
varying bytes, reject truncation and check an ordinary UTF-8 literal across
chunk boundaries; their axiom sets are empty. The existing one-body-per-callee
memoization, segmented compilation, candidate filters, function tags and all
proof/resource limits are unchanged. Grammar history showed no speed-oriented
change this undoes. No finite-dispatch candidate is erased to obtain a result.

Resource errors embedded in import rows, thrown exceptions or logged
warning/error diagnostics are blocked. All diagnostics are retained, and a
warning preceding a resource error cannot turn exhaustion into a demonstrated
semantic failure. Replay controls cover diagnostic order, getter roles and
source-name collisions. No statement, run, taclet or soundness rule changes;
the existing typed statements and their soundness theorems continue to apply.
These frontend observations are not a universal source-correctness theorem.

### Reproduction and remaining scope

The reviewable per-fixture evidence is in
`tests/upstream/group05/reproduction.json`: exact commands, fixture/source
hashes, model/runner/compiler/archive hashes, before/after statuses, every
required pipeline and all retained observations/gaps. Each exact fixture uses
`--filter`, `--batch-size 1` and its own output directory. Final validation and
long-log locations are recorded in `tests/upstream/group05/validation.json`.
The 24 assigned historical failures reproduce on current master as 12 working
and 12 broken in the pre-patch runner's raw labels. Four of those twelve are
caught resource-depth failures, not demonstrated semantic disagreements. The
patch's observational result is 19 working and five broken, each with legacy
and viaIR evidence. Twelve cases are explicitly already fixed;
seven are repaired here.

The four `deployedCodeExclusion` cases now reach the existing unsupported
reference-return function-type boundary (`bytes memory`) rather than failing
at literal elaboration. Their finite-dispatch/ref-return gaps are retained;
these are expected current coverage exclusions, not passing cases or proved
runtime disagreements. Source runtime-code membership and generated bytecode
exclusion are outside this interpreter adapter, regardless of fixture names.
`functionCall/calling_other_functions.sol` remains unsupported because the
assignment in its repeatedly evaluated loop condition needs a statement on
every iteration. It is a loop-lowering gap, not a function-value failure; no
condition effect or loop premise is dropped to make it pass. The final run
has no timeout/resource/host block; resource-classification controls remain
separate from those five coverage gaps.

### Read-only review

The AGENTS finder and independent skeptic opened no Lean workers. They confirmed
and prompted fixes for source-name canonicalization collisions, logged-resource
classification (including warning-before-error order), and insufficient byte
ordering coverage. The varying-byte and UTF-8 kernel controls replaced the
initial repeated-byte control. Their final focused review found no remaining
confirmed defect. No new axiom, unfinished proof, dependency or raised limit is
introduced. A final hostile-`Append` control found that overloaded `++` could
change the literal at its call site. Quotation now names `List.append`
directly; a kernel control first proves the hostile instance is active, then
proves the literal still contains its original bytes. The superseded broad
build log is retained separately; final evidence is regenerated after this fix.
Lean MCP diagnostics were unavailable in this thread; configured
per-file CLI checks and build logs supply the verification evidence instead.

### Per-fixture handoff

Both required pipelines completed for every row; full observations are in the
JSON evidence above. “Broken” is the runner’s coverage-gap label here, not a
claim that a Lean execution contradicted Solidity.

| Fixture below `test/libsolidity/semanticTests/` | Before | After | Classification |
| --- | --- | --- | --- |
| `constructor/store_function_in_constructor_packed.sol` | broken | working | repaired |
| `constructor/store_function_in_constructor.sol` | broken | working | repaired |
| `constructor/store_internal_unused_function_in_constructor.sol` | working | working | already-fixed |
| `constructor/store_internal_unused_library_function_in_constructor.sol` | working | working | already-fixed |
| `deployedCodeExclusion/library_function_deployed.sol` | broken | broken | expected-reference-return-exclusion |
| `deployedCodeExclusion/static_base_function_deployed.sol` | broken | broken | expected-reference-return-exclusion |
| `deployedCodeExclusion/super_function_deployed.sol` | broken | broken | expected-reference-return-exclusion |
| `deployedCodeExclusion/virtual_function_deployed.sol` | broken | broken | expected-reference-return-exclusion |
| `expressions/conditional_expression_functions.sol` | working | working | already-fixed |
| `functionCall/call_function_returning_function.sol` | broken | working | repaired |
| `functionCall/call_function_returning_nothing_via_pointer.sol` | broken | working | repaired |
| `functionCall/call_internal_function_via_expression.sol` | working | working | already-fixed |
| `functionCall/calling_other_functions.sol` | broken | broken | loop-lowering-gap |
| `functionTypes/address_member.sol` | broken | working | repaired |
| `functionTypes/pass_function_types_internally.sol` | working | working | already-fixed |
| `functionTypes/struct_with_functions.sol` | working | working | already-fixed |
| `immutable/internal_function_pointer.sol` | working | working | already-fixed |
| `inheritance/inherited_function_through_dispatch.sol` | broken | working | repaired |
| `inheritance/super_in_constructor_assignment.sol` | broken | working | repaired |
| `libraries/internal_library_function_attached_to_internal_function_type_named_selector.sol` | working | working | already-fixed |
| `libraries/internal_library_function_attached_to_internal_function_type.sol` | working | working | already-fixed |
| `libraries/internal_library_function_pointer.sol` | working | working | already-fixed |
| `structs/struct_storage_to_memory_function_ptr.sol` | working | working | already-fixed |
| `virtualFunctions/internal_virtual_function_calls_through_dispatch.sol` | working | working | already-fixed |

Shared changes are limited to function-value printing in
`Frontend/SolcJson/Body.lean`, type inference in `Syntax/Elab/Values.lean`, byte
quotation in `Syntax/Grammar.lean`, and observational replay in
`Tools/Upstream.lean`. Integration needs no unpublished lane or extra dependency.

### Validation details

Configured per-file Lean commands passed for all six changed Lean files; the
final `Body.lean`, replay and byte-literal checks were repeated after freshness
repair. `node --test --test-isolation=none scripts/solidity-upstream.test.mjs`
passes all 14 tests. Strict automation reports 491 automatic, 61 budgeted,
11 refuted and zero pending; reachability reports 667 reachable and zero
orphans; all 143 core modules remain separate from the elaborator. Frozen
sort checking parses 377 taclets and matches all 131 read-bearing annotations.
The frozen TestSuite audit retains 552 derived, 11 refuted, one excluded and
zero pending.

Affected source controls pass all 17 admission/replay tests and all nine getter
controls. The original full `FunctionTypes` positive/negative regression passes
in 252 s on a rerun with broad workers paused and unchanged limits. An earlier
contended invocation timed out and is retained as inconclusive, not passing.
The declaration-metadata source test retains its original failing expectation:
`errorSelector` is rejected by the baseline `solidity.functionMemberKind`
admission guard. The unchanged `Admission.lean` guard rejects error declarations
before `Contract.lean` reads the body; a direct current-scanner check confirms
the diagnostic. This baseline attribution uses code/AST identity, not a separate
baseline proof run. Its legacy pinned AST bypasses modern admission, explaining
why the pinned Lean example and freshly compiled source suite differ.

The source regression compiler is the existing SHA-checked 0.8.34 tool used by
`solc-ast.mjs`; assigned corpus reproductions use the separate pinned 0.8.38
compiler throughout. The trust source inventory has the identical 25 findings
before/after this patch. The documentation path audit retains its 13 existing
missing vendor/Eqns references. Neither is represented as a passing global gate.
The executor's 16 GiB cap required stopping a concurrent corpus build and
rerunning it serially; its probe output and interrupted build log are retained.
Timings include contention and scheduling pauses and are not isolated benchmarks.

The existing `TrustAudit.lean` check passes: all 468 headline theorems use only
the standard axioms. The new literal controls separately pin empty axiom sets.

The broader inheritance/call suite passes 12 of its 13 tests after the original
base-constructor negative-control test is rerun without contention. Its full
`RevertData` source-contract invocation still reaches the original 300 s wall
limit. Individual checks retain every one of its ten original asserted
properties and the same proof limits in `tests/upstream/group05/revert-properties.json`.
`reasonBytes` and `reasonOfBranch` retain open proof goals; they are not relabeled
as expected failures or passing cases. Read-only path inspection finds that the
new lowering branches are not selected by `reasonBytes`, but this does not
establish a baseline proof failure. These broader validation gaps remain
unresolved and separate from the 24 assigned fixture results.

The completed individual revert-data checks total six proved, three open goals
(`reasonBytes`, `reasonOfBranch`, `reasonPastCustom`) and one resource block
(`externalReason`). All ten retain their original expected `proved` verdict.

The full frozen corpus gate passes without updating pins: all 774 obligation
classifications reproduce and all 257 Lean build jobs complete. The complete
Lean build log is retained as `.lake/upstream/group05-corpus-build-final.log`.

The separate `lake build SolkeyTestSuite` gate passes all 249 jobs, including
suggestion replays. The fully serial official default-build retry reaches its
45-minute wall budget in unchanged `Examples/DecisionArrays.lean` at 644/649;
`Examples/Decision.lean` passes in 966 s. No Lean errors were reported, but the
full default build remains blocked and is not counted as passing.
The frozen sort, full frozen corpus, replay and theorem-axiom gates passed
separately. No proof limit was raised; these timings are not controlled benchmarks.

Final read-only finder and independent skeptic reviews verify all 67 completed
log digests and all 24 fixture/report/source/model hashes. Historical inputs
and expected verdicts are unchanged. Both found no confirmed handoff issue
and opened no Lean workers; the unresolved proof and resource gaps above remain.

### Group05 resumed repair (2026-10-27)

The existing lane and commits through `a4c84673` were preserved. The five
remaining original fixtures required internal `bytes memory` function returns
and an effectful unannotated `while` head. All 24 assigned fixtures now agree in legacy and viaIR (70 ordered
observations): 12 were already fixed on the starting master, seven were fixed
on the previous lane, and these five complete the remaining repair. The final
combined evidence is recorded separately
in `tests/upstream/group05/resumed-reproduction.json`, leaving the earlier
19/24 milestone and historical upstream results intact.

The function-type component grammar retains data locations. Admission and the
native signature agree on the implemented boundary: internal, zero arguments,
one `bytes memory` result. Reference arguments, external reference-return ABI
calls, and other reference kinds still fail closed. The dispatcher captures
the selected function once, keeps finite source-tag candidates and scope
checks, and uses existing intrinsically typed memory-call/alias binding with
a shared destination. Existing per-callee body memoization is retained; no
core statement or state representation changes. The destination uses the
existing memory allocation, not a scalar encoding of a reference. Exact
Panic(0x51), independent returned memory, pointer mutation during a call,
negative byte assertions and rollback have kernel/replay controls in
`tests/upstream/FunctionDispatch.lean` and production source controls in
`scripts/finite-dispatch.test.mjs`.

Abstract source declaration identities remain in the reader metadata, while
execution uses the resolved concrete body. Only explicitly `implemented=false`
abstract declarations with a verified concrete alias can omit a nonexistent
body from execution dependencies. The finder caught that missing body metadata
alone was insufficient evidence; this was fixed and a malformed concrete-base
negative control added. Ordinary virtual, static-base and super value
references use the same resolution as their rendered bodies. Concrete base
candidates continue to participate in admission. The modern AST adapter now
retains explicit implementation metadata for this new memory-return family;
legacy and primitive-only normalization remain unchanged. Both abstract and
malformed concrete production controls pass.

An unannotated effectful `while (c)` lowers to an iteration-head test with a
synthetic break before its original body. Existing jump lowering then preserves
continue, break, return, final-false effects and short circuiting. Annotated
loops retain their existing path. The obsolete unsupported-effectful-head pin
in `Solidity/Examples/Tactics/Loops.lean` becomes a positive kernel execution
check on the same loop, including its final increment. Upstream sources,
expected observations, default loop fuel and proof limits are unchanged.

The earlier default-build interruption was profiled, rather than treated as
an unavailable host. All three DecisionArrays kernel certificates finish;
the compiled live-length verdict entered an expensive width-11 arithmetic
walk for a goal already available as a conjunct of an implication hypothesis.
`Solidity/Calculus/LinearHypotheses.lean` adds a bounded proof-producing
propositional fast path. Every success carries validity; failure retains the
original arithmetic/countermodel fallback and its hashed graph walk. History
`5154e4e9` records that walk's speed rationale and it is preserved. The three
unchanged isolated array verdicts return proved/refuted/proved in under one
millisecond of measured compiled evaluation after this change; this is not a
whole-build timing claim. No new axiom, `sorry`, heartbeat or recursion-depth
limit is introduced. The skeptic independently checked conjunction projection,
implication introduction, normalized-validity transport and unchanged fallback.

Lean MCP diagnostics were unavailable in the exposed tools. Configured CLI
checks and full logs are used instead. The final validation manifest records
commands, timings, source/model hashes, proof axiom pins, resource results and
remaining baseline limitations. Runtime agreement remains observational
evidence; deployed bytecode inclusion/exclusion, gas and code generation are
outside these functional replay observations.
