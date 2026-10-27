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

## Group 08 source-lowering repair (2026-10-26)

This is a **partial repair**, not completion of the declaration group. The branch
`codex/group08-source-lowering` starts at current `origin/master`
`006fcd593f5beeb540e7adf2bc76de4638566924`. All 23 assigned historical rows were
reproduced before editing and were still broken. Final isolated runs have **20
working, three broken, zero blocked**, zero already-fixed cases and zero expected
exclusions. Every working fixture agrees in both required pipelines with all
observations retained. Runtime agreement is observational evidence, not a
universal compiler/lowering correctness theorem. Compiler diagnostics remain
reference-solc checks, not Lean coverage.

[Before/after evidence](../../tests/upstream/group08-results.json) retains exact
commands, every pipeline, gap and observation, source/expectation SHA-256 values,
report hashes, compiler/archive/runner/model hashes and execution limits. The
historical `tests/upstream/results/`, upstream bytes and pinned archive are
unchanged. The historical import was produced on `cadb628c`
(model `c042a72f4d864a780a366ad4f27d148df0d7e213d33c37d4b6a51f0ad33710df`);
that assignment evidence is separate from fresh task-base reproduction.
Fresh baseline model SHA-256:
`c86945ed62a18ffccf0b72b291c6271f44462f7b1d60b101e73fd2ec565c8699`;
patched model SHA-256:
`85a5997f85830ba8411aebf339c313668060eea14a36ee032db895a01a6839a7`.

The source changes reuse existing intrinsic statements, typed roots and proof
rules. Local `delete` emits assignment of the type's default. Duplicate lexical
declarations receive collision-avoiding names by compiler identity, preserving
outer reads before activation and within initializers. Narrow/fixed-byte
constants retain source casts; literal narrow immutables retain their source
values. Qualified state accesses resolve only lineage contract identities and
retain dropped-declaration refusals. Parentheses preserve super/UDVT identities.
Static declaration-reference statements with no runtime receiver are discarded;
object/indexed receivers and calls retain evaluation or explicit refusal. Foreign
struct discovery follows referenced identities transitively, stopping at a fixed
point. Invoked foreign modifiers retain their defining lexical scope, bodies,
admission dependencies and payment/call analysis. Unrelated foreign declarations
do not expand selected supported shapes. Foreign-modifier-local struct types can
still fail closed.

Computed immutable initializers retain deployment roots even when their values
are never read. Unsupported declarations with initializers remain in admission
and block deployment rather than disappearing. Folded literals use deployment
defaults before their declaration initializes. Nonphased initializer calls that
would reach a future folded immutable through a shared runtime body are refused;
that boundary is pinned by a negative control. Known implicit-constructor gaps
retain their admission diagnostics in an explicit refused constructor row. Late
native-elaboration failure of the complete initialization contract also produces
a refused row; neither path can warn and silently deploy defaults. Synthesized
phased constructors retain direct/transitive initializer callback metadata.

Inheritance needs distinct initialization schedules. The import passes the
validated pipeline provenance to the frontend. Legacy retains its existing
all-initializers-before-constructor-arguments schedule. For viaIR inheritance,
immutable values retain typed roots; constructor arguments execute derived to
base, then each owner's initializers and constructor body execute base to derived.
The traversal includes owners with implicit constructors and synthesizes a
constructor when necessary. Initializers are rendered once; shared callees
remain shared, with their admission/call dependencies retained. Pinned compiler
IR inspection confirms base-before-derived initialization and argument-before-
base-initialization in the review counterexamples; this inspection is not an EVM
execution theorem. Testing imports also expose inherited public/external ABI
entries by declaration identity, excluding overridden and internal helpers.
The original `multiple_initializations.sol` now replays inherited `get()` at 255
in both pipelines; the test does not substitute a wrapper observation.

ERC-7201 arguments with an exact validated source string type retain that kind
through the existing explicit string conversion. This repairs inline string-array
indexing without relaxing native bytes admission or changing user-defined
functions sharing the builtin name. Arguments occur once at their original
expression positions.

Storage mapping alias assignments now retain their full declared key/value
shape; RHS shape equality is checked separately and mismatched widths remain
refused. Existing typed `forceArg` snapshots preserve the RHS reference yielded
by assignment and a mapping receiver before an effectful key rebinds its alias.
The skeptic caught `(m=n)[(n=a)[0]]=7` in the first metadata-only probe; the
corrected snapshots write through the original reference and are pinned alongside
bare receiver rebinding, single index evaluation, width-sensitive overflow and
rollback. This is restricted to mapping aliases, not a general reference-capture
refactor. Snapshots add typed locals; the possible checking cost was disclosed.
History traces the shortcut to W8.1 (`30611d7c`), with a no-rebinding assumption,
not a separately documented speed rationale. Callee bodies remain shared.

`mappingAssignmentShape` proves syntactic metadata propagation; admission checks
RHS equality independently. `snapshot_rebind` proves preservation of the fresh
typed alias under a later rebind of an older local. These reuse existing typed
rebind/run soundness and do not establish compiler equivalence. Guarded axiom
reports are respectively `propext`, `Quot.sound` and `propext`, `Classical.choice`,
`Quot.sound`. Kernel/source controls live in `tests/upstream/MappingDeclarations.lean`;
source replay checks both pipelines and preserves the pre-failure state.

No core representation, run semantics, taclet, external dependency, proof limit
or `maxHeartbeats` setting changes. No obsolete SolKey reader changes. Before
adding viaIR deployment roots, the possible checking cost was disclosed and git
history inspected: immutable folding (`fa96f08d`) had no recorded speed rationale;
the one-body-per-callee optimization (`1a7d5b0e`) remains intact. Factoring
initializer rendering out of the large importer kept elaboration within the
existing heartbeat limit after an intermediate deterministic timeout; limits were
not raised. General effectful loop conditions and all source-printer forms are
not claimed supported by this patch.

| Fixture basename | Before | After (legacy / viaIR) |
| --- | --- | --- |
| `abi_functions_member_access.sol` | broken | working / working |
| `as_function.sol` | broken | working / working |
| `assign_at_declaration.sol` | broken | working / working |
| `assign_type_info.sol` | broken | broken / broken |
| `c99_scoping_activation.sol` | broken | working / working |
| `crazy_elementary_typenames_on_stack.sol` | broken | working / working |
| `cross_contract_types.sol` | broken | working / working |
| `delete_local.sol` | broken | working / working |
| `delete_locals.sol` | broken | working / working |
| `erc7201_param_array_string_literal.sol` | broken | working / working |
| `function_modifier_library.sol` | broken | working / working |
| `function_modifier_library_inheritance.sol` | broken | working / working |
| `in_parenthesis.sol` | broken | working / working |
| `keccak256_optimized.sol` | broken | working / working |
| `mapping_local_compound_assignment.sol` | broken | working / working |
| `multiple_initializations.sol` | broken | working / working |
| `packed_storage_structs_enum.sol` | broken | broken / broken |
| `state_variable_local_variable_mixture.sol` | broken | working / working |
| `state_variable_under_contract_name.sol` | broken | working / working |
| `super_alone.sol` | broken | working / working |
| `super_parentheses.sol` | broken | working / working |
| `typed_multi_variable_declaration.sol` | broken | broken / broken |
| `wrap_unwrap.sol` | broken | working / working |

Remaining roots, without weakened expectations:

- `assign_type_info`: compiler creation/runtime bytecode constants are unavailable
  in the current constant representation. They must not become runtime slots.
- `packed_storage_structs_enum`: struct validation does not resolve enum members
  through its struct-only dependency table. A repair must retain enum ranges.
- `typed_multi_variable_declaration`: tuple declaration printing fails first. An
  isolated lowering probe preserving explicit storage declarations then exposes
  `storage` on a function with several returns in both modes. The intrinsic
  multiple-return call-frame gap remains; removing `storage` would change provenance.
  The failed probe is retained outside the patch, not counted as coverage.

### Reproduction and validation

Use the attached managed executor at `/workspace/solidity-lean`:

```sh
source /workspace/.setup/activate.sh
lean --version
lake --version
lake build Solidity.KeySort
node scripts/solidity-upstream.mjs verify
```

The concrete runtime gate passes: Lean 4.24.0, commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`; Lake 5.0.0-src+797c613; KeySort
build succeeds. Snapshot verification checks all 11,622 files. The runner's
SHA-checked compiler is
`/workspace/.setup/soljson/soljson-v0.8.38+commit.1835d247.js`, SHA-256
`6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`.
For every exact path in the evidence file:

```sh
node scripts/solidity-upstream.mjs run \
  --compiler /workspace/.setup/soljson/soljson-v0.8.38+commit.1835d247.js \
  --filter EXACT_PATH --batch-size 1 \
  --out .lake/upstream/group08/BASENAME-handoff
```

Baseline directories use `BASENAME` (except `delete_local-before`); final reports
use `BASENAME-handoff`. Intermediate after/final/stable/verified/audited/reviewed/sealed and
phase-exploration reports are not merged into final evidence. Every final run
uses timeout 120,000 ms and loop fuel 1,000. No limits were raised. All final
model hashes agree. Logs/timings are retained under `.lake/upstream/group08/`.
Initial overlapping Lake writes produced code 135 before fixture verdicts;
sequential retries succeeded and those process failures were never called passes.
An environment reconnect interrupted an earlier broad build; its partial log is
not a successful final gate.

The `lean-verify` workflow was read. No Lean MCP diagnostics tools are exposed;
configured per-file `lake --quiet --no-build lean FILE -- --tstack=131072`
checks and Lake builds were used. Body, Contract,
Arms and Import build successfully. Final Contract build: about 21 seconds;
Body: 8.3 seconds; Import: 6.4 seconds. The earlier Arms check took about 78 seconds. Final declaration controls take 17.722 seconds, mapping controls 3.197 seconds;
existing replay checks take 2.937 seconds (cached imports).

`tests/upstream/Declarations.lean` proves universal agreement of emitted local
assignment with typed `setLocal` of `PrimTy.dflt`; its guarded axiom report is
exactly `propext`, `Classical.choice`, `Quot.sound`. Kernel controls cover unsigned,
signed and Boolean deletion, false preserved-value claims, one evaluation of an
incrementing index and an effectful storage receiver. Negative controls reject
non-place deletion, including hoisted `delete make()` and `delete x++`, and keep
storage-pointer deletion refused. Source controls pin stateful calls, signed
immutables, lexical activation, packed byte widths, unread effectful initialization,
255 versus omitted-effect 253, direct forward defaults, unsupported initialization
refusal, transitive struct/modifier admission, inherited ABI override/visibility,
legacy/viaIR construction phases, implicit constructors and string-array ERC-7201. An unread unsupported initializer
with an unrelated matching output still refuses implicit deployment. Paired
callback/pure metadata controls check synthesized constructor classification;
they do not execute an unavailable external host.
Each positive replay has a false-observation negative; raw bytes remain refused
without an explicit string conversion. No new axioms or `sorry`; no universal
source-lowering theorem is claimed.

Final managed-executor gates (exact commands, durations and log hashes in
`tests/upstream/group08-validation.json`):

- `bash run-lean.sh`: passed (exit 0, 6035.157 seconds, `LEAN_NUM_THREADS=2`).
- `lake build SolidityCorpus`: passed (exit 0, 45.124 seconds, `LEAN_NUM_THREADS=1`).
- `bash scripts/check-corpus.sh`: passed (exit 0, 13.248 seconds, `LEAN_NUM_THREADS=1`).
- `node --test --test-isolation=none scripts/declarations-metadata.test.mjs scripts/test-solidity.test.mjs`: failed (exit 1, 3787.667 seconds, `LEAN_NUM_THREADS=1`).

The runtime gate, 11,622-file snapshot verification, 14 runner tests, both new
per-file controls, existing replay checks, strict automation, module reachability,
core layering and frozen TestSuite audit pass. The initial Constructors per-file
precheck reported a stale SurfaceNotation dependency (exit 3); the final full
build successfully recompiles the Constructors regression. An earlier corpus
attempt was killed with exit 137 and is retained as a resource-blocked attempt;
the final single-worker retry above has its own result. No limits were raised.

The affected source API suite finishes with 46 passed and 15 failed tests (not a
passing gate). Nine failures reproduce on the exact task base in the isolated
`codex/group08-baseline-check` worktree: metadata selectors, assembly status,
malformed NatSpec diagnostics, byte indexing, modern full-source TestSuite
recursion/code generation, a stale pending reference-copy expectation, omitted
specification status, `tryScopeExit`, and `tryArgumentSideEffect`. The source API's
modern TestSuite discovery resource failure is distinct from the passing frozen
TestSuite build/audit and corpus gate. Three source subprocesses exit 135 for
PushSources, MemoryPush and StorageReturns; focused unchanged-model retries
have no errors and match all 36 existing expected rows and clean readings,
including negative observations. The original process failures remain in the log.
Calldata, Hashing and RevertData each hit the unchanged 300-second timeout and
remain resource blocked/inconclusive. No expected statuses or proof limits were
changed to make these checks pass. All baseline comparison commands and focused
report hashes are in the validation manifest. The final runtime and Constructors
per-file rechecks pass. A transient environment-unavailable notification occurred;
the same managed executor and original source-suite process survived it.

The documentation-path check still reports 13 missing vendor references. The
citing files are unchanged on the task base and all targets were absent there;
`sealed-doc-paths-baseline.json` in the log package records that baseline proof.
This unrelated check is a baseline failure, not a pass. Historical results,
upstream source/expectation bytes, archive and frozen SolKey inputs are unchanged.

Selected long logs, exact fixture reports and rejected probe evidence are packaged
in `.lake/upstream/group08/group08-logs.tar.gz`; the reviewable per-fixture record
is `tests/upstream/group08-results.json`.

### Read-only review and integration

Finder and independent skeptic reviews inspected all changed areas without
opening Lean workers. Confirmed findings were fixed: repeated struct closure
scans, non-place deletion after hoisting, omitted unread immutable initializers,
forward folded reads, inherited virtual/argument phase ordering and missing
inherited ABI entries, warning-only implicit initialization refusals, and
initializer callback metadata, and mapping-alias snapshot provenance. The late native-elaboration warning branch was
closed structurally, without claiming a reproduced source counterexample for it.
The final phased schedule and string-kind boundary had no
remaining confirmed findings. Earlier conservative phase exclusions were replaced
by explicit scheduling and positive/negative controls. The three assigned gaps
above and the nonphased shared-callee forward boundary remain explicit.

Shared implementation changes are limited to Import, Body, Contract, Arms and Values;
integration must carry them with the controls. The existing Constructors regression
and source API test now require an explicit refusal row instead of the obsolete
warning-only behavior; the empty-initializer and non-passing verdict checks remain.
The source API's warning-handling comment is aligned; its behavior is unchanged. No unpublished changes from other groups
are assumed. No push or merge to master is performed.

## Group 08 resumed remaining declarations (2026-10-27)

This continues `62338a6f` on the same `codex/group08-source-lowering` lane;
its earlier patch, logs and evidence above remain historical artifacts. The
[new exact before/after record](../../tests/upstream/group08-resumed-results.json)
compares that lane's 20 working / 3 broken result with **23 working / 0 broken /
0 blocked**. Every fixture was rerun with its exact path, `--batch-size 1` and
a distinct `resume/sealed-*` output directory. All 46 required legacy/viaIR
variants retain all 58 observations, unchanged expected results and source bytes.
The compiler remains SHA-checked 0.8.38; the new record includes model, runner,
compiler-code adapter, report and log hashes. This is observational agreement,
not a universal correctness theorem or generated-EVM validation.

The three actual roots and the bounded repairs are:

- `constants/assign_type_info.sol`: static `type(C).creationCode/runtimeCode`
  requires compiler artifacts, rather than runtime account code. A demand-driven
  second compiler invocation retains source/settings/pipeline and requests the
  exact identified contracts' full linked bytes. The Lean input boundary checks
  source/compiler hashes, settings, unit, declaration identities, duplicate
  names/IDs, lowercase hex and a 128 KiB materialization bound. It does not
  authenticate the compiler or prove its output correct. Ordinary inputs avoid
  code generation. Historical AST-only fixtures retain explicit exclusions for
  missing artifacts. Length folding uses the same byte parser as the retained
  complete byte literal; initialized runtime bytes remain deployment state.
- `storage/packed_storage_structs_enum.sol`: validated enum identities are
  terminal struct dependencies. Existing uint8 carrier metadata retains widths
  through struct printing, locals, indexed values and arrays. Identity-resolved
  native enum conversions check cardinality before exposing the uint8 carrier;
  a same-named shadow enum cannot supply another declaration's range. Whole
  enum arrays retain ABI array padding. Enum/composite `abi.decode` targets
  remain refused because the native decoder lacks nominal cardinality checks.
- `various/typed_multi_variable_declaration.sol`: a restricted source helper
  uses the existing shared typed storage-return frame. Admission requires a
  nonvirtual internal/private helper with no modifiers/specification, a single
  lineage, one terminal explicit tuple return, exactly one storage result and
  closed, source-range-checked scalar literals for the other slots. Every use
  must be a matching tuple declaration. Unit literals use the existing constant
  evaluator. The caller executes the helper once, captures a fresh typed alias,
  then activates source targets in order; holes retain effects and reference
  validation. Other mixed frames remain refused. There is no heterogeneous core
  frame, body duplication or new core representation; the shared-body speed
  decision recorded at `1a7d5b0e` remains intact.

`tests/upstream/RemainingDeclarations.lean` and both SHA-pinned source fixtures
exercise full byte content and storage initialization, malformed artifacts,
enum local/indexed/whole-array widths and shadowed ranges, malformed enums,
nominal decode refusal, mixed tuple holes, call counts, units and rollback.
Positive replays have false-observation controls. The universal scalar binding
lemmas establish preservation of the captured alias and the supplied scalar;
they use only `propext`, `Classical.choice` and `Quot.sound`. The static length
agreement lemma uses only `propext`. These local lemmas are not a universal
source-rewrite theorem. No new axiom, `sorry`, proof-limit increase or changed
historical expectation is involved. The optional Bridge remains separate.

The three previously timed-out source tests explicitly request one obligation
per subprocess, retaining all rows and the existing 300-second bound. The
shared API retains its existing default of 32; unrelated suites retain their
original scheduling. Profiling isolated the previous
Calldata aggregate timeout: `sliceLength` proved in 8.657 seconds,
`sliceRead` remained pending in 91.951 seconds and `sliceOfSlice` remained
pending in 92.757 seconds, each with no tool errors. Pending remains pending.
This changes scheduling, not proof premises, search budgets or expected results.
Development attempts made while dependencies were changing remain recorded as
stale-dependency failures, not successful validation.

The final independent skeptic review additionally identified composite ABI input
ranges: uint8 struct fields preserve width, but the existing parameter premises
only bound direct enum values and one-dimensional enum arrays. Public/external
and constructor composite enum inputs now explicitly refuse admission until
recursive nominal checks exist. Controls pin struct, struct-array and nested
enum-array refusals and retain direct scalar/one-dimensional array admission
with their exact cardinality premises. Internal storage references remain on
their existing typed path. The first resumed source-suite attempt was stopped
for this confirmed fix and retained as incomplete, rather than treated as a pass.

The final build exposed an additional related checking regression in
`CallExceptions.enum_code`: giving every source enum a new uint8 carrier
made an established symbolic panic-code proof exceed its bounded closer
search. Carrier metadata and the extra conversion now apply only to actual
enum-containing struct dependencies. Other enum programs retain their prior
lowering shape; packed ABI sites still retain the correct byte width. A printed
source control pins this distinction. No closer budget or heartbeat was raised.
The pre-fix build and incomplete concurrent suite remain development evidence,
not passing final gates. Subsequent build jobs queue before Lean starts using
a local `flock` launcher over the same 4.24.0 binary, rather than pausing a
checker after it starts; independently timed source proof jobs are never paused.

### Resumed validation evidence

The attached executor reports Lean 4.24.0 (`797c613`) and Lake
5.0.0-src+797c613; the concrete cached `lake build Solidity.KeySort` gate passes
(two jobs). No Lean MCP diagnostics are exposed, so configured per-file
`lake --quiet --no-build lean FILE -- --tstack=131072` checks are used.
The five final upstream/import control files pass. The sealed 23-fixture runs
take 234.931 seconds in total under model
`ca4710564ff1b148a42492323ffe8e667745f2d9e1d5f331cca266481f0234cc`.
Exact commands and individual pipeline observations are in the resumed fixture
record; the preserved 20 already-repaired rows remain working.

The source API compiler is separately pinned 0.8.34+80d5c536, SHA-256
`c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8`.
It is not the upstream fixture runner's 0.8.38 compiler. Exact `62338a6f`
comparisons retain all rows: Calldata has 11 proved, one internal, two
unsupported, three pending and one not-run row; Hashing has 26 proved and four
bounded-walk errors; RevertData has seven proved, eight skipped and three
pending. Hashing and RevertData finish without tool timeouts when scheduled one
obligation at a time. The four nested codec errors are existing 20,000-step walk
limits, not proof passes. RevertData's pending `reasonBytes`, `reasonOfBranch`
and `reasonPastCustom` are baseline proof gaps. Calldata's `sliceHashed(bytes)`
still reaches the unchanged 300-second bound even alone on the exact handoff:
its symbolic slice materialization/hash under a diamond needs existing loop
automation. It remains resource blocked; there is no blind longer retry.
Current Calldata and Hashing checkpoints are complete and match every baseline
status, signature and reading (18 and 30 rows respectively).

Two additional aggregate source subprocesses hit their original wall limit.
Separate complete checks change scheduling only: MemoryPush retains all nine
original expectations (six proved, three pending negative controls), clean
readings and no tool errors; NarrowNested retains all 30 rows (28 proved, two
internal), with all 28 original positive expectations proved and no tool errors.
They take 619.081 and 610.554 seconds respectively, with one obligation per job,
two Lean threads and the same 300-second bound per job. The full-suite failures
remain recorded; these focused results do not relabel the full suite as passing.

Build timing includes intentional queueing alongside source checks and exact
baseline comparisons; it is not a controlled performance benchmark. The default
649-job build passes. `CallExceptions` passes in 23 seconds after the scoped
carrier repair. OpenLoops passes in 941 seconds, within the retained 569/1,172
second range. The frozen TestSuite, final corpus and source-suite outcomes follow below.

The recursion source test also reaches its existing 300-second aggregate bound
(the test already documents load sensitivity). Its complete per-function recheck
retains all 15 original expectations: 14 proved, one pending negative control,
no tool errors, 543.206 seconds total. No expectation or proof limit changes.

Final managed-executor gates pass: `bash run-lean.sh` (8,304.210 seconds,
including intentional serial queueing), `lake build SolidityCorpus` (41.442
seconds, 257 jobs), and `bash scripts/check-corpus.sh` (28.773 seconds). The
frozen TestSuite builds all 249 jobs; the sort check matches all 377 taclets and
131 read-bearing annotations. These are separate from the source API's modern
full-source compilation/code-generation limit.

The unchanged affected source assertions finish **47 passed / 14 failed** in
9,024.147 seconds; this gate does not pass. Nine failures are the previously
independently reproduced task-base cases recorded above. MemoryPush,
NarrowNested and Recursion have aggregate timeouts with complete, successful
focused expectation checks. Calldata retains the exact-handoff `sliceHashed`
resource block and other baseline gaps; RevertData retains three baseline
pending proofs. All 18/30/18 current Calldata/Hashing/RevertData checkpoints are
present and match the exact `62338a6f` status, signature and reading fingerprints.
The remaining Hashing walk errors and RevertData/Calldata pending rows are not
universal proof coverage. Historical source inputs and expected statuses remain
unchanged; no timeout is counted as passing or as an expected semantic failure.
Exact diagnostics, commands, hashes, timings and classifications are in
[the resumed validation record](../../tests/upstream/group08-resumed-validation.json).

Final non-Lean gates pass: all 17 runner/helper tests, verification of all
11,622 snapshot files, strict automation (491 automatic, 61 with a step budget,
11 refuted, zero pending), 667 reachable modules with no orphans, 143 core
modules with no elaborator reachability, current feature-catalog generation and
the frozen TestSuite audit. The documentation-path audit still fails on 13
vendor references and the trust inventory still reports 25 findings; both final
outputs are byte-identical to `62338a6f`, not passing audits or new trust sites.

Finder and independent skeptic performed their final read-only reviews without
opening Lean workers. Each checked the sealed fixture rows and hashes, current
model hash, 35 manifest-referenced log/report hashes, build/corpus outcomes and
source-failure classifications. No remaining confirmed issue was found. The
confirmed implementation findings (unit scaling, enum identity/width/array
padding, artifact unit identity, composite enum ABI admission and unrelated enum
checking cost) were fixed with controls before this review.

Integration keeps the frontend changes together: `Frontend/Source.lean`,
`Frontend/SolcJson/Body.lean`, `Frontend/SolcJson/Contract.lean` and
`Frontend/Import.lean` share the validated artifact/carrier/projection
metadata. The new `scripts/solc-code.mjs` must accompany its two adapter callers;
reports record its separate SHA. The feature catalog and generated inventory
travel together. Source-test changes select batch size one only for the three
measured contracts and preserve every original assertion. No unpublished lane
changes, optional Bridge dependency, new core frame or obsolete reader work is
required.

The lane remains local, with no push or merge. The final handoff exports
`group08-resumed.patch` from `62338a6f`, `group08-combined.patch` from `006fcd59`,
and `group08-resumed-logs.tar.gz` under `.lake/upstream/group08/resume/`.
`handoff-artifacts.json` records their hashes and final commit after export;
the original Group08 patch/log archive remain unchanged. All 23 assigned
fixtures are verified; broader composite enum decoding/input shapes, general
mixed return frames and unavailable static artifacts retain explicit refusals.
The failed source gate and remaining baseline proof/resource limits above remain
open scope, rather than being relabeled as full-project repair.


## Group 08 source validation continuation (2026-10-27)

This continuation starts at `bcd86b83` on the same local lane. The previous
23/23 fixture reports (46 pipeline variants, 58 observations), commits, exports,
source/expectation bytes and the historical results are preserved. The 47/14
source-suite log remains a failed historical gate; baseline matching never
converts an unfinished proof or a tool timeout into a pass.

### Confirmed declaration repairs

Modern admission previously mistook error/event declaration references for
stored function values because solc gives them function-shaped `typeString`s.
The `.selector` exception now requires a static identifier/path or a
contract-qualified member, an exact resolved error/event declaration identity,
and the existing bounded full-width selector parser. It does not admit an
error's `.address`, anonymous events, malformed hex/widths or non-static
receivers. Existing function/getter/stored-function paths remain separate.
The unmodified metadata source assertion now passes all 15 rows: 13 proved,
one internal, and its deliberately false property pending. The new canonical
error/event theorems and malformed/non-static admission controls complement
that modern source check; none asserts a compiler-correctness theorem.

The malformed NatSpec source was already safely refused on both `62338a6f`
and the continuation base: `ensures false; requires false` fails the complete
single-member parser with `expected end of input`. There was no admitted
injected premise. Its empty API error list nevertheless failed the unchanged
single-clause assertion. Uniform whole-import error promotion was rejected:
`SpecBindings.malformedRenamed` has identical syntax and its unchanged mixed
source assertion requires a local refusal with no report errors.

The repair retains the local refusal and attaches the structured
`solidity.specificationSyntax` diagnostic. Testing checkpoints/results expose
`invalidSpecification`. Only a selection whose every non-internal/non-skipped
verification candidate depends on invalid clause syntax additionally produces
one API specification-input error. Mixed usable reports keep their local gaps;
ordinary exclusions, pending proofs and resource failures do not become syntax
errors. A valid caller retains its malformed callee's transitive refusal.
The new regression checks mixed one-row batches, unrenamed/renamed singleton
selections, transitive callers, a proved positive, a false pending property and
an ordinary assembly exclusion. No historical assertion or source was changed.

The two original focused assertions pass unchanged (197.436 seconds); the new
diagnostic-policy test passes (27.983 seconds). The directly affected
SpecBindings report retains all 37 rows and no API errors. Its original test
still fails specifically at `tryScopeExit` pending versus proved; this is not
reported as a passing source gate. The malformed-renamed row stays unsupported,
with its exact full-input parser diagnostic, and the invalid loop name remains
unsupported independently.

### Remaining required source validation

`Calldata.sliceHashed(bytes)` is an admitted implicit-diamond obligation, not
an expected semantic failure. Its printed source contains fresh allocation and
an unannotated symbolic-length memory copy loop before hashing. Direct-file
phase measurement separates successful import/problem generation and callback
classification from the expensive scoped search; smaller compiled walk stages
leave the sequent unfinished. The bounded larger-stage measurement and final
fresh gate results are recorded below when complete.

A general memory-writing loop invariant is not available: `docs/loops.md`
explicitly excludes it because the heap is not anonymised. That explains the
unwinding cost, but it does not establish that the original diamond is true.
The exact source counterexample below supersedes the earlier missing-loop-proof
diagnosis: no sound copy summary can prove the unchanged unconditional claim.
A different, explicitly in-range or box property could require a typed
slice-copy summary (fresh allocation, exact bytes, source preservation, failure
priority/rollback and termination), or a separately proved memory-loop rule.
No such new premise or tag is introduced here. The unchanged automated source
run remains blocked; extending wall time or heartbeats is not a repair.

Other preserved failures remain distinct. Bytes.indexOutOfRange needs a
fixed-bytes bounds/failure-path and closer diagnosis, not a changed expected
verdict; its pending result alone does not identify the responsible layer. The modern
full-source TestSuite testing-table code-generator recursion limit is separate
from the frozen kernel build. SpecBindings.tryScopeExit and
solc/open.tryArgumentSideEffect need callback/try proof support (the latter's
source explicitly identifies the effectful try-argument capture gap).
RevertData.reasonBytes/reasonOfBranch/reasonPastCustom need reason-data catch
proofs. Runner and SpecImport retain policy exclusions versus assertions for
unsupported; loosening exclusions is not a repair. ReferenceParameters.
copiesBeforeEffects remains proved versus a stale pending assertion; the proof
must not be degraded. Hashing's four nested codec rows retain their existing
20,000-step walk errors. These are not passes by baseline provenance.

Calldata additionally retains its three pending slice read/bounds proofs and
the localAlias known-origin refusal. The latter's next frontend step is
concrete: the standalone testing path builds `sol_raw!` after converting source
calldata parameters to memory declarations, whereas native contract expansion
passes explicit calldata roots to `RawStmt.sliceViews`. A repair must seed
origins after those synthetic parameter declarations while retaining lexical
shadow removal, read-only checks and original parameter range premises; simply
marking every memory local as calldata would be unsound. That separate source
alias interface and bounded, initialized-reference-aware negative validation
remain required scope. A copy proof for a different property must not be
substituted for this refuted diamond.

MemoryPush (9), NarrowNested (30), and Recursion (15) retain their existing
complete successful focused expectation checks; those historical rechecks are
not rerun or reclassified as a successful broad source gate.


### Final control correction and measured limit

The first full build correctly rejected the new admission control's use of the
historical legacy AST as modern input: that fixture omits BinaryOperation.
commonType. The modern validator was not weakened. A separate generated
`DeclarationMetadataAdmission.ast.json` retains the modern compiler fields,
while the unchanged legacy fixture now has an explicit modern-refusal control.
This corrects the test setup; the original modern Solidity-file assertions had
already passed. The first full-build failure remains retained as development
evidence, not a final passing gate.

The Calldata measurement reaches the actual compiled-walk bottleneck.
Import takes 1.776 seconds, scoped-problem generation 0.213 seconds, tail-mode
classification 56 ms, evaluable-form preparation 1 ms, and callback
classification 62 ms (`false`). Stages 16 through 1,024 finish in a combined
612 ms and return `none` (the walk has not finished), then scoped search is
interrupted at 300.458 seconds without a proof declaration. A separate
larger-stage measurement takes 1.098 seconds at 2,048 steps, 5.304 at 4,096,
and 32.711 at 8,192, each still `none`. The 16,384-step compiled stage does not
return before the unchanged 300-second job bound (300.978 seconds total,
about 260 seconds in that stage); the 20,000-step stage is never reached.
Sampled peak Lean RSS is 1,386,360 KiB. This is repeated symbolic-copy-loop
unwinding in scoped search, not a failed import, kernel rejection, missing
compiler, or expected semantic failure. No larger wall/proof limit is tried.
The phase helpers are diagnostics only and create no proof or passing source
row. Earlier stream-buffered or elaboration-invalid diagnostic attempts are
retained separately and are not used to locate the bottleneck.

The printed `tryScopeExit` source also distinguishes the return binder `age_`,
the Panic binder `age__`, and the final storage invariant `age == 0`. This is
source-printer evidence that these scopes remain distinct, not a proof of its
pending callback specification; the next proof step is inspection of the
callback/try residual obligation rather than renaming these binders again.

The configured SolKey snapshot lacked its adjacent pin file. All 274 existing
snapshot files were verified against the frozen `473da8944c` manifest before
restoring the byte-identical repository pin beside it. No snapshot bytes were
modified. Both the explicit frozen-path and repaired configured-path TestSuite
audits pass. The initial missing-pin audit failure remains configuration
evidence and does not invalidate the frozen snapshot or become a proof pass.


### Exact Calldata source counterexample

`tests/upstream/DeclarationSourceValidation.lean` now proves
`¬ Fml.Valid Group08SourceValidation.Calldata.sliceHashed.problem` for the
exact imported obligation, then derives its nonderivability by soundness. A typed heap containing one empty byte-array object and
a `some` reference to that object satisfies the original initialized-reference
guard, the full address/byte-element ABI premises, and storage well-formedness.
The array-element premise is proved for every unsigned index, not dropped.
The bounds guard then reverts before copying or hashing. A separate checked
run pins `.error .revert`, excluding exhaustion; length-four and length-five
positive controls require actual normal return (`toOption.isSome = true`).
All five certificate/control axiom outputs are pinned to the standard `propext`, `Classical.choice`
and `Quot.sound` set. This is a checked model-sequent refutation plus concrete
typed-run controls, not a compiler/EVM equivalence theorem.

The new `CalldataValidation.ast.json` is the unchanged modern generated AST of
the existing `Calldata.sol`, from the separately pinned 0.8.34 source compiler.
No historical Solidity source, tag, expected result or archive was changed.
In particular, no `b.length >= 4` input premise was added to obtain a proof.
The generic `sol_refute` attempt found no certificate in its existing 2,000
candidates: its memory-binder domain contains only `none`, and its candidates
start with an empty heap, so it cannot supply this initialized-reference
witness. That failed search is not evidence of validity; the explicit typed
certificate supplies the missing evidence. Failed development proof attempts
are not trusted declarations or reported as axiom-clean proofs.

The original 18-row API report and its timeout remain preserved and blocked.
The refutation does not relabel that timeout as passing or an expected semantic
failure. To remove the automation block soundly, bounded negative validation
must handle initialized reference inputs or replay this kind of certified
counterexample; the unconditional positive claim cannot be made true by a
source-admission rule. Other Calldata positive assertions and the broader
source failures above still require their own repairs. The whole source gate
therefore remains incomplete despite the two repaired declaration assertions.


### Sealed continuation validation and handoff

Final fresh fixture evidence retains **23 working / 0 broken / 0 blocked**,
46 required legacy/viaIR variants and all 58 observations. Every complete
result object exactly matches the preserved continuation-base record. The
final model SHA-256 is
`1e5887ad79a3eaf4a20b18b86a46f176f9504385eb1d8092b8383dce186b160b`;
fixture runtime totals 152.766 seconds. The previous 192.081-second interim
record remains retained separately because its control-source digest predates
the legacy/modern control correction.

`bash run-lean.sh` passes in 1,325.539 seconds: 649 default jobs, 249 frozen
TestSuite jobs and the frozen sort gate (377 taclets, 131 read-bearing
annotations). `lake build SolidityCorpus` passes in 35.089 seconds and
`bash scripts/check-corpus.sh` in 15.095 seconds. The final exact-source
semantic counterexample, nonderivability, genuine-revert and two normal-return
controls pass in 3.525 seconds. After these production gates, only the checked
test outside `Solidity/`, its axiom guards, documentation and evidence changed;
no production dependency was changed, so broad gates are reused rather than
repeated. The core remains intrinsic and dependency-free, with no new axiom,
`sorry`, representation change, raised heartbeat or weakened source premise.
The static selector theorems use only the standard axioms; `ScopeScan.within`
remains axiom-free. The optional Bridge and obsolete SolKey reader are untouched.

The 17 runner/helper tests, snapshot verification, strict automation, module
reachability/layering, feature inventory and frozen TestSuite audits pass.
The trust audit still fails on the same 25 inventory findings (232 sites),
byte-identical to its `62338a6f` output. The documentation audit still fails on
the same 13 missing vendor/external paths, also byte-identical after making an
existing frontend basename citation unambiguous. Neither audit is claimed
passing, and no new trust site is introduced.

Finder and independent skeptic performed final read-only reviews without Lean
workers. They verified all 69 fresh fixture summary/report/log hashes and
source bytes, plus 67 initial and 72 final manifest-referenced hashes, then
reviewed the exact initialized-input certificate and its full original premises. Confirmed
findings were fixed: transitive diagnostic policy was pinned, the new modern
control received its own complete provenance, the legacy missing-metadata
refusal was retained, and every new source-certificate axiom output is now
pinned. The old loop-only explanation is explicitly superseded by the checked
semantic counterexample. No confirmed implementation issue remains in these
repairs; broader source failures remain open rather than being counted as
passes.

Complete per-fixture commands, pipelines, hashes and observations are in
[group08-source-validation-results.json](../../tests/upstream/group08-source-validation-results.json).
Focused source tests, exact proof/resource evidence, retained baseline failures
and remaining scope are in
[group08-source-validation.json](../../tests/upstream/group08-source-validation.json).
The original 47/14 source gate remains failed and was not rerun wholesale;
there is no combined new pass-count claim. The two declaration assertions are
repaired, while initialized-reference-aware bounded negative automation and the
other specifically listed source proofs/interfaces remain required work.

The local continuation consists of `4003dbd7`, `4b638b43`, `d5a68ddb` and the
final documentation/evidence commit. Exports under
`.lake/upstream/group08/source-followup/` include a continuation patch from
`bcd86b83`, a combined patch from `006fcd59`, a commit series and retained logs;
`handoff-artifacts.json` records the final commit, artifact hashes and patch
application checks after export. All previous commits, reports and exports are
preserved. No push or merge is performed. Integration should keep the narrow
Admission/Contract/Testing/API diagnostic changes together with their controls;
no unpublished work from another lane is assumed.
