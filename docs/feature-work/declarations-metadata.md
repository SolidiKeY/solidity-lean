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
