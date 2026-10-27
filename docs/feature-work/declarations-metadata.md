# Declarations and metadata

Compiler-resolved declaration metadata, synthesized public getters and source
ABI identities. Inventory status: partial.
`Examples/Tactics/DeclarationMetadata.lean` and `tests/solc/DeclarationMetadata.sol`
pin the metadata; `Examples/Tactics/PublicGetters.lean` and
`scripts/public-getters.test.mjs` pin the getters.

## Metadata (`Frontend/SolcJson/Body.lean`)

- `type(C).name` is the contract's name as a UTF-8 string literal.
- `type(I).interfaceId` XORs the selectors of the ordinary external/public
  functions declared in `I`, its own overloads and overrides included.
  Inherited methods and receive/fallback contribute nothing.
- Error selectors (four bytes) and non-anonymous event selectors (32 bytes) come
  from solc's canonical ABI metadata, resolved by declaration ID (qualified
  declarations with the same short name included). The parser returns
  `Fin (2^(8*bytes))`. Malformed widths or digits fail closed; anonymous event
  selectors are refused.
- Static declaration selectors and `this.f.selector` fold to literals. A
  dynamic receiver's selector is a fresh pure helper that consumes the receiver,
  so it is evaluated once in place; Boolean and conditional arms stay lazy.
- Unnamed input parameters get names derived from declaration IDs. Unnamed
  returns keep the return-frame naming.
- Generated helpers carry an `#internalEntry` marker in the width metadata
  table (`#` cannot start a Solidity identifier). Function-value construction,
  both dispatch forms and the dynamic call graph exclude them; direct generated
  calls still work, and function-tag indexes are kept.

No selector uniqueness or hash injectivity is assumed. Compiler-invalid
contexts (an ambiguous overloaded reference, a public function's own
declaration selector inside its contract) are left to solc.

## Public getters

- `FunDecl.sourceDecl` is defaulted source metadata: local versus ABI
  functions, selected versus retained base bodies, getters, special entries and
  implementation helpers. ABI selectors are `Fin (2^32)`. Canonical signatures
  are computed before enum/UDVT/contract/struct lowering, so model names never
  feed a selector. Modern serialization keeps every public/external selector.
- A public state variable synthesizes a function beside its storage root.
  Mapping keys and array indexes become parameters; terminal elementary values
  become results; a terminal struct keeps its non-mapping, non-array fields in
  order. Supported types are elementary bool, address, integer and fixed bytes.
  Explicit `uint256`/`int256` indexes are canonicalized.
- Getters share dependency ordering, elaboration and self-call inlining with
  source functions. Scalar, mapping and fixed/dynamic/nested array getters run
  through external self calls; primitive struct tuples through
  `try … returns (…)`. Public variables overriding interface functions resolve
  through solc's `baseFunctions`. Named mapping-key arguments reorder to the
  declared order.
- A getter is recognized only as an external member (`this.x`, `c.x`): a bare
  identifier keeps its storage identity, and a function-valued slot's
  `x.selector` does not fold to its getter's selector.
- **Out-of-bounds getters revert with empty data**, while an ordinary array
  read panics (both pinned compilers, both pipelines). Each generated array step
  is `require(index < path.length)` before the read. Getter bodies skip the
  `withPanics` pass, which would add unreachable `Panic(0x32)` catch
  alternatives.
- Internal function values exclude external declarations, getters and special
  entries; external values exclude local/free/library helpers. Selector dispatch
  and self-body lookup admit selected entries and getters; retained overridden
  base bodies stay available to direct internal calls.
- Generated function, getter and constructor aliases avoid source names,
  generated local/state aliases and printed struct renamings. Constructor
  helpers join `internalFuns` with implementation roles.

## Narrow self returns and byte prefixes

- Narrow primitive external returns are accepted for a static `this` receiver
  once its typed self frame resolves. Range checks reject invalid values before
  the success body, and such a decoder failure reverts the caller with empty
  data outside its catch clauses. The callee's source result kind must match
  the binding: fixed byte widths exactly, no byte/integer crossing; same-sign
  numeric widening keeps the caller-side range checks.
- Dynamic `bytes` to `bytesN` evaluates the receiver once, extracts at most N
  guarded bytes and right-pads with zero; storage operands are materialized
  first. The prefix is a lowering builtin, hoisted whole at an initializer or
  assignment. `bytes(string)` stays valid; both branches of a conditional must
  keep the bytes kind.
- An unused bare scalar identifier is dropped only when it resolves to a
  `VariableDeclaration` of known scalar type.

## Refused, and why

- Getters with nominal (enum/UDVT/contract) or function types, dynamic
  `bytes`/`string` keys or results, or nested aggregate results. An unsupported
  returned field refuses the whole getter: `bytes`/`string` are not silently
  omitted as arrays. Narrow or fixed-byte constants the `uint` constant
  collector does not recognize.
- Narrow returns from an unknown address: world `bytesN` words differ in
  padding from typed self values.
- Byte prefixes of arbitrary `uint8` arrays, and direct `string` conversions.
- Abstract-contract `.interfaceId` (only interfaces are supported).

## Cost

`FunDecl.sourceDecl` touches low syntax, so changing it rebuilds broadly. It
keeps `1a7d5b0e`'s one-body-per-callee memoization and segmented contract
compilation.

## Left

- Import/remapping resolution across source units.
- Reference-valued getters (they need the world's return-value interface) and
  tuple external returns; nominal getter types; struct omissions in exact
  getters.
- Inherited external function values with renamed model declarations (the
  function-value packer hashes model names): one shared ABI identity for
  source declarations and model functions.
- Broader `using for`, qualified custom-error reverts, receive/fallback/world
  registration, remaining constructor/immutable/visibility distinctions,
  and the erasure of mutability in function types.
- `#verify`, `#counterexample` and `#difftest` may still show generated helper
  obligations; the source testing API does not.

## Selector admission and integration

Admission recognizes error/event selectors by resolved declaration ID. They
receive no `.address` exemption. Malformed and missing identities stay rejected;
a same-named stored value remains a typed projection, not declaration metadata.
The SHA-pinned solc 0.8.34 accepts static `MetadataForeign.Problem.selector` and
`MetadataForeign.Changed.selector` but rejects their effectful instance forms
with TypeError 9582, so folding cannot erase a valid source receiver effect.

The source regression requires thirteen proofs, one internal helper and one
pending false property, including the newly admitted typed stored projections.
The focused CLI/admission/filter/tuple build passes 269 jobs and all sixteen
source/CLI integration checks pass. Read-only finder and skeptic reviews found
no blocker; [the integration notes](dafny-verification.md#integration-with-current-origin)
record the checked scope. This does not establish general world/getter parity.

## Group 02: upstream callable-entry replay (2026-10-26)

The 67 historical missing-function rows were reproduced individually on
`006fcd593f5beeb540e7adf2bc76de4638566924`; none was already fixed at the
upstream adapter boundary. Getter bodies and source ABI identities already
existed, but the replay selected only proof-report rows by source spelling.
The final per-fixture evidence and validation are linked from
[the upstream test documentation](../solidity-upstream-tests.md).

The opt-in `solc_import ... testing entrypoints` mode retains selected inherited
ABI bodies and their dependency closure, and reports their rows and synthesized
getters, including getter gaps. Ordinary proof imports retain their previous
report shape. Replay resolves exactly one compiler declaration with the requested
canonical signature and an external-entry role. Internal helpers, retained
base implementations, constructor/receive/fallback entries, missing identities,
and ambiguous signatures cannot serve as a fallback. Source declaration IDs,
getter parameter/result types and native widths remain in the existing tables.
Source-local spellings such as enum and value-type names are never used as ABI
signatures. The old row-based normalization remains only for native replay
controls without source metadata and preserves the function name.

Retained scalar ABI parameter ranges, including enum membership, are checked
before executing either a runtime body or an explicit constructor. A failed
decode reverts with empty data and cannot run body effects. The existing
constructor sequencing, failed-call rollback and getter bounds guards remain
active; no observation, expected value, fuel limit or heartbeat budget changed.
No core representation, run rule or proof rule changes. No new axiom or `sorry`.
This is executable adapter evidence, not a compiler/lowering equivalence theorem.
Body memoization and segmented compilation remain intact.

The pinned source controls in `tests/upstream/Entrypoints.sol` execute in both
legacy and via-IR modes. They cover scalar and nested mapping/fixed/dynamic-array
getters, bool keys, signed/narrow results, inherited entries calling an internal
helper, selected overrides, overloads, canonical enum/value-type signatures,
invalid enum decoding before mutation, constructor decoding, wrong signatures,
missing getter indexes, internal/special entries, missing IDs and ambiguity.
Reference-valued getter refusal remains explicit. Native replay's existing
sequencing, rollback, exhaustion and panic controls also remain required.

Read-only finder and independent skeptic reviews opened no Lean workers. The
finder identified the initially omitted constructor parameter-range check;
that was fixed and given valid/invalid constructor controls. The skeptic requested
an inherited entry calling an internal helper; the source control now exercises
that dependency closure and refuses that same helper as an ABI entry.

### Nominal-key and narrow-constant completion

The final replay also admits primitive UDVT getter inputs/results by their
compiler declaration's elementary underlying type. Enum mapping keys retain
canonical `uint8`, native width eight and an explicit empty-revert membership
guard before storage access. Enum-valued results, contract/function nominal
values and reference returns remain refused. Narrow integer constants use the
existing declaration-based inlining, checked source casts and cycle stack;
the source controls include a signed `int224` constant chain and a negative
constant in both pipelines.

Follow-up finder review caught contradictory key metadata: an elementary type
carrying an enum reference could otherwise receive a different native width
from its canonical ABI signature. Enum-key recognition now requires a nominal
type node and cardinality 1..256, and elementary getter types reject nominal
references. Missing UDVT identities/declarations and contradictory metadata have
explicit refusal controls. The independent skeptic found no further confirmed
issue in this extension; neither reviewer opened Lean workers. Scalar/nested
getter source IDs and native result widths are pinned by the source controls.

### First entrypoint repair result (1d99d00d)

All 67 missing-entrypoint failures reproduced on fresh master. Final results
are 65 working fixtures and two initialization-order mismatches, with zero
assigned exclusions or blocks. All 131 required modes completed; 129 match.
The [per-fixture handoff](../../tests/upstream/repairs/group02.md) retains exact
commands, full passing observations, both mismatch prefixes, every expectation
line, source/model hashes and timings. Later calls after the first mismatch
remain unobserved rather than being counted as matches. Constructor/initializer
sequencing by pipeline remains an integration dependency, with no unpublished
changes assumed from another group.


### First build and corpus validation (1d99d00d)

The managed runtime gate passed with Lean 4.24.0, Lake 5.0.0-src+797c613
and `lake build Solidity.KeySort`. The full 649-job library build passed;
existing `Examples.Decision` and `Examples.DecisionArrays` took 956 and
2,328 seconds on the cold build. These costs are consistent with the existing
slow-check notes in `docs/automation.md`; no representation was changed.

The first process disappeared at 643 jobs. A resumed build completed the
library, but four concurrent TestSuite derivation workers saturated the
16 GiB environment and made no further completion during about ten minutes
of reclaim. That attempt was interrupted and retained as a resource block.
The unfinished modules were retried one target at a time with
`LEAN_NUM_THREADS=1`; all 21 derivation targets passed, with a maximum of
129.6 seconds. The complete `bash run-lean.sh` then passed the 249-job
TestSuite gate and frozen sort check (377 taclets, 131 read-bearing).
`bash scripts/check-corpus.sh --solkey tests/migration/solkey/keyext.solidity.examples`
passed all 774 existing obligation rows without verdict or generated-output
drift. Existing unsupported/unported rows remain so; a passing corpus gate
is not a claim that those rows are proved.

The affected JavaScript suite passes 14/14, replay and new entrypoint controls
pass, and strict automation, reachability and layering pass. The separate
source-suite comparison remains 5 passing and 3 failing on both master and
this patch: one unsupported stored-function observation and two unchanged
300-second source-proof timeouts. No expected result or proof limit changed.
Full commands, logs and review findings are retained in
[group02-validation.json](../../tests/upstream/repairs/group02-validation.json).


### Group 02 initialization-order completion

Resumed the existing lane at `1d99d00d`, preserving both prior commits and
all reports. Both outstanding via-IR mismatches reproduced, while the exact
legacy companion still returned `x = 4`. The source reader now receives the
verified pipeline from import provenance. Legacy retains all-initializers,
arguments, bodies. Via-IR captures base arguments first and then emits each
reverse-C3 owner's initializers immediately before its constructor body,
including implicit intermediate/derived constructors. It selects fields by
compiler declaration identity and carries expression prefixes and fresh names.
The native typed assignment, constructor helpers, modifier wrapping, return
boundaries, admission and call closure remain in use. No intrinsic model,
calculus rule, core representation, expected result or proof limit changed.

`tests/upstream/InitializationOrder.lean` imports the same independent source
under pinned 0.8.38 legacy and via-IR settings. Eleven kernel-checked theorems
cover effectful base arguments, interleaved bodies, implicit owners, modifier
suffixes and early returns, checked-width refusal and first-failure ordering.
The exact legacy assertion panic versus via-IR base revert demonstrates that
failed base construction prevents later initialization; failed deployment
returns no committed state. Swapped pipeline expectations are rejected.
All headline theorems use only `propext`, `Classical.choice` and `Quot.sound`.
The narrow-overflow control explicitly pins the existing model's empty-revert
range guard; it does not claim EVM `Panic(0x11)` payload fidelity.

Read-only finder and independent skeptic reviews found no confirmed schedule
bug and requested the modifier/return, failure-order and narrow-width controls.
Those controls were added and passed; neither reviewer opened a Lean worker.


Fresh full-scope completion replay passes **67/67 fixtures and all 131 required
modes** (65 legacy, 66 viaIR), with all 442 expected call observations retained.
There are zero failures, blocks or exclusions in the assigned scope. The former
state-initialization mismatch now completes all eight calls. The completion
model hash is `4def0e389306e966b857dc45c30fde97248d5b15fced83983c0f416428a93ec6`.
Per-case `priorEntryRepairAfter` fields preserve the earlier 65/2 reports and
mismatch prefixes exactly, and the entire earlier validation object remains
under `priorMilestoneValidation`. Fresh reproductions of both initialization
failures and the passing legacy companion are also retained. Independent
finder and skeptic evidence audits verified every report/source hash, all
expectation lines, 67 exact commands and complete observations. A wording
clarification distinguishes the retained prior Node source-suite comparison
from this follow-up's fresh constructor/inheritance Lean checks.

The required JavaScript suite passes 14/14; fresh getter/replay and affected
constructor/inheritance Lean checks pass. Strict automation, reachability,
layering, immutable archive verification and the frozen TestSuite static audit
pass. Trust findings match the retained baseline exactly. Final dependency-
ordered serial builds and full build/corpus checks passed: all 75 recorded
commands succeeded, including the 649-job library, 249-job TestSuite, frozen
sort (377 taclets, 131 read-bearing, zero mismatches), and frozen corpus
(774 existing obligation rows, no verdict/generated-output drift). Existing
unsupported/unported corpus rows remain unchanged. One Lean worker was used;
no resource failure occurred. The longest TestSuite derivation module took
215.177 seconds, `OpenLoops` 734.213 seconds and `PublicGetters` 140.053 seconds.
The 73 affected modules were built in dependency order before the aggregate
gates; total recorded serial build time was 3,050.104 seconds. These are
unisolated validation timings, not a performance equivalence claim.
The implementation is committed as `6fceb880`, following both preserved prior
commits. Exact commands, logs, model/source hashes and proof/axiom evidence are
in the updated validation record and per-fixture handoff. No push or merge.


The final read-only finder and independent skeptic gate reviews passed. Both
matched all 75 manifest commands, log success markers, build/corpus counts,
timings and preserved artifact hashes; neither opened Lean workers. No further
issue was found. The original patch/log archive remain byte-preserved, and the
completed export and follow-up validation archive use distinct filenames.

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

The explicit proof-bridge audit confirms `AFml.hypVerify?` depends only on
`propext`; `AFml.verify` retains the standard `propext`, `Classical.choice`,
`Quot.sound` set. Existing sequential elaboration is retained: history
`20e30b13` records that parallel decision pins overflowed the CLI stack.
The unchanged loop module checked in 73 seconds, hashing example in 179
seconds, and hash-decision example in 388 seconds. Those timings include
checking their existing examples, not just the new fast path. A managed
reconnect interrupted the first session-attached build after 309 completed
jobs; the branch, evidence and cache survived. Runtime was reverified and
validation resumed with detached drivers and serial compilation.

Integration is self-contained on this lane from `006fcd593` through the
preserved `a4c84673` milestone and resumed implementation `b599a178`. It uses
no unpublished changes from other groups. Shared frontend edits concern
function-type locations, reference-return dispatch admission and declaration
resolution; the AST adapter adds only the required implementation metadata.
The final export contains the complete lane; the separate resumed export
applies after `a4c84673`. Neither export changes the earlier patch artifact.

Final validation completed: all 24 assigned fixtures pass legacy and viaIR with
all 70 ordered observations retained. The 22 dispatch, nine getter and 12
affected inheritance/call/callback source tests pass, as do the three replay
files and all 13 configured per-file Lean checks. The public audit confirms
468 headline theorems use only standard axioms. Strict automation, reachability
and layering pass. `run-lean.sh` passes all 650 default and 249 TestSuite jobs,
then the frozen sort gate (377 taclets, 131 annotations). The unchanged
`DecisionArrays` file completes in 10 seconds; the preceding `Decision` file
takes 1,162 seconds. These are measured module timings, not a controlled
whole-build speed comparison.

The frozen corpus gate passes unchanged: 774 obligations, comprising 552
derived, 11 refuted, one excluded, two skipped, 70 proved, 37 unsupported and
101 unported. No assigned fixture remains excluded or blocked. The documentation
path audit retains its 13 pre-existing missing references. Earlier unrelated
DeclarationMetadata/RevertData coverage limits remain recorded in the prior
milestone; their full source suites are not claimed repaired here. Peak
resource observations and exact log hashes are in
`tests/upstream/group05/resumed-validation.json`; long logs remain under
`.lake/upstream/group05-resume/`. Both independent read-only reviews found no
remaining confirmed issue and opened no Lean worker.

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

The last performance review found that eager enumeration of all possible enum
name suffixes allocated quadratic total underscore characters even when the
first name was unused. The implementation now reuses the existing bounded
`freshSourceName` helper, returning at the first available candidate. The finder
confirmed the cost and the skeptic confirmed identical selected names. This
changes no representation or proof limit. Contract's per-file check, all three
new source regression cases, Replay and all fifteen isolated fixture reports
were refreshed after this correction; the result remains twelve working and
three recursive gaps. Earlier reports are retained separately. Frozen sort
coverage passes with 377 taclets and all 131 read-bearing annotations.

The final skeptic identified a generated-name capture during raw-body inlining.
A function-pointer parameter shadowing state `enumType4` is renamed to
`enumType4_`, which was also an enum conversion's generated name. The original
pointer-only hypothesis passes, but the converse control confirms the defect:
a genuine enum cast in the colliding scope executes the pointer and returns `1`
instead of `0`, in both pinned 0.8.38 pipelines. Generated conversion names now
use quoted `#solcEnum<declaration-id>` identifiers, which ordinary Solidity
identifiers and their generated aliases cannot spell. Explicit import renamings
can spell these quoted names, so they remain reserved by the existing bounded
fresh-name helper. This is a frontend binding fix, not a core representation or
semantic rule change.

`EnumNameShadow.sol` retains both pointer and cast paths, with distinct expected
results and assertions. The explicit import-rename control now deliberately uses
`#solcEnum4`. The new controls preserve eight runtime observations across the two
pipelines and two source assertion obligations; final outcomes and logs are
recorded in the Group 06 evidence. Earlier pointer-only observations and the
confirmed converse mismatch are retained separately.

The namespace fix passes its configured per-file check and frontend rebuild.
All fifteen original fixtures were refreshed again in distinct
`.lake/upstream/group06-resumed-namespace-final/<fixture>` directories: twelve
work in both required pipelines and three retain the recursive import gaps.
The final model SHA-256 is
`c893bd606146fb542537b8b24f351ca39e98291a6e12f1bafb941c0afbc2cf3c`.
The four focused source regressions pass; the direct quoted-import case also
checks the fresh enum name exists and the reserved name does not. Its draft
wrapper/CLI restrictions were corrected without changing model or expectations.
Replay passes nine checks, all six enum-bound kernel checks pass, and the
upstream runner's fourteen JavaScript tests pass. Source controls now total
eleven proved rows, two deliberately pending rows, two unsupported admission
controls and one internal helper; runtime controls retain twenty-six observations.
The strict automation, reachability, layering and frozen-archive checks pass;
the twenty-five trust-inventory findings are byte-for-byte unchanged.

The first serial default run reached its 7200 s process bound at 643/649 jobs,
inside unchanged `Examples/Decision.lean`, without a reported Lean error. Its
completed artifacts are reused by the final serial run, including checks against
the namespace fix. The interrupted run is not counted as a passed default or
TestSuite build. Final default/TestSuite/sort and corpus outcomes remain pending
until their logs close.

The final ABI audit confirmed a separate entry-boundary defect in canonical
matching: `read(EnumAbi.E)` has ABI spelling `read(uint8)`, but the enum has only
two values. The body model accepted `2` as a uint even though it is outside the
source decoder's enum domain. The adapter now checks the selected import row's
existing `paramRanges`, including the unique constructor row, before invoking
the model. Out-of-domain inputs are **blocked**, not counted as successful
expected failures or ABI-decoder coverage. Address checks remain in place.
No argument range, proof premise or expected source result was weakened.

`EnumAbiRanges.sol` and SHA-checked 0.8.38 ASTs pin function and constructor
entry under both pipelines. Four valid cases match six observations; four
out-of-domain cases are explicitly blocked. Eight permanent replay checks and
one additional source assertion pass. The independent skeptic confirmed row
ownership, constructor identity and signed-literal handling without opening a
Lean worker. The final source-control total is twelve proved rows, two
deliberately pending rows, two unsupported admission controls and one internal
helper; successful runtime controls retain thirty-two observations. The source
proof runner still uses the repository's 0.8.34 compiler pin.

All fifteen assigned fixtures were refreshed after this guard, under
`.lake/upstream/group06-resumed-abi-ranges-final/<fixture>`, with exact filters,
batch size one and separate output directories. The final model SHA-256 is
`c42462c7acbc77c576ccb1f375c021ad1708bb241e59091d96e2a68bbd78fa08`.
The result remains twelve working and three broken, each in both required
pipelines; no assigned fixture is classified as an adapter/resource block.
Per-fixture wall times are 4.09–8.01 s including compiler/import/replay, not an
isolated performance benchmark. Previous model reports remain preserved.

Final validation passes the fourteen upstream JavaScript tests, existing nine
replay checks, six enum-bound kernel theorems and eight new enum ABI checks.
`lake build SolkeyTestSuite` completed all 249 jobs, rechecking the report's
552 derived and eleven refuted obligations with zero pending. Frozen sort
coverage passes 377 taclets and all 131 read-bearing annotations. Frozen corpus
parity passes all 774 ledger rows (including its explicit excluded, unsupported
and unported rows; this is not 774 derived proofs). Strict automation passes
491 automatic and 61 budgeted derivations, eleven refutations and zero pending;
its build-log check times 26 TestSuite modules, all below the unchanged 300 s
budget (largest 219 s). Cached TestSuite, sort and corpus confirmations pass
after the last adapter change. Reachability remains 667/zero orphans, layering
143 core/zero elaborator reach, and the 25 trust-inventory findings match the
baseline byte-for-byte. The thirteen missing external/vendor doc references and
unchanged-parent `Bytes.indexOutOfRange` pending proof remain baseline findings.

The full default library gate is **resource blocked, not passed**. The cached
follow-up completed `OpenLoops` in 918 s and `Decision` in 1294 s, then reached
644/649 jobs. The unchanged `Examples/DecisionArrays.lean` runtime pin
`verdict gapArrayBlock` held about 9 GiB after more than forty minutes; it was
stopped to free memory. Its kernel coverage checks complete quickly in the
diagnostic copy. A separate native-symbol attempt compiled 700 cached artifact
jobs and loaded 233 dependency libraries in order. Existing replay and all six
enum-bound kernel checks pass with those ordinary compiled Lean symbols, using
only the standard axiom whitelist. The unchanged array file, run serially with
all three expected results retained, nevertheless reached the 14.5 GiB memory
guard in this 16 GiB executor after 167 s. No array verdict or default-build pass
is claimed. Earlier loader, address-space and concurrent-memory probes are
retained as superseded diagnostics, not passing checks. No `native_decide`,
proof heartbeat increase, new axiom or source representation change was used.
The final adapter change is outside that array module's dependency graph; the
resource evidence records its actual earlier source-model hash separately.

Both independent read-only reviews found no remaining finite-admission issue.
The exported code series applies to preserved `615bd3fa` and reproduces its
committed tree; final evidence and patch export are committed on the existing
lane. This is still an incomplete repair of the fifteen-fixture assignment:
the three recursive fixtures need ordinary graph memory/storage interfaces and
their operation-preserving correspondence, not finite unrolling or an alternate
unproved evaluator. Historical upstream inputs, expectations, archive and
`tests/upstream/results` are unchanged. No push or merge to master was made.

## Group 06 monitor continuation after d4a55688

The continuation preserves all earlier commits, reports and exports. It first
traced `struct_reference` from its exact final import gaps and compiler AST
through ordinary reference admission to the graph foundation. The operation,
missing interface, required agreement theorem and explicit scope decision are
recorded in [recursive-types.md](recursive-types.md#group-06-operation-boundary-diagnosis-after-d4a55688).
The three recursive fixtures remain broken in both pipelines; no unsupported
operation is silently dropped and no unchanged failed admission is retried.

Commit `d8324d62` repairs the unresolved default array check's reduction cost.
A new per-command diagnostic corrects the previous attribution: the combined
list pin does not reveal progress between verdicts. With only the cached
`VisitedSet` and `LinearDecision` native libraries loaded, `gapArrayBlock`
and `arrayBlockBad` finish; the slow verdict is `arrayLenBlock`. Direct array
arithmetic has width seven for the former (a diagnostic walk closes 14,834
states in 129 ms), versus eleven for the latter (100,000 diagnostic steps do
not finish, taking 2.151 s). These are diagnostic copies and bounded search
observations, not successful original default checks or changed production
limits. Earlier 233-library memory failures and interpreted resource logs
are retained unchanged. Superseded probes, including the canceled 54 s
selective-library run used to separate the verdicts, are not passes.

The live-length reduction's normalized arithmetic ends in `(A ∧ B) → B`.
`AFml.nImp` now closes either direct conjunction projection using equality
of the complete formulas. Its general meaning and width proofs are checked;
all other cases retain their previous behavior. This adds at most two finite
structural comparisons per affected connective, not another search. The
history's `5154e4e9` hashed, one-bit derivative walk remains intact. No
representation migration, new dependency, axiom, `sorry`, `native_decide`,
proof heartbeat increase or premise weakening was introduced. The original
`DecisionArrays` source and all three verdict pins are unchanged.

The permanent linear controls pin both projections to `tt`, retain
same-shape wrong-constant and reversed-implication counterexamples, and pin
`[true, true, false, false]`. The general connective proof's axiom guard uses
only `propext`, `Classical.choice` and `Quot.sound`. The independent skeptic
confirmed full-formula equality, constant-case precedence and nonmatching
behavior. The read-only finder corrected the checker name and the two-line
adapted-source offset in the recursive diagnosis. Neither reviewer opened a
Lean worker. Per-file shell checking substituted for unavailable Lean MCP;
the changed core file built in 5.6 s and the linear example in 2.5 s.

Validation is serial in the configured executor. Final commands, hashes,
results and limits are recorded additively under `monitorContinuation` in
[the Group 06 evidence](../../tests/upstream/group06.json); the earlier
milestone evidence is preserved rather than rewritten as a current result.

Integration is self-contained: this continuation edits no shared frontend or
runner interfaces and needs no unpublished group patch. The normalizer's
public types are unchanged, but its low-level module invalidates downstream
artifacts, so the serial default/TestSuite/corpus rechecks are required. Final
checks use ordinary Lean execution without the diagnostic native-library
loading flags.

The original, unchanged `DecisionArrays` module now passes all three runtime
pins in 11 s in the ordinary serial default build, without native loading
flags. `Decision` finishes in 888 s and `DecisionHashes` in 411 s in that run.
These are module wall times, not a general performance bound or controlled
benchmark. The array success supersedes the old resource block; it does not
turn the three recursive source-admission gaps into passes.

The full `LEAN_NUM_THREADS=1 ./run-lean.sh` check passes in 2,067.7 s:
649 default-library jobs, the cached 249-job TestSuite target, and sort
coverage 377/131. Peak child RSS is 6.65 GiB; the memory guard did not fire.
The TestSuite's 247-module source import closure does not reach the changed
`LinearDecision` module, so its successful cache check is not presented as a
fresh re-derivation or timing of 552 proofs. The affected default-library modules and original
array pins were actually rebuilt; the cached TestSuite gate does not
substitute for that result. The sort rules used by the configured default
check have the same SHA-256 as the frozen migration rules.

All twelve supported assigned fixtures pass again in both required pipelines,
with exact-path filters, batch size one and distinct `group06-monitor-final`
outputs. Their retained observations are identical to the previous passing
reports, including call order and failures. The source-model SHA-256 is
`8dfbc7d7d04eb76d78c6753c3037d9ac73cb2bbeb666e6308a4491a19fc856ee`.
The three recursive rows retain their last broken reports and the new static
operation diagnosis; no unchanged failed admission attempt is counted as a
fresh observation on this model.

Post-validation passes the fourteen upstream Node tests, seven focused source
control tests, the original narrow-type source assertions, nine ordinary
replay checks, six enum-bound kernel checks and eight enum ABI replay checks.
The broader bytes test still fails its unchanged `proved` assertion at
`Bytes.indexOutOfRange` (`pending`), independently established on `615bd3fa`.
It is not counted as a pass or confused with recursive source admission.
Source proof controls use the repository's 0.8.34 compiler pin; upstream
runtime/AST checks use the SHA-checked 0.8.38 compiler.

Explicit frozen sort and corpus checks pass, with 377 taclets/131 read-bearing
annotations and parity over 774 ledger rows (552 derived, 11 refuted, one
excluded, two skipped, 70 proved, 37 unsupported and 101 unported). This is not
774 derived proofs. Strict automation remains 491 automatic, 61 budgeted,
eleven refuted and zero manual/pending. Its current build-log gate has zero
fresh TestSuite timing rows because that unaffected target used the cache;
the older 26-module timing result remains historical evidence. Reachability
passes 667/zero orphans and layering 143/zero elaborator reach. The 25 trust
audit findings match `d4a55688` exactly; the standalone inventory audit and
thirteen external/vendor documentation misses remain baseline failures.

A corrected diagnostic normalizer timing copy checks 10,000 unchanged
nonprojection formulas: both checksums are 20,000, with 94 ms before and
95 ms after in one sample; 1,000 outputs are identical. This is not a general
speed claim. Its initial unresolved-name draft was rejected rather than
forced through evaluation. The evidence collector also rejected an independent
hash calculation with different path ordering; full-string ordering now
matches every runner report. Neither issue changed model source or inputs.

The final read-only finder verified all twelve fresh report payloads, hashes,
exact commands, pipelines and unchanged observations, plus all 78 retained
file hashes and 28 structured log hashes. The independent skeptic checked the
projection proof/controls, original array pins, cache/performance limits,
baseline failures and recursive operation boundary. Neither opened a Lean
worker or found a confirmed remaining issue in the delivered change. The
assignment itself remains partial: twelve passing fixtures, three unrepaired
recursive fixtures, and no new fixture pass from this monitor continuation.
