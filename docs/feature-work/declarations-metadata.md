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
