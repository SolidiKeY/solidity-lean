# Solidity scope and syntax subset

This audit classifies the Solidity language at **0.8.38**, the latest stable
release returned by GitHub on 2026-10-25. It pins
[`argotorg/solidity` at `1835d247de183f23e7b0e2bc4a50732af525b77c`](https://github.com/argotorg/solidity/tree/1835d247de183f23e7b0e2bc4a50732af525b77c).
The historical `ethereum/solidity` repository redirects to this repository.
This is a versioned language inventory and a scope contract, settled by the
[user decisions](#user-decisions-2026-10-29), with
an inspection assessment of existing implementation support. It does not
assert that every target feature already imports, executes, or proves correctly.

## Compiler completion target

The user-requested endpoint is a complete compiler with kernel-checked proofs
for every feature except explicit user exclusions. The
[full compiler roadmap](coverage-plan.md) owns implementation groups, source
semantics, admission/lowering coverage, backend/EVM proofs and composition.
Existing `partial`/`missing` statuses, shape refusals and proof limits are work
to finish, not permission to narrow the target. Its initial scope audit must
reconcile recorded exclusions with user authorization; no new exclusion or
assumption is introduced by scheduling a group. The former environment/log
extension proposals do not change the profile without explicit approval.

## Artifacts and separate lists

| Artifact | Purpose |
|---|---|
| [Feature inventory](solidity-feature-inventory.md) | Every classified feature, its syntax, scope, current support, requirement/reason, and upstream/local evidence. |
| [Feature manifest](solidity-features.json) | Machine-readable authority for feature families, source pin, Git blob IDs and SHA-256 hashes of inspected upstream files. |
| [Upstream coverage ledger](solidity-upstream-inventory.json) | 783 source symbols mapped explicitly to feature families, including assembly features excluded as a group. |
| `Solidity/Language/Features.lean` | Generated, dependency-free Lean catalog, structured diagnostics and subset interface. |
| `scripts/solidity-feature-audit.py` | Regeneration, metadata validation, source-drift and symbol-coverage checks. |

The Lean API (`Solidity.Language`): `Feature.all`/`Feature.info`; the scope lists
`modelFeatures`, `abstractFeatures`, `targetFeatures`; the status lists
`presentFeatures`, `partialFeatures`, `missingFeatures`, `requirements`;
`outsideScope : List Unmodelled` with `Unmodelled.reason`/`errorName`; and
`rejectedByUpstream`.

Each `FeatureInfo` stores category, source spelling, scope, current status,
required semantics, upstream source references, and local evidence paths.
`Scope.model` is intended source-level functional behavior;
`Scope.abstract` needs an explicit environment, oracle, or observation profile;
`Scope.exclude` is deliberately outside this profile;
`Scope.upstream` is removed/reserved/invalid syntax or upstream-incomplete
functionality. The last category must not be diagnosed as a Lean modeling gap.

The manifest's current statuses are `present`, `partial`, `missing`, and
`notApplicable`. Lean spells `partial` as `Current.limited`, because
`partial` is a Lean keyword. `present` records implementation evidence for a
narrow feature, not a solc-equivalence theorem. `partial` includes restricted
shapes, conditional entry assumptions, and incomplete proof automation.
Do not use either status as a universal admission rule. Scope and current
support are deliberately independent.

The existing importer's `Gap.excluded` also covers representation limits,
including recursive struct shapes. Those are in-scope implementation work in
this catalog. `Unmodelled` records the deliberate observation/profile boundary;
it is not a mechanical renaming of legacy importer statuses.

## User decisions (2026-10-29)

**User decision (2026-10-29):** the user answered the open scope questions of
roadmap groups G00, G01 and G04 ([G00](feature-work/roadmap-g00-scope.md#open-scope-questions),
[G01](feature-work/roadmap-g01-interfaces.md#open-scope-questions),
[G04](feature-work/roadmap-g04-restrictions.md#6-open-scope-questions)).
These answers settle the questions; they close no proof obligation. The
follow-up list below records what they still require of the pins, the
manifest and the G01 statements.

| Question | Decision |
|---|---|
| G00 Q1 — the 30 recorded exclusions | All 30 confirmed as approved exclusions (for example assembly/Yul, gas, `delegatecall`, low-level calls, selfdestruct, salted creation, raw code, physical layout, logs, extra block/transaction fields). |
| G00 Q2 — premises of the 23 `abstract` rows | Approved: opaque hashes and `ecrecover`, and `msg`/`block`/`this`/balance values as universally quantified inputs. Not approved: `worldAssumptions` and the payment-acceptance boolean, which must be replaced or proposed again. The no-callback reading must become a proved special case (not yet proved; G01 Q4). The remaining abstract rows follow G01 Q4 and Q8. |
| G00 Q3 — EVM fork | Osaka, for the pinned semantics and the compiled bytecode. |
| G00 Q4 — settings | Revised in the second round below: solc's two pipelines only. The frozen profile is solc 0.8.38; 0.8.34 fixtures are SolKey compatibility checks only. |
| G00 Q5 — `creationCode`/`runtimeCode` | The bytes this compiler produces, read from G01's whole-input `Artifact` table, which the source semantics takes as a parameter. |
| G00 Q6 — fixed-point types | Full fixed-point support, beyond the acceptance boundary of pinned solc. |
| G01 Q1 — source resources | Idealized source: unbounded fuel and recursion. |
| G01 Q2 — fixed EVM limits | Resource exhaustion is a failure the source allows (see the follow-up rows below), not an observation; internal calls keep their frames in memory, so recursion depth is bounded only by gas. The code-size limits (EIP-170, EIP-3860) are a recorded idealization: the theorem assumes any code size deploys. |
| G01 Q3 / G04 Q1 — hash collisions | A per-run premise that the preimages hashed by the execution prefix do not collide, plus a random-oracle lemma bounding the probability of a collision (about q²/2²⁵⁷ for q hashes). Global injectivity stays forbidden. |
| G01 Q4 — environment | History-dependent callee strategies with unbounded reentrancy; the no-callback reading (`transferSemantics`) is a special case, not a premise; address 0 having no code stays an assumption. Sender funds and precompile addresses: see the follow-up rows below. |
| G01 Q5 — observation | The full `Event` list with exact ABI and revert bytes, `Panic` codes included. |
| G01 Q6 — state transfer | The public theorem exports `decode : EvmWorld → Option IntrinsicWorld`. |
| G01 Q7 — gas and the environment | Over-approximation: callee answers range over all outcomes regardless of forwarded gas. |
| G01 Q8 — system boundary | The whole input, every contract and linked library, is the compiled system. |
| G04 Q2 — storage aliases after `pop`/`delete` | In profile, with solc's slot behaviour (G28). |
| G04 Q3 — payment acceptance | Any outcome: an untyped recipient may accept or refuse each payment, depending on history; typed recipients run their own code (G47). |
| Follow-up — nested-frame failures | Any external call frame may fail with a revert its caller sees, after which the caller continues: this covers the 1024 call-depth limit and our own code running out of forwarded gas inside a callback. |
| Follow-up — gas exhaustion | Any transaction may revert from gas exhaustion, and the session continues with the next one. |
| Follow-up — sender funds | `msg.value` is bounded by the sender's ledger balance; a transaction the sender cannot afford is invalid and never executes. |
| Follow-up — precompile addresses | Calls to the Osaka precompiles behave as their EVM definitions (the crypto ones through the approved fixed functions), never as environment code. |

Follow-up the decisions require:

- **Contracts (G01).** Revise `Solidity/Roadmap/Contracts.lean` before G01
  counts as frozen: a per-run hash premise and the `decode` export in
  `PublicCorrectness`, the `Artifact` table as a source-semantics parameter
  (with the G07 non-circularity whitelist explaining why a compiler-output
  parameter is not circular), code size dropped from the `EvmSpec`
  resources, and the "open question" wording removed.
- **Pins (G00, G05, G06).** Re-pin the bridge (the hand-written vector scripts
  are re-pinned: [roadmap-g06-osaka.md](feature-work/roadmap-g06-osaka.md)) from
  Cancun to Osaka, modulo EIP-170/EIP-3860, EIP-7825 and the block gas limit
  as recorded; resolve G00's
  disagreements 5 (reference-EVM versions) and 6 (`validateSettings` rejects
  `libraries`, while G01 Q8 puts linked libraries in the system; settled
  below as an empty link map).
- **Manifest.** `fixedPoint` is still scoped `upstream`. Full support needs
  a manifest change, owners and a reference semantics beyond solc 0.8.38;
  the 174 in-profile count changes with it.
- **Resources in the contracts.** The follow-up rows replace "exhaustion
  ends a finite prefix" for gas and call depth: the G01 source semantics must
  let any external frame and any transaction fail, and `Lang.Res` must stop
  ending a session at gas exhaustion.
- **Readings.** Opaque hashes are a fixed parameter instantiated by keccak,
  not an environment input; `this` comes from deployment and the own
  balance follows the ledger. "solc's slot behaviour" for dangling aliases
  fixes the logical alias semantics, not solc's physical packing, which
  stays unobservable.

### Second round (2026-10-29)

**User decision (2026-10-29):** the user answered the questions raised by
the roadmap-w1 cloud batch (G03, G05, G06, the hash bound and the fixed-point
design), and revised G00 Q4. Their question texts are in those groups'
documents as each is integrated.

| Question | Decision |
|---|---|
| G00 Q4 (revised) / G05 Q2 — settings | solc's two pipelines only: the legacy order with the pragma's ABI coder (v1 or v2), and the via-IR order with coder v2. The other six `EvalOrder` flag combinations are not in the profile. |
| G06 Q2 — Osaka gas caps | EIP-7825's per-transaction cap and the block gas limit are a recorded idealization, like EIP-170/EIP-3860; this refines "Follow-up — gas exhaustion" above, which still holds for a gas limit chosen too low. |
| G06 Q1 — forced ether | The environment may credit the system's balance (block beneficiary, a foreign `SELFDESTRUCT`, withdrawals) between transactions and during environment frames; the ledger records these credits and the source lets the own balance grow. |
| G06 Q3 — stipend payments to our own instances | A compiler-independent source cost rule decides which `receive`/fallback bodies fit the 2300-gas stipend; the source fails the payment otherwise, and the compiler is proved to fit every body the rule admits. The rule assumes cold (EIP-2929) access costs, and for a body it does not admit the compiled payment must fail too (compiler-enforced), so the two sides agree. This is a carve-out: gas stays an unobserved quantity (G00 Q1), and for these payments the rule, not "Follow-up — nested-frame failures", decides the outcome; G01 Q7 concerns environment callees only. |
| Hash regions | The per-run premise extends to hashed regions: no region of length at most L based at a hashed slot overlaps another such region or any root region, with a probability lemma of about q²·L/2²⁵⁶. |
| G03 Q1 — shared compiler foundation | Shared-foundation child packages ahead of wave 3 (frozen slot, state and statement interfaces under G24); the work-package manifest and the VM table grow accordingly. |
| G05 Q1 — library addresses | Only an empty link map is admitted: the session deploys and links every library itself; a pre-assigned map is refused. |
| Fixed point — `*` and `/` | The exact product or quotient, truncated. |
| Fixed point — implicit conversions | Only range-contained pairs; lossy pairs need an explicit conversion. |
| Fixed point — explicit conversions out of range | Wrap at run time; an out-of-range constant is a compile error. |
| Fixed point — rounding | Toward zero. |
| Fixed point — shifts | As solc: its type checker admits them but reaches an internal assertion, so no such program compiles; treated as rejected, which narrows G00 Q6. |
| Fixed point — unary minus on `ufixed` | Accepted as solc's type checker does: `Panic(0x11)` unless the operand is 0; wraps in `unchecked`. |
| Fixed point — `++`/`--` | Add or subtract the value 1. |
| Fixed point — explicit fixed/integer and `bytesM` conversions | Integers by value; `bytesM` by bit pattern. |

Follow-up the second round requires:

- **Contracts (G01).** Settings over the two pipelines only; the gas-cap
  idealization; environment credits in the ledger; the stipend rule; the
  hash-region premise next to the per-run hash premise in `PublicCorrectness`.
- **Frontend (G05).** `validateSettings` admits only an empty link map; the
  session deploys and links libraries (resolves G00 disagreement 6).
- **Hash bound.** The region predicate and its counting bound.
- **Roadmap (G03).** The shared-foundation child packages under G24, added to
  the work-package manifest and the VM table.
- **Fixed point.** The reference semantics encode the answers above.

## What belongs in the model

The target includes lexical forms and compile-time values; file/import
resolution; contracts, interfaces, libraries, inheritance and overrides;
functions, constructors, modifiers and repeated placeholders; visibility,
mutability, constants, immutables and getters; structs, enums, value types,
using directives and operator aliases; all legal primitive/aggregate/function
types and data locations; expressions, assignments, conversions, allocation,
tuples, slices, control flow, loops, return, exceptions and argument effects.
The inventory separates ABI encoding/decoding, hashes, typed calls,
reentrancy, reference/copy behavior, storage updates and lifetime semantics.

Solidity arithmetic, bounds, type rules, reference identity and rollback
remain necessary even without an EVM. In particular:

- Track width and signedness at intermediate operations, including nested
  type positions. Fold rational constants exactly. Checked and unchecked
  modes differ locally; division by zero and invalid indexing still fail.
- Preserve short-circuit evaluation, ternary laziness, tuple captures,
  modifier continuations, and evaluation of every `require` argument.
  Record legacy/via-IR selection where the compiler permits different order.
- Distinguish logical storage references, fresh memory copies, memory aliases
  and immutable typed calldata views. Preserve mappings through deletion,
  array reuse and dangling-reference restrictions under the selected profile.
- Distinguish a callee revert from argument evaluation and return decoding
  failures in its caller. State exact panic/revert-byte coverage and what the
  calculus can observe, separately from what the interpreter computes.

**Transient values are an implementation task, not inherently an exclusion.**
A separate logical store can reset at transaction end, persist across
reentrant frames and roll back at failing calls. Physical transient slot
access and gas remain excluded. The current importer/interpreter has no
complete transient-store implementation; accepting its AST as ordinary
persistent state would be unsound.

Likewise `erc7201` can evaluate the namespace formula on runtime strings and
fold constant inputs without exposing physical storage. `type(C).name`, interface IDs, function selectors
and function addresses are source-level metadata. Internal functions and
statically resolved library functions can be lowered without machine code.
Static `type(C).creationCode` and `type(C).runtimeCode` constants are admitted
only with matching compiler/source/settings artifact inputs (to be replaced by
this compiler's artifact table, [G00 Q5](#user-decisions-2026-10-29)); they do not
provide deployed-account code observations or arbitrary bytecode execution
([artifact boundary](feature-work/source-admission.md)).
The typed contract-world API and restricted factory/library source commands
provide creation, creation catches and linked caller-storage execution
([supported fragments and limits](feature-work/contract-world.md)). General
world-aware `solc_import` statements remain missing. Salt-based deployment
remains excluded.

## What requires explicit abstraction

The environment supplies caller, payment, contract identity, balance and
timestamp; chain guarantees are premises (the list is
[semantic-gaps.md](semantic-gaps.md), "Chain facts, as premises"). Arbitrary typed external calls
need a call relation, typed responses, success/failure, payment rollback and
a stated callback interpretation. Linked external library calls additionally
need caller-storage execution context. Source `view` is not by itself a
proof about arbitrary external code.

Cryptographic operations need an explicit interpretation. Selectors can
collide; hashes and packed encodings cannot be assumed injective. Existing
Keccak implementation and opaque/externally interpreted cryptographic
functions must retain their actual trust boundaries.

Payment-only empty-data calls and `send`/`transfer` have existing abstractions.
Their use does not admit arbitrary byte-oriented calls or establish exact
gas/stipend behavior. A no-callback interpretation is today a selected premise,
not an EVM theorem; [G00 Q2](#user-decisions-2026-10-29) requires it to become
a proved special case. Resource fuel, bounded call expansion and mathematical
divergence are distinct from real EVM gas and stack exhaustion.

## What is deliberately outside this profile

`Unmodelled` has finite constructors, including a typed `blockField` payload.
`BlockField` lists coinbase, difficulty, prevrandao, number, gaslimit, chainid,
basefee, blobbasefee and slotnum; timestamp is already modeled and cannot
accidentally be included in that constructor.

- General inline assembly/Yul, including memory-safe flags and every listed
  Yul opcode. The separately recognized whole-buffer revert idiom is an
  explicit exception, validated by shape and declaration identity.
- `gasleft`, gas options, exact gas forwarding/stipends/refunds and real
  machine resource limits.
- Raw `msg.data`/`msg.sig`, byte-oriented fallback dispatch/output, arbitrary
  low-level call/return bytes, `delegatecall` and low-level `staticcall`.
  Typed calldata slices and caught revert bytes are separate supported targets.
- `selfdestruct`, `create2` salt/address rules, address code/codehash,
  arbitrary creation/runtime bytecode execution, physical storage/transient
  slots and packing,
  custom `layout at`, and raw memory addresses/layout.
- Observable logs, topics, event ordering and log gas. Event arguments must
  still execute, including their side effects and failures. Erasing the log
  only supports properties that do not observe logs.
- The listed extra block fields, block/blob hashes, `tx.origin` and
  `tx.gasprice`. Most extra fields are feasible environment extensions in a
  different profile; their exclusion here is a deliberate boundary, not a
  claim that modeling them is impossible. `block.slotnum` is Amsterdam-gated;
  historical difficulty/prevrandao interpretation is fork-dependent.

Diagnostics are stable structured names such as `solidity.inlineAssembly`,
`solidity.rawCalldata`, and `solidity.blockField.number`, with the exact
one-line reason stored in the manifest and returned by `Unmodelled.reason`.
The Lean theorems `Unmodelled.excluded` and `Feature.exclusion_complete`
prove that every diagnostic denotes an excluded feature and every excluded
feature has a diagnostic. `Feature.all_complete` proves the list enumerates
the feature type.

## A subset of actual Solidity syntax

The full syntax belongs to solc. Do not create a toy recursive tree and call
it a complete Solidity AST. The catalog instead supplies
`ProfileSyntax Syntax uses`, the ASTs whose used features are all
`inProfile` (`WithinProfile`).

The solc importer's admission scan (`Frontend/SolcJson/Admission.lean`,
`ScopeScan` in `Frontend/Source.lean`;
[feature-work/source-admission.md](feature-work/source-admission.md)) is that
extractor: a successful scan certifies its feature list is within the profile
(`ScopeScan.within`). It must traverse initializers, inherited bodies,
modifier bodies/arguments, callees, function-valued dispatch, ABI/error/event
arguments and call options. It must resolve builtin identities and respect
shadowing, rather than matching only names. Unknown nodes must fail closed.
Composite nodes need several features: `{value:...,gas:...}` includes both
`valueOption` and excluded `gasOption`; a byte-oriented fallback includes
excluded raw input/output even though a fallback declaration exists.

Extraction also depends on the declared observations. An `emit` uses
`emitStatement` and its argument features; a property that observes logs
additionally requires excluded `eventLog`. A verified canonical rethrow uses
`canonicalRethrow`; every other assembly block requires `inlineAssembly`.
The many-to-many coverage ledger cannot be used directly as this extractor.

Completeness of that extractor and lowering correctness are separate proof
obligations, not proved.

## Coverage, provenance and maintenance

The source audit crosses the ANTLR parser/lexer with the compiler's C++
parser, AST classes, token table, type categories, builtin function kinds,
global names and native members. It also reads the type/syntax checkers,
global-variable documentation and release changelog. Source SHA-256 hashes
and verified Git blob IDs in the manifest make the exact 19-file inspected
corpus reproducible.

The coverage ledger maps every extracted symbol (parser rules, lexer rules,
AST classes, tokens, type categories, builtins, globals, native members, Yul
builtins) to feature families. Symbols can map to several features; shared
punctuation is a coverage index, not an admission algorithm. Semantic
requirements are additionally enumerated by hand.

ANTLR and AST presence do not establish accepted Solidity: `>>>`, `years`,
`throw`, old aliases and reserved words remain represented in some tables.
Conversely modifier `_ ;` is recognized by the C++ parser despite its absence
from the ANTLR statement alternatives. Concrete modifier bodies must contain
at least one placeholder, and placeholders cannot appear inside `unchecked`;
conditional placeholders can still skip execution dynamically. Fixed-point syntax remains upstream
incomplete; [G00 Q6](#user-decisions-2026-10-29) asks for full support. The removed Generic Solidity prototype is not part of this audit's
mainstream language. Compiler CLI/JSON protocols, optimizer passes, SMTChecker,
debuggers, code generation, linking tools and metadata packaging are compiler
products, not additional executable Solidity syntax; their selected settings
remain relevant provenance where they affect accepted input or behavior.

This establishes explicit coverage of these pinned source surfaces and a
semantic checklist. It is not a mechanically proved completeness theorem
over all compiler behavior, historical versions or future language changes.

```sh
# Regenerate the Lean catalog and readable inventory after editing the manifest.
python3 scripts/solidity-feature-audit.py

# Check generated files, metadata, local evidence paths and classification IDs.
python3 scripts/solidity-feature-audit.py --check

# Also compare exact source hashes and every extracted symbol against a checkout.
python3 scripts/solidity-feature-audit.py --check --upstream /path/to/solidity

# Check the Lean definitions and metadata consistency theorems independently.
lake env lean Solidity/Language/Features.lean
```

An upstream hash/symbol change requires a new review and explicit ledger
updates; the checker never assigns newly discovered syntax a default scope.
The normal CI check verifies generated-file consistency without downloading
upstream sources.
