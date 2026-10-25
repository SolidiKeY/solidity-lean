# Solidity scope and syntax subset

This audit classifies the Solidity language at **0.8.38**, the latest stable
release returned by GitHub on 2026-10-25. It pins
[`argotorg/solidity` at `1835d247de183f23e7b0e2bc4a50732af525b77c`](https://github.com/argotorg/solidity/tree/1835d247de183f23e7b0e2bc4a50732af525b77c).
The historical `ethereum/solidity` repository redirects to this repository.
This is a versioned language inventory and a proposed scope contract, with
an inspection assessment of existing implementation support. It does not
assert that every target feature already imports, executes, or proves correctly.

## Artifacts and separate lists

| Artifact | Purpose |
|---|---|
| [Feature inventory](solidity-feature-inventory.md) | Every classified feature, its syntax, scope, current support, requirement/reason, and upstream/local evidence. |
| [Feature manifest](solidity-features.json) | Machine-readable authority: 211 feature families, source pin, Git blob IDs and SHA-256 hashes of inspected upstream files. |
| [Upstream coverage ledger](solidity-upstream-inventory.json) | 783 source symbols mapped explicitly to feature families, including assembly features excluded as a group. |
| `Solidity/Language/Features.lean` | Generated, dependency-free Lean catalog, structured diagnostics and subset interface. |
| `scripts/solidity-feature-audit.py` | Regeneration, metadata validation, source-drift and symbol-coverage checks. |

The Lean API lives in `Solidity.Language`:

```lean
-- Complete, finite vocabulary of classified feature families.
Feature.all : List Feature
Feature.info : Feature → FeatureInfo

-- Target semantics and explicit abstractions, independent of implementation status.
modelFeatures : List Feature
abstractFeatures : List Feature
targetFeatures : List Feature

-- Separate implementation work from permanent scope decisions.
presentFeatures : List Feature
missingFeatures : List Feature
partialFeatures : List Feature
requirements : List (Feature × String)
outsideScope : List Unmodelled
rejectedByUpstream : List Feature

Unmodelled.reason : Unmodelled → String
Unmodelled.errorName : Unmodelled → Lean.Name
```

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
Ordinary `new C` could use a fresh-address contract world with constructor
execution; that extension is missing. Salt-based deployment remains excluded.

## What requires explicit abstraction

The environment supplies caller, payment, contract identity, balance and
timestamp; chain guarantees are premises. Arbitrary typed external calls
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
gas/stipend behavior. A no-callback interpretation is a selected premise,
not an EVM theorem. Resource fuel, bounded call expansion and mathematical
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
  creation/runtime bytecode, physical storage/transient slots and packing,
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
it a complete Solidity AST. The catalog instead supplies this interface:

```lean
def WithinProfile (features : List Feature) : Prop :=
  ∀ f ∈ features, f.inProfile

def ProfileSyntax (Syntax : Type u) (uses : Syntax → List Feature) : Type u :=
  { ast : Syntax // WithinProfile (uses ast) }
```

Instantiate `Syntax` with the actual validated AST representation. A future
`uses` implementation must traverse initializers, inherited bodies,
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
obligations. The wrapper alone does not establish either. This change adds
the inventory and subset contract; it does not wire a new validator into the
existing importer or change runtime semantics.

## Coverage, provenance and maintenance

The source audit crosses the ANTLR parser/lexer with the compiler's C++
parser, AST classes, token table, type categories, builtin function kinds,
global names and native members. It also reads the type/syntax checkers,
global-variable documentation and release changelog. Source SHA-256 hashes
and verified Git blob IDs in the manifest make the exact 19-file inspected
corpus reproducible.

The coverage ledger records 93 parser rules, 26 expression alternatives,
195 lexer/fragment rules, 71 AST classes, 170 compiler tokens, 21 type
categories, 43 builtin function kinds, 24 global names, 30 magic members,
20 other native members, all nine native-member owner classes and 81 Yul
builtin spellings. Dynamic member sets in contract, struct and module types
are covered by declaration identity, field access and imported exports.
Symbols can map to
several features; shared punctuation is a coverage index, not an admission
algorithm. Semantic requirements are additionally enumerated by hand.

ANTLR and AST presence do not establish accepted Solidity: `>>>`, `years`,
`throw`, old aliases and reserved words remain represented in some tables.
Conversely modifier `_ ;` is recognized by the C++ parser despite its absence
from the ANTLR statement alternatives. Concrete modifier bodies must contain
at least one placeholder, and placeholders cannot appear inside `unchecked`;
conditional placeholders can still skip execution dynamically. Fixed-point syntax remains upstream
incomplete. The removed Generic Solidity prototype is not part of this audit's
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

## Audit review

Read-only coverage review identified the new `erc7201`/`slotnum` features,
modifier placeholders omitted by ANTLR, stale upstream syntax, type metadata,
transient-store feasibility and conditional existing abstractions. They are
represented explicitly above and in the catalog. The finder and skeptic
confirmed four repairs: zero-modulus `addmod`/`mulmod` raise Panic(0x12),
`erc7201` admits runtime strings, invalid concrete modifier bodies belong to
upstream diagnostics, and source hashes must preserve exact GitHub bytes.
Source references now point at the relevant productions/native-member sites.
Split elaborator inspection also confirmed existing partial selector-prefix
ABI encoders and function-address projections; they are not missing features.

Validation: the generated-file/source audit, three negative audit cases
(missing parser classification, unknown feature ID and changed pinned source),
module reachability and layering checks pass. All 19 upstream files were
verified against GitHub's original blob IDs before recording their hashes.
The Lean catalog and its metadata consistency proofs compile on Lean 4.24.0.
The repository's doc-link check has 13 pre-existing missing references in
unchanged vendor/external-reference files. The trust-scanner unit test passes;
its repository inventory check has 13 pre-existing drifts in unchanged files,
with no findings in the generated catalog. `lake build Solidity.Language.Features`
passes. A broader `lake build Solidity` was attempted and stopped after more
than 450 targets while compiling unchanged proof examples; it reported no
Lean errors before stopping. Whole-library validation is therefore incomplete.
The broader build used a writable temporary Lake cache and two workers after
the default concurrency approached this environment's 16 GiB memory limit.
