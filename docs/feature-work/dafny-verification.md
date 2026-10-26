# Dafny verification additions

The [Dafny inventory](../dafny-parity.md) tracks feature families and remaining
gaps. These additions reuse the typed interpreter and logical equality, with no
new runtime type, core package dependency or proof axiom.

## Well-founded loop termination

`Solidity/Semantics/Termination.lean` supplies an explicit finite outer-iteration
witness (`TLoop.finite_of_wellFounded`) and relates it to the existing interpreter
(`run_wellFounded`, `run_measure`, `run_lex`). Lexicographic pairs allow the second
component to increase when the first decreases; the generic API admits nested
products and other well-founded relations.

The generic theorem accepts an explicit predicate on terminal outcomes. For
successful termination, `Stmt.loop_terminates_of_wellFounded` requires live body
runs to return successfully in the invariant with a smaller rank and proves an
actual `.ok` output satisfying the postcondition. Divergence, exhaustion, panic
and revert are not successful witnesses. Measures read typed states, including
their growing heaps.
The scoped theorem reads `Stmt.run`; callback relations need their own
termination proof.

`Solidity/Examples/Termination.lean` proves arbitrary natural-counter resets and
a source-elaborated Solidity loop whose inner flag resets upward while its outer
flag decreases. Actual divergent, exhausted and reverting scoped loops are
negative cases. The finite witness uses only `propext`; the operational and
scoped results use Lean's standard three axioms.

The optional `Bridge/SolidityBridge/LoopFixpoint.lean` already supplied a Mathlib
fixed-point proof of generic well-founded correctness. The core addition avoids
that dependency and adds finite witnesses, a scoped bridge and lexicographic
examples. Typed source tuple annotations and their strict certificates are
described below. Total recursive termination
remains separate work. Bounded recursive contracts retain their exhaustion policy.

## Finite primitive membership

Function preconditions, postconditions and contract invariants can use:

```solidity
/// @custom:key requires \in uint (amount; 1, 2, 5)
/// @custom:key ensures \in uint (\result; 1, 2, 5)
function echo(uint amount) public pure returns (uint) { return amount; }
```

The domain is `uint`, `int`, `bool`, or `address` (the existing uint alias).
`\in uint (x;)` is empty membership. Duplicates do not change membership.
Quantifiers and `\old` retain their scopes. The raw specification constructor
compiles only after the key and every element check at one primitive sort. Even
empty membership checks its key. Mixed fixed types, unbounded ledger integers,
reference-valued keys, unknown names, forbidden snapshots and invalid literals
are refused.

The compiler uses `Fml.finiteMember`. Its general denotation theorem,
`holds_finiteMember` in `Solidity/Calculus/FiniteMembership.lean`, equates the
formula with equality to a listed term under the typed Theory interpretation.
Every operand is a `Tm C Γ (.val p)` at the same `p`.

This is finite **equality** membership. It preserves the existing KeY rule that
two halting specification expressions are equal; it does not assert that every
operand returns a value. First-class sets, definedness obligations, cardinality,
maps, sequences, multisets and comprehensions remain separate work. Loop
annotation syntax is unchanged.
Membership is a specification formula: combine it with logical connectives or
`<->`, rather than using it as a primitive-valued operand of another membership.

`Solidity/Examples/Tactics/FiniteSets.lean`, `tests/solc/FiniteSets.sol` and
`scripts/finite-spec-sets.test.mjs` cover positive and false postconditions,
type errors, empty keys, snapshots, ledger-valued Boolean comparisons, parameter
renaming, quantified shadowing, literal traversal and printer/parser round trips.

## Certified entry-condition audits

A postcondition proof can be vacuous because its entry condition is impossible.
The new audit checks the entry condition independently:

```sh
node scripts/test-solidity.mjs --audit-preconditions path/to/Contract.sol
```

The JavaScript option is `auditPreconditions: true`; the VS Code option is
`solidityLean.auditPreconditions`. Auditing is off by default and discovery does
not run it. Listing and auditing cannot be combined at the CLI.

An audited row retains its normal proof status and adds `preconditions` and
`preconditionReason`:

| Result | Evidence and behavior |
|---|---|
| `possible` | A kernel-checked counterexample to entry impossibility. |
| `impossible` | A kernel-checked proof that no entry state meets the condition; strict suites fail even if the postcondition is proved. |
| `unknown` | No accepted certificate within the bounded search; strict suites fail without claiming possibility or impossibility. |
| `notApplicable` | No admitted function specification to audit. |
| `notRun` | An interrupted checkpoint, which cannot pass a strict suite. |

The editor shows impossible entries as vacuous-specification warnings and marks
audited tests requiring attention. Unknown audits stay distinct from certified
counterexamples. A backend omitting a requested audit is rejected.

Lean callers can retain a named certificate:

```lean
#audit_preconditions cspec[ContractName]{functionName} as entryCheck
```

The result is `Fml.PreconditionsImpossible` or `PreconditionsPossible`, tied by
the indexed `Fml.EntryNegative` relation to the original obligation. The extractor
preserves leading primitive quantifiers and hidden parameter binders, then
negates the first implication's antecedent. It does not execute or assume the
postcondition. Unsupported shapes report unknown without creating a theorem.
Failed searches restore their state and messages; accepted declarations are
kernel checked and restricted to the standard three axioms.

Possibility is satisfiability in the typed model under the specification's entry
premises, including its layout, value and invariant assumptions. It does not
establish constructor reachability, successful execution or absence of dead
branches. Partial-correctness proofs of reverting programs retain their meaning.

`Solidity/Examples/Preconditions.lean` and `tests/solc/Preconditions.sol` distinguish
an impossible entry, a possible entry and a false postcondition with a possible
entry. The runner regression also checks default behavior, opt-in strictness,
batching and listing rejection.

Candidate enumeration checks the Cartesian product's cardinality before
allocating it. Oversized pools use the existing bounded random search instead;
regressions cover a 40-parameter product, empty factors and a real source audit
with 12 primitive parameters. An exhausted search still reports unknown.

## Certified source model prestates

`--counterexamples` (JavaScript option `counterexamples: true`) runs an opt-in
search after an ordinary specified function leaves open proof goals. The first
fragment admits primitive storage and primitive named input binders. Callback,
recursive and plain obligations retain their existing results. Reference storage,
unsupported shapes and unsuccessful search or certification supply no witness.

`Tools.refuteSource?` receives the exact original `Fml.Valid` goal. It searches
once, constructs a proof of that goal's negation with the found candidate, and
serializes that same candidate. The frontend retains the theorem at
`function.refuted`, kernel checks the exact negated goal, and checks its transitive
axioms before emitting `status: "refuted"`. A found candidate without an accepted
certificate stays pending. The initial search is capped at 256 candidates, with
the existing bounded shrinking afterward; subprocess and heartbeat limits also
apply. The cardinality preflight above runs before product allocation.

The optional `counterexample` JSON contains a certificate declaration and axiom
names, typed argument values, transaction inputs, initial storage, ledger and
balance, plus an optional halt or post-storage outcome and readable lines.
Numerical values remain decimal strings, including full-width unsigned and signed
words. The empty external-response table is checked before serialization.
Argument `paramIndex` comes from an exact model-name lookup in the import row's
source-order parameter list. The JavaScript adapter uses the original solc
declaration ID and this index for source names and types, preserving model names
and unnamed parameters without underscore or overload guesses.

The extension validates this transport envelope, renders only validated fields,
escapes model text, and reports refutations as failed tests and error diagnostics.
Existing source-hash, document-version and cancellation checks govern witnesses.
An envelope is evidence from the configured backend; the editor does not itself
run the Lean kernel on a theorem received through JSON.

These are arbitrary typed model prestates under the specification's premises.
They do not establish constructor reachability, replayable transactions, a full
post-ledger/heap, or a sequence of intermediate execution states. The inspected
Dafny handler instead emits source-positioned noninitial model-state assumptions
(`DafnyCounterExampleHandler.cs`, lines 103–112). Its request depth defaults to 5,
but the inspected handler does not use it as a serialization bound. The inventory
now pins five additional counterexample server/test blobs; it retains a partial
assessment for this family.

## Validation commands

```sh
lake build Solidity.Examples.Termination Solidity.Examples.Preconditions Solidity.Examples.Tactics.FiniteSets Solidity.Frontend.Testing
node --test scripts/preconditions.test.mjs scripts/finite-spec-sets.test.mjs
node --test scripts/counterexamples.test.mjs
node --test scripts/check-dafny-features.test.mjs scripts/source-locations.test.mjs vscode/test/*.test.cjs
node scripts/check-layers.mjs
node scripts/check-orphans.mjs
```

Source tests need the pinned compiler described in
[solidity-testing.md](../solidity-testing.md). Use one Lean worker for constrained
environments; this session has a 16 GiB memory limit. CI downloads a fixed
compiler binary and the existing helper checks its SHA-256 before executing it.
The editor-host harness includes a fixture audit; its optional real backend
checks membership and entry certificates through solc and Lean.

## Review record

Read-only finder and skeptic passes checked the typed membership compiler,
termination theorem scope, entry certificates and editor metadata. Review found
that a failed later batch could omit requested audit metadata from its checkpoint
rows, causing the extension to discard completed siblings. The runner now emits
`notRun` audit fields; a cross-layer 33-function regression checks that behavior.

A follow-up pass checked the candidate cardinality preflight, including positive
counts, division before multiplication, odd budgets, empty factors and exact
candidate order. Neither reviewer found a remaining issue. The bound limits the
number of combinations, not the size of every candidate or all proof execution.

Separate read-only finder and skeptic passes checked source witness generation,
the retained exact-goal proof, transitive axiom checks and the editor transport.
They confirmed that serialization uses the certified candidate and that input
indices follow the original solc parameter array, independently of formula-binder
order. Rendering was tightened to display only validated transaction, ledger and
outcome fields. Search-budget wording was clarified to distinguish initial
candidates from subsequent bounded shrinking.

The source trust gate exposed 25 inventory drifts already present at the initial
`23d23377` checkout. An audit of those exact Git blobs confirmed there were no
forbidden proof constructs. Finder and skeptic reviewed the current cache,
compiled implementation and evaluator sites before reconciliation: two obsolete
entries were removed and 27 exact occurrences added, including the three new
search/presentation evaluator sites. The checker and forbidden-construct policy
remain unchanged. This records frontend and native implementation surfaces; it
does not prove cache correctness or EVM conformance. The independent transitive
axiom audit also includes the new termination, membership, entry-condition and
retained source-refutation theorems.

Real editor-host testing exposed hover selection of a synthesized constructor's
whole-contract range ahead of its function. Function declaration IDs now take
precedence; a controller regression and the real certified-witness hover check
cover the correction.

## Validation results (2026-10-26)

- `./run-lean.sh`: the final checkout passed 631 default build jobs, 248 imported
  solkey suite jobs, and the 377-taclet/131-annotation cross-check.
- 51 fast inventory, source-position, controller, protocol and subprocess tests
  passed. The two trust-checker tests also passed.
- Five finite-membership/entry-audit source tests passed, including wide parameter
  pools and interrupted-batch metadata. Three source-witness tests passed for
  overloads, exact source names, full-width values and unsupported readings.
- The real VSCodium extension host passed 20 checks, including actual solc/Lean
  membership proofs, entry certificates, an exact-goal refutation, source mapping,
  diagnostics and hover. Transport fixture checks remain distinct from those
  real-backend checks.
- The transitive audit passed for 479 headline theorems. The unchanged source
  trust checker reports 662 sources, 231 implementation/recovery sites and zero
  findings. Layering reports 137 core modules with no elaborator reach; all 649
  modules are reachable with no orphans.
- Version 0.3.0 packaged and installed in an isolated editor profile. Its manifest
  and every runtime source matched the tested checkout. The local artifact is
  `.gen/solidity-lean-0.3.0.vsix`.

The repository-wide prose-path check still reports the same 13 pre-existing
external/vendor references; none names the new files. No core package dependency,
proof axiom or raised heartbeat limit was introduced. The remaining gaps in the
inventory stay open.

## Source tuple follow-up

`LoopMetrics C Γ (n + 2)` now retains at least two unsigned components in source
order. NatSpec `decreases (outer, inner)` and longer tuples pass every component
through the existing capture-free `loopExpr` check before construction. Both
quoters, source and calculus printers, weakening and size accounting preserve
the tuple. Malformed, effectful, unknown and wrongly typed components are refused,
including invalid second and third components.

The explicit Lean-only `loopLexErase` rule reaches the existing invariant proof
without transforming runtime code. Its annotation size strictly decreases;
ordinary and callback erasure have separate checked semantic lemmas. This supports
the existing partial-correctness proof path without asserting that a source tuple
decreases. The scalar variant path is preserved. The automatic tuple diamond VC
follow-up below extends this path; broader metric sorts remain open.

`Semantics/LexMetrics.lean` evaluates the typed tuple into an unbounded nested
natural product and proves its lexicographic relation well founded. The strict
certificate requires defined components at every invariant head, successful
invariant-preserving body runs and a decrease after every body turn. It derives
an actual `.ok` result. These sufficient conditions are conservative at exit,
break and return; they read ordinary `Stmt.run`, not callback total semantics.

Review identified an identity distinction: the run erases annotations, so a
successful-run proposition alone cannot certify the declared tuple. The added
`LoopMetrics.SourceCertificate I G actualLoop` is indexed by the actual statement
syntax and retains the certificate for its stored tuple, condition and body.
`SourceCertificate.checks` recovers that exact check; `.valid` projects successful
execution given an initial proof of `I`. The semantic invariant and postcondition
are explicit and do not silently certify the annotation's invariant clauses.
A false invariant is vacuous; the entry witness remains necessary.

`Examples/LexMetrics.lean` retains this indexed object for an actual annotated
source program, proves its successful execution and rejects equal, increasing,
undefined and exhausted-body certificates at live, inhabited heads. A regression
shows that runtime results themselves erase metric choice. The imported-source
tests separately verify safety proofs, invalid components, tuple lengths and
order, loop lowering and a retained callback-semantics proof. Initial validation
kept source local-variable shadowing as an explicit gap; the source-binding
follow-up below closes that gap without changing the typed core's freshness rules.

Read-only finder and skeptic passes checked component validation, typing, scope,
quotation, rule partition/coverage, callback capture and the fallback ranking
function's guarded use. Review corrected fixture tags: untagged functions use
diamond obligations, while the safety cases require explicit box tags. The
remaining source gaps and strict-certificate boundaries are documented in
[loops.md](../loops.md#typed-tuple-measures).

Focused validation for this follow-up passes: 222 Lean jobs, the three imported
tuple tests (safety, explicit gaps and kernel-checked source shapes/callback
reading), 51 fast tests, and 23 real editor-host checks. The source trust scan
reports 666 sources, 231 inventoried implementation/recovery sites and zero
findings; layering finds 139 core modules with no elaborator reach and 653
reachable modules with no orphans. The headline audit accepts 492 theorems with
only the standard axioms. The full build exposed a generic rule-printing gap:
opaque tuple metrics escaped as an entire statement. Packed typed escapes now
print and reconstruct the tuple annotation, while concrete source tuples still
print every component. A typed schema regression and all 26 rule lines pass in
a 227-job focused build. A source regression rejects the same Lean escape syntax
inside NatSpec comments. Final global checks are still required after integration.

## Source lexical scope follow-up

The solc importer now assigns declaration-ID model names to declarations with
colliding source or effective names. It preserves collision-free legacy aliases
and reserves all source identifiers, specification binders and generated names.
Body references still resolve through solc's `referencedDeclaration`, including
outer-variable reads in a shadowing declaration's initializer. Source annotation
bindings retain their lexical stack; function specifications use only the
parameter/return scope, and named call arguments retain their original labels.

The six new source tests check inner reads and writes, scope restoration, default
and self-initialization, state/parameter/return/modifier/catch bindings, tuple
declarations, quantified loop binders, named calls and attempted capture of an
allocated model name. A kernel-checked tuple-shape assertion identifies the
innermost local position. Certified counterexamples retain source parameter order
and exact source names after model renaming; a false assertion remains pending
without that opt-in search. The previously unsupported tuple-shadowing fixture
and four C99 scope migration cases now prove from freshly compiled source.

Read-only finder and skeptic reviews found no blocking allocator defect. Finder
identified the older tuple test's unsupported expectation, which is updated with
this integration. Duplicate-name scans add quadratic allocation work in the
number of declarations; the frozen TestSuite compatibility check measures the
existing large import. Historical migration snapshots are not rewritten to imply
they were produced by the new importer. Constant/enum name resolution and the
remaining source admission limits remain separate work.

The complete source-addition suite passes all 17 tests (266 seconds), including
the three tuple tests and six shadowing tests. Fast tests pass all 51 cases; the
real editor host passes 26 checks, including source shadowing, renamed witness
positions, exact diagnostics and hover content. CI runs both the broader source
suite and the host against the real compiler/verifier. Its large frozen listing
gate exposed a baseline code-generation recursion limit. Rebuilding exposed
list spines and compiling certified 64-row report segments fixes both whole-model
projection capture and large report serialization without increasing depth
limits. Whole-contract and whole-report kernel equality checks remain. The actual
617-row frozen listing gate now passes in 193 seconds (563 ready, 51 internal,
two skipped and one unsupported recursive layout); the historical proof report
retains its separate excluded classification.

## Ordinary tuple diamond verification conditions

The typed `LoopLex` snapshots retain all components in source order. Initial
snapshots read the original context; subsequent body snapshots retain old ghost
values while reading the changed state. The semantic bridge proves definedness,
landing-state identity, context weakening and equivalence between the generated
comparison formula and the well-founded natural-tuple relation.

`whileInvariantLexDiamond` is selected for ordinary diamond loops with an
admitted body frame, no break flag and no quantified invariant clauses. Its VC
requires invariant preservation and strict decrease after every successful body
turn, including the final turn. Unsupported shapes remain pending. The erasure
rule has an explicit side condition preventing supported diamonds from bypassing
these checks. Callback diamonds have no bridge. Ordinary diamond semantics still
accept exhaustion, as a concrete exhausted-body regression demonstrates; the
rule does not generate `SourceCertificate` values or claim strict termination.

Rule metadata, printed syntax, replay and tree data retain the exact frame
witness. The rule-size proof counts one initial update per metric and one for
the condition, replacing the old universal two-update bound with an arity-aware
bound. The two-update theorem remains available for existing shapes, and the
global `16 * statement.size + 16` formula-size bound remains proved unchanged.
The public tactic matrix passes, including pair/triple countdowns and inner
resets, scalar compatibility and negative cases. The broad build found a source
branch-label mismatch in the new packed notation. Explicit optional labels now
appear in the actual rule schema and round-trip through the printer. All 274
focused jobs pass, including the unchanged source-label audit, exact typed
premise identity, 181/27/4 printer coverage and actual source-loop tree labels.

The source reset regression also exposed a budget boundary in leaf search:
classification of a third leaf inherited the heartbeat count spent on earlier
leaves. It now receives its own inherited cap, like the closing attempts. A
failed classification selects only the existing conservative closers. No numeric
limit or proof obligation changes; the source pair reset now proves at the
unchanged 200000-heartbeat cap. Temporary diagnostic probes are removed. The
remaining complete source, editor and global gates are being rerun.

The source matrix also distinguishes a do-while invariant limitation from a
runtime defect. Lowering introduces `first = true`, but the user invariant
`x <= 2` does not retain its relation to the source initialization. The abstract
head `first = true, x = 0` invalidates the generic decrease VC. The safe x=2 run
therefore stays pending, beside a separate actual zero-start underflow negative.
Finder and skeptic confirmed this classification. No first-phase relation is
assumed, no runtime body is duplicated, and no source tuple component is changed.
Checked phase strengthening and general entry-phase reasoning remain tracked work.

Current editor validation passes all 30 real-host checks, including the ordinary
source tuple proof, equal-tuple pending diagnostic/hover, Test Explorer statuses,
source shadowing and exact certified witness display. All 60 fast tests pass.
The revised six-group tuple suite passes all 18 retained rows: five proofs and
thirteen explicit pending cases, including the do-while invariant limitation and
actual underflow. The standalone quantifier hygiene repair and final combined
source/global gates remain in progress.

## Logical binder scope repair

A separate narrow compiler repair rejects logical binders named `old`, `oldNet`,
`result` or `result_*`, and gives primitive locals precedence over outer storage
and memory reference paths. This prevents a same-typed logical binder from
capturing a function's special return value, and prevents a primitive binder's
field/index access from silently reading an outer reference. Parameter-name
policy stays the same. The check deliberately rejects reserved names even in
vacuous guards.

The focused 84/253-job builds pass. Both new tests pass: 26 distinct source rows
retain seven kernel-checked proofs, eighteen explicit compiler errors and one
pending false actual-return claim. Direct compiler patterns check inner and
outer result positions. Existing finite membership and source return/renaming
regressions also pass (three tests, 108 seconds). Read-only finder/skeptic review
corrected one generated test syntax typo and found no remaining production
blocker. The pending false claim is not reported as a certified refutation.

## Finite filtered membership

The [implementation notes](filtered-membership.md) describe the new literal-domain
identity filter, its typed binder and exact scoped denotation. The outer key and
inner guard remain distinct through source aliases, nesting and snapshots.
Existing prefix equality-membership keeps its original semantics. The new form
is limited to primitive literal domains; general collection values, images and
source predicates remain separate work.

All focused proof/compiler/API/example checks pass. The final three source tests
pass in 41.65 seconds: 24 admitted rows retain 21 kernel-checked proofs and three
intentional pending claims; 29 invalid rows retain 28 errors and one explicit
loop-annotation gap. The exact-goal certified witness also passes. Bounded
`allLeft` equality hints close signed and quantified cases without increasing
candidate, application or heartbeat caps; parsed free-root queries preserve
binder scope when checking omitted state declarations. Final finder/skeptic
review corrected one temporary candidate-array cap and found no remaining blocker.

One syntax-round-trip inspection evaluates a `SpecExpr` in a meta command. It is
explicitly marked and inventoried; the actual correctness theorems retain kernel
and transitive axiom checks. The headline audit now includes the six generic
filtered-membership facts and five public correctness examples. Final combined
source, editor and whole-tree validation is still required.

## Integration with current origin

The integration with upstream `aa1b76c5` preserves both the native CLI inspection
helpers and the editor runner's entry audits, exact-goal refutations, source
hashes, declaration IDs, ranges and interrupted-batch checkpoints. Goal display
and witness output have separate named arguments. The CLI action path retains
its own request command; audit and witness flags apply to verification requests.

Upstream finite dispatch and typed stable external-function projections
supersede the initial baseline's unsupported function-value roster. The merged
integration test requires all 26 qualified rows: sixteen proofs, seven internal
helpers and three deliberately pending false claims. Metadata again requires
thirteen proofs, one internal helper and one pending false claim. Declaration
selectors still resolve by compiler identity; stored projections use their
separate typed ABI path. Malformed and effectful projections remain rejected.

Read-only finder and skeptic reviews found no blocking merge defect. The
focused Lean build passes all 269 jobs, including CLI, selector admission,
filtered-set proofs and tuple-loop proofs. Both native executables build, all
56 fast integration tests pass, and trust, layering, reachability and inventory
checks pass. This is focused integration validation, not a new whole-tree or
real-editor-host run. Some CLI action and synthetic getter rows lack source IDs;
range enrichment remains conditional on explicit compiler evidence.

All sixteen focused source/CLI checks also pass: entry audits, certified
witnesses, metadata, native verification and inspection, concrete execution,
source-range mapping and the complete function-value verdict roster.
