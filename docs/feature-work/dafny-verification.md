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
examples. NatSpec tuple `decreases` syntax and total recursive termination remain
separate work. Bounded recursive contracts retain their existing exhaustion policy.

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
