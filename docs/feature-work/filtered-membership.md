# Filtered membership over finite primitive domains

The new NatSpec form declares one typed logical binder and a finite literal
domain:

```solidity
/// @custom:key requires amount \in uint(x; 1, 2, 2; x > 1)
/// @custom:key ensures \result == 2
function echo(uint amount) public pure returns (uint) { return amount; }
```

The key `amount` belongs to the outer scope. Only the guard `x > 1` binds
`x`. In `amount \in uint(amount; 1, 2; amount > 1)`, the key still names
the function parameter, and the guard names the logical value. Nested
filters and existing quantifiers retain the nearest guard binder.
Primitive logical binders also shadow outer storage and memory references:
member/index access on such a binder is rejected. Hidden obligation names
`old`, `oldNet`, `result` and `result_*` are reserved for logical binders,
including nested `forall`/`exists`, as they already are for parameters.

Types are `uint`, `int`, `bool` and `address` (the existing unsigned model
type). Domains contain numeric literals, negative numeric literals, Boolean
literals or fixed `uint(n)` literals at the declared type. The compiler
checks literal ranges and constructs a `List p.Denote` before lowering the
formula. It rejects dynamic domains, arithmetic domain expressions, mixed
sorts, ledger integers and references. Domains are finite independently of
their guards. Their order and duplicate literals do not change membership.

An empty domain is written `key \in uint(x; ; guard)`. It is always false,
but the compiler still checks both the key and the guard. Unknown names,
wrong types, forbidden snapshots and oversized literals cannot disappear
through an empty domain.

The generated scoped formula has this exact meaning:

```text
∃ v : p.Denote,
  v ∈ literalDomain ∧ key.denote(state) = some(v) ∧
  holds(state.push(v), guard)
```

`holds_filteredMember` proves this statement for every typed state. The key
is checked in the outer context and weakened by typed positions under the
binder. An undefined key cannot equal the bound value. The guard uses the
existing KeY formula semantics: equations between two undefined arithmetic
expressions may hold. This facility does not reproduce Dafny's separate
expression-wellformedness obligations. Existing prefix membership
`\in uint(key; items)` retains its existing equality semantics.

Snapshots retain their established meaning. `\old` around the full filter
switches its storage and ledger context; `\old` inside the guard retains
the logical bound value while switching those snapshots. Nested `\old`
and old-memory reads remain rejected. Source parameter renaming only
renames the key and free guard references, preserving bound guard names.

Source constant and enum substitution conservatively leaves a clause
containing this new binder unchanged. A guard binder may therefore shadow
an inherited constant safely. The omitted-state check inspects parsed free
root reads, keeping the key and domain outside the binder's guard scope.
It ignores member labels, retains a lexical precheck for unrelated names,
and rejects parser failures. Other constant aliases in such a clause may
remain unresolved and are rejected rather than guessed. Loop annotations
explicitly reject filtered membership in this milestone.

Signed witnesses and nested quantified filters use the existing bounded
`sol_close_all` fallback, the `allLeft` policy recorded in
[lean-key-rule-map.md](../lean-key-rule-map.md). Closed equality-side values
such as `-1` take priority among its existing candidates. Candidate,
application, binder, node and heartbeat limits remain unchanged; every
instance is a checked application of the original universal proof.

This is formula-valued membership in a finite identity filter. It adds no
first-class sets, cardinality, set operations, general image expressions,
dynamic intervals or collections, multiple binders, allocation-sensitive
domains, reusable predicate declarations or solver triggers. The upstream
research and remaining predicate design are recorded in
[dafny-specification-research.json](../dafny-specification-research.json).

The Lean examples in `Examples/Tactics/FilteredSets.lean` check proof
closure, failure equality, binder positions, malformed operands, snapshot
queries and parser/printer round trips. The source fixture
`tests/solc/FilteredSets.sol` and `scripts/filtered-spec-sets.test.mjs` cover
real source import, lexical capture, inherited constants, signed and Boolean
domains, snapshots, malformed empty domains and an exact-goal certified
counterexample.

Focused verification passed: the generic module (61 jobs), syntax/compiler
(86 jobs), frontend API (254 jobs), and final API/examples (255 jobs). All
five public proof examples and parser, typed-position and free-read controls
pass; the generic denotation and example axiom pins contain only
`propext`, `Classical.choice` and `Quot.sound`.

All three source tests passed in 41.65 seconds with one worker and no
concurrent build producer. Exactly 24 admitted rows remain: 21 proved and
three deliberately pending false claims. All 29 malformed cases remain
explicit: 28 errors and one unsupported loop annotation. The separate
source witness test retains an exact-goal certified counterexample with
the Boolean argument `true`. No failed search is labelled refuted.
