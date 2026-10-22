# Contract lifetime properties

`Solidity/Semantics/Lifetime.lean` adds a transition system rooted at successful
deployment. `Solidity/Calculus/Lifetime.lean` connects its preservation
obligations to existing function correctness proofs. Neither changes the run
or adds a dependency.

## Building a model

Import `Solidity.Calculus.Lifetime` and the usual syntax/proof modules. Work
under `open Solidity.Lifetime`. A `System C D A` supplies:

* `deploy : D → Prog C [] []`: a closed `constructor(args);` call, with its
  initializers elaborated as usual. `D` selects the constructor inputs.
* `call : A → Prog C [] []`: the explicit external interface, a closed
  `f(args);` call for each action. `A` selects the function and typed inputs.
* `payable : A → Bool`: whether that entry accepts value; default `false`.
* `allowDeploy` and `allowCall`: environment restrictions; default `True`.

For example, the escrow in `Solidity/Examples/Tactics/Lifetime.lean` uses:

```lean
inductive Action where
  | pay | refund | deposit | fail | exhaust

def model : System Escrow Unit Action where
  deploy := fun _ => sol[Escrow]{ constructor(); }
  call
    | .pay => sol[Escrow]{ pay(); }
    | .refund => sol[Escrow]{ refund(); }
    | .deposit => sol[Escrow]{ deposit(); }
    | .fail => sol[Escrow]{ fail(); }
    | .exhaust => sol[Escrow]{ exhaust(); }
  payable := fun a => match a with | .deposit | .fail => true | _ => false
```

**The interface is a model obligation.** `Contract` does not retain function
visibility. Select the externally callable methods explicitly, supply their
actual elaborated calls, and copy their `payable` metadata. The structure does
not certify that an arbitrary supplied block is a declared external call or
that its payable flag agrees with the source. Constructors and internal-only
functions must not appear as transaction actions. A missing external method
restricts the model and can invalidate a claim about the complete contract.

`D` and `A` are ordinary Lean types and may carry typed inputs. The selected
program must bind those inputs and close its frame. The example has no
arguments; this layer does not add a new ABI dispatcher or an input quoter.

## States and transitions

`World C` contains typed storage, the KeY net ledger, spendable contract
balance, contract address and last timestamp. It contains no locals, heap,
caller, call value or oracle table. `World.ofState` extracts this persistent
part. `World.observe` gives state predicates a fresh, unpaid observation
frame; caller, value, oracle and memory predicates belong in call entry
obligations, rather than persistent predicates.

`M.Init s` requires an actual `.ok` result from `Contract.deployT`, including
its nonpayable guard, and an admitted deployment. A constructor that reverts,
panics, diverges or exhausts creates no initial deployed state. `AG` ranges
over every admitted successful deployment; `EF` chooses one. Use
`allowDeploy` to fix the deployment of interest, or `CanReach M s P` to start
from a specified deployed state.

`World.accepts` fixes the deployed address, requires nondecreasing timestamps
and excludes a top-level call whose sender is the contract itself. Self-calls
are handled inside the existing program semantics. Additional restrictions
such as authorized callers or admissible oracle replies belong in
`allowCall`.

`World.enter` creates empty memory and locals, credits `msg.value` to the
spendable balance and adds it to the sender's net ledger entry. A zero-value
call leaves the ledger unchanged. An overflowing balance is refused. The
ledger records net flows, not the environment's available money: sufficient
sender funds must be an environment assumption when relevant.

`Step M s event t` has three cases:

| Case | Evidence | Persistent result |
|---|---|---|
| `commit` | Accepted/admitted call and an actual successful `M.run` | The program's final storage, ledger and balance |
| `rollback` | Accepted/admitted call ending in revert, revert data or panic | Original storage, ledger and balance; transaction timestamp |
| `wait` | A nondecreasing timestamp | Original persistent data; new timestamp |

Rollback removes both the incoming payment and all writes, including writes
performed before the failure. Divergence and exhaustion have no completed-call
transition. Waiting permits an unchanged timestamp and state, so inactivity is
present. The model observes completed transaction boundaries, not each
instruction, emitted events or gas costs. Panic rolls back: an invariant of
persistent states alone does not establish that no call panics.

## Safety and possibility

`Trace M s events t` is a finite execution with a checked `Step` for every
label. `Trace.append` composes witnesses. `Reachable M t` starts with an
admitted successful deployment and closes under steps. `reachable_iff_trace`
equates the inductive definition to a finite deployment-rooted witness.

| Predicate | Meaning |
|---|---|
| `AG M P` | Every reachable state satisfies `P` |
| `CanReach M s P` | Some finite continuation from `s` reaches `P` |
| `EF M P` | Some admitted deployment and finite continuation reaches `P` |
| `AGEF M P` | From every reachable state, a finite continuation to `P` exists |

Zero steps count when the target holds already. `CanReach.here` supplies that
witness; `CanReach.next` prepends a step. `ef_iff_reachable` characterizes `EF`
by a reachable target. `AG.not_EF` excludes target witnesses using safety.

These are semantic predicates, not a full CTL parser or a model checker.
`AGEF` expresses that recovery remains possible, including favorable choices
of callers and oracle responses. It does not say a user can force recovery
against an adversary, or that anyone eventually acts. Universal eventuality,
fairness, infinite execution semantics and strategy quantification are not
implemented.

## Proving an invariant

An `Invariant M I` has constructor establishment (`initially`) and one-step
preservation (`preserved`). `Invariant.always` proves `AG M I` by reachable-state
induction. `Invariant.never` excludes a bad state using an invariant stronger
than its negation.

`Invariant.ofRuns` splits the work into successful deployments, successful
calls, and stability when time advances. Its rollback cases follow from time
stability because all other persistent fields are restored. Time-dependent
predicates must really satisfy that obligation; storage-only predicates
usually do so definitionally.

`Invariant.ofSpecs` accepts a `Spec` precondition and postcondition per action,
their existing correctness proofs, entry and interpretation lemmas, constructor
establishment, and time stability. A call's precondition must hold in its fresh
frame **after crediting its payment**. `System.preserves_of_spec` exposes this
bridge for one action. `System.preserves_of_fml` provides the corresponding
bridge for internal dynamic-logic proofs, as the escrow example demonstrates.
Both require explicit interpretation of the postcondition as a persistent
invariant.

**Possible reachability requires successful runs.** The existing diamond
accepts exhaustion. Neither a diamond proof nor an existential state chosen
by callback havoc supplies a lifetime witness. `System.run_ok` extracts the
actual successful entry and program run from every commit.

## Observation and environment limits

This layer uses `Prog.run`, the deterministic reading. An oracle response
does not realize arbitrary callback storage changes. The escrow example has
no external calls. For contracts that can reenter, use the callback calculus
to establish boundary safety separately; this module does not prove that all
real callback executions are represented by lifetime transitions. In
particular, a transaction-boundary invariant does not state that it holds
while control is exposed to another contract.

The environment can advance time and submit the selected transactions. Forced
ether receipts, other contracts' persistent states, account nonces and
environment funding are not represented as additional transitions. Include
them in an extended transition model before making properties that depend
on their effects.

## Milestone L1: constructor-rooted lifetime

Implemented persistent states, incoming payment and rollback, an explicit
interface, waiting, labelled finite traces, reachability induction, `AG`, `EF`
and `AGEF`, and bridges from both correctness readings. The escrow proves
mutual exclusion for every reached state, two concrete settlement witnesses,
and that settlement remains possible from every reached state. Its flags
record settlement; the example does not transfer ether.

Regressions cover payment rollback after a write, refusal of nonpayable value,
successful payable commits and composed deposit/payment traces, blocked
refund after payment, waiting, backwards time, changed addresses,
fresh memory, incoming ledger/balance accounting, exhausted calls that satisfy
the old diamond but cannot commit, and a failed constructor with no reachable
deployed state. `exhaust()` uses Lean's `assume(false)` modelling assumption
solely to exercise exhaustion.

**Review.** Independent read-only finder and skeptic passes confirmed the
deployment root, actual-run evidence, rollback and invariant proof bridges,
and temporal quantification. Neither found a semantic or proof defect. Their
coverage suggestion added a successful payable commit and a two-transaction
deposit/payment trace; incoming funds are checked both when committed and
when rolled back. Interface completeness, payable metadata, callbacks and
environment effects remain the explicit model obligations described above.

**Validation.** Per-file Lean diagnostics report no errors or warnings in the
three new modules. The full default build (453 jobs), TestSuite (174 jobs),
and frozen SolKey sort check pass (377 taclets, all 131 read-bearing
annotations). The example pins the headline theorems' axiom sets to
`propext`, `Classical.choice`, and `Quot.sound`; no new axioms or `sorry`
are used. The final command was:

```sh
LAKE_CACHE_DIR=/tmp/solidity-lean-lifetime-cache \
SOLKEY_RULES=tests/migration/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key \
./run-lean.sh
```

The temporary artifact cache avoids writing to the sandbox's read-only
toolchain cache. The ordinary live-checkout sort check separately reports an
unannotated `localValueDelete` in the sibling SolKey (381 taclets, 132
read-bearing); updating that pin/table is outside this change. The repository
orphan check reaches all three new modules but reports 25 existing ignored
scratch modules. The full documentation path check reports 13 existing
missing references in vendored documentation and the Eqns provenance link;
the new lifetime references resolve. Those broader checks are not claimed
as passing.
