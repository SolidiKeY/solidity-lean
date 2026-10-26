# Transient storage: composed execution milestone

Integration status (2026-10-26): included in the shared checkout. Current
combined validation is tracked in [integration.md](integration.md).
Worker handoff statuses and isolated validation results below are historical;
they neither report the current combined checks nor establish full source support.

Worker handoff (historical): **patch_ready_unvalidated**. The worker supplied the implementation
without Lean checking; the supplement is now included in combined integration. The `transientState` inventory remains
missing: ordinary source elaboration and scoped transient terms/rules are not
implemented. Physical transient layout, raw `tload`/`tstore` and gas remain
outside the logical model.

## Implemented by this patch

`Semantics/Transient.lean` supplies an explicit model-building supplement that
composes typed transient operations with the actual ordinary `Prog.run`.
`Slot L p` is a declaration position indexed by its primitive type. `Store L`
has exactly the declared values; a reference-typed cell cannot be declared.
Labels are documentation; positions identify cells. The cells are separate
from `State.storage`, its roots and its physical representation.

An ordinary fragment carries `Prog.within μ P = true`. Execution checks source
mutability compatibility, and an inherited static context additionally checks
`Prog.within .view P`. These checks reuse the current frame analysis; the
supplement does not infer safety from a user-supplied arbitrary state
transformer. `Program.ordinary_frame` uses `Prog.run_frame` and its conditional
balance/storage/ledger preservation directly. `Prog.within` currently admits
only heap-neutral fragments. Memory-allocating ordinary fragments and locals
spanning fragment boundaries are not admitted by this API.

Zero-value calls to the same owning contract share persistent and transient
cells. A child starts with fresh heap/locals, `msg.sender = selfAddress` and
zero `msg.value`; entry does not book the outer payment again. Successful
return adopts child storage, ledger, balance and transient cells, and restores
the caller's heap and transaction metadata. This supplements the ordinary
interpreter; it does not change `TRun.tryCall`'s existing frame semantics.
Calls to another owning contract and delegate calls are not represented here.

A caught revert, revert with data or panic restores the whole entry
`FrameState`, including successful descendant writes to either store.
Divergence and exhaustion propagate instead of becoming successful catch
results. Static execution prohibits transient writes through all descendant
calls; pure frames cannot read transient cells. Source mode compatibility is
checked separately from inherited static execution.

`Program.transact` uses `Lifetime.World.enter` for payment and fresh top-level
entry, supplies `Store.empty`, and discards the transient store at exit.
`transact_ok` requires actual successful entry and execution. The address,
time, payable-interface and environment restrictions of a lifetime model are
still its explicit caller obligations. `transact_ordinary` states equality
with the existing `Lifetime.System.run` when the body has only its ordinary
fragment. A failed transaction returns no changed world; it cannot commit.

`Calculus/Transient.lean` reads the supplement with the existing
`Modality.afterRunTR`: boxes exclude panic, and diamonds retain the ordinary
exhaustion policy. It provides sequencing, successful-post extraction, and
ordinary `Spec` box/diamond proof bridges, including reuse of a theorem obtained
from `Proves.valid`. This is not a new transient `Taclet` or an extension of
`Fml`. `Examples/Tactics/TransientStorage.lean` exercises actual persistent
ordinary writes alongside transient sharing/reset/rollback, typed boolean and
integer cells, static writes, false properties and an ordinary calculus proof.

## Source admission safety

Until the ordinary scoped bridge exists, the contract reader must reject a
contract containing a transient declaration, rather than print it as an
ordinary persistent root. The header guard runs over the inherited state
declarations before lowering any of them. It also covers unused declarations,
public getters and a function that never mentions the cell. This supplements
the concurrent source-admission work; the integrator may replace the guard
with an equivalent structured whole-contract diagnostic only if the regression
continues to pass. It must not be relaxed merely because the supplement exists.

The source fixture has successful and failing reentrancy/rollback properties,
static writes, a header/getter-only case, inheritance and a persistent control
contract. `scripts/transient-storage.test.mjs` requires whole-contract refusal
for the transient contracts, proves the persistent control assertion, and
keeps its false assertion pending. A pending row is not a refutation; the
independent EVM vectors check the false source properties actually panic.

## Broad migration still required

Full source support requires retaining transient declarations in `Contract`
and introducing typed reads/writes in the ordinary scoped syntax, signature,
updates, terms, printers, quotation, tools and source elaborator. A transient
read must be captured as a mutable value, not classified as `Simple`: it cannot
move across a sibling call which changes the cell. Narrow widths, signedness,
aliases and source mutability must be retained.

Adding a field to `State` alone is unsound. Callback and loop havoc must range
over the new store, and all state rebuilding/weakening/frame/anonymous-state
proofs must include it. The current modifies-set `FrameKeeps`/`Prog.storeAt`
interface (origin/master commit `2c1ce2e7`) must distinguish persistent root
modification from transient modification. A view loop frame must preserve both
stores; an arbitrary mutable callback cannot preserve transient cells by fiat.
The calculus's `holds`, callback `holdsC`, closers, `Upd.Lands`, function and
recursive contracts, `TGFrame` and their soundness proofs need to migrate
together. Different owning contracts also need a world interface with typed
owner identity and rollback of all descendants, including delegate ownership.

This patch leaves those indexed datatypes unchanged. It does not undo the
upstream speed-oriented core layering or the modifies-set optimization.
Consequently it avoids invalidating the dependent constructor folds just to
land a store field that the existing calculus cannot yet read soundly.

## Validation and review

The patch worker did not run Lean, MCP, builds, or source runners against the
real checkout. All following Lean claims are proof scripts requiring validation.
The primary should check the semantic module, then its calculus bridge, then
the example module; inspect their headline axiom sets. Check the frontend after
merging concurrent source admission and build `Solidity.Frontend.Testing` before
running `node --test scripts/transient-storage.test.mjs`.

The worker ran only pure scripts against its own staged files:

- `node --check` on both new JavaScript scripts: passed.
- Pinned solc `0.8.38+commit.1835d247` and an in-memory Cancun VM: 18 signed
  transaction executions across legacy/viaIR passed, including two real
  successive transactions on the same VM with transient reset and persistent
  preservation. The test never manually clears the transient store.
- Twelve compiler rejection checks (six invalid declarations/effects in both
  pipelines): passed.

The reference command is `node scripts/check-transient-vectors.mjs SOLJSON_FILE
EXTERNAL_NODE_MODULES`. It pins compiler bytes, needs no Lake dependencies,
does not install anything, and writes no fixture or checkout output.

The read-only finder checked current and origin/master frame interfaces,
fresh self-call semantics, header admission and ordinary proof integration.
The read-only skeptic confirmed the semantic boundary and found a cross-carrier
panic-exclusion proof issue in `holds_bind`; it was corrected by transporting
the exception equality explicitly. Self-review also replaced decidability-based
error equalities over dependent states with direct reduction proofs. Neither
reviewer invoked Lean or changed files. The dependent recursor, structural
store recursion and normalization in `transact_ordinary` remain focused
elaboration checks for the integrator.

After Lean validation, run reachability/layering, doc-path, inventory consistency,
ordinary TestSuite/corpus and frozen-SolKey checks appropriate to integration.
Do not upgrade the feature status based on these supplemental examples.

## Upstream reference

Semantics follow the manifest-pinned [Solidity v0.8.38 transient-storage
chapter](https://github.com/argotorg/solidity/blob/1835d247de183f23e7b0e2bc4a50732af525b77c/docs/contracts/transient-storage.rst).
The source/EVM tests use actual zero-value self-calls, successful descendants,
an ancestor revert, static execution and top-level transaction boundaries.
