# Frozen P1 interface v1 (H12)

Module: `Solidity/Backend/InternalFlow/RuntimeFrameInterfaceV1.lean`.
Namespace: `Solidity.Backend.InternalFlow.RuntimeFrame.InterfaceV1`.
These signatures are frozen at their checkpoint commit. Changes require an
explicit coordinator notification; implementations belong in separate modules.

This is an interface-only checkpoint. `PendingCallProducer`,
`PendingFixedCallRecProducer`, `PendingRecursiveReturns` and `PendingRestoration`
are explicitly UNPROVED premise structures. There is no instance, axiom,
proof stub, new evaluator or claim that they are inhabited. Consumers may
stage against their types only with the outstanding obligations visible.

The emitter base b and input Frag are fixed producer parameters, matching
existing checked certificates; the contract does not quantify one static
code image over unrelated bases or unsupported input fragments.

`Emission` separates workspace need, runtime arena words and source heap
allocation cost. `Entry` retains full initial StateRepr, real runtime cursor,
word bounds, header/payload separation and genuine AllocationInput. `Returned`
requires actual existing Evm.run, full final StateRepr, caller evaluation-stack
preservation, old-address extension, exact heap allocator growth, restored
runtime cursor and all older frame words in the protected arena prefix.
Ordinary calls and fixed-thunk callRec use actual intrinsic Stmt constructors.

`RecursiveEmission` has ONE code image independent of n. `recursiveSource`
uses actual recUnroll/recBase; all-finite successful-return and bare-revert
requirements are explicit. Source recDepth, exhausted, panic, payload failures
and divergence retain their original meanings. This is not a proof or complete
interface for G37.02 running-prefix/termination/divergence correspondence; that
remains open and must be relayed as a separate versioned contract when its
actual source/target execution interface is settled. No semantic change or
new supported profile follows from these declarations.

`RestoredRepresentationClaim` states the general old-caller/source transport
and current fragment condition needed for full restored representation. Its
NoAliasPromotion is an explicit producer obligation, not an approved exclusion
of storage aliases or logical locals. Current liveness comes from the actual
post-body representation. No old-heap Heap.Keeps or world rollback is inferred.

P2 is still the separately typed premise already published in the relayed
`Solidity.Lowering.Readonly.InvocationFrame.Invocation.RuntimeFrames`:
mode=true and StaticJournal.History for the SAME after/final source states.
V13's separate SAME-invocation RawAt remains explicit. These world premises
are not consequences of the word-frame signatures here. Byte memory, gas,
external world, transaction/transient rollback and unbounded recursion remain
open. All original Work/Backfill and held final gates remain partial/failed.

Existing proved producer components remain in the preceding RuntimeFrame
modules and P1-01 through P1-10 seals. H12 pauses additional proof work until
this frozen surface is committed and relayed; this checkpoint itself adds no
new proof. The existing blocked persistent goal is unchanged.

Before freezing, independent review identified the vacuous arenaWords=W case.
Every pending call producer now requires a genuine `RealizableEntry`; the
recursive-return producer also requires actual successful-source-family
`RecursiveReturnCoherence`. These are UNPROVED fields, not assertions that
arbitrary builders are coherent or supported. RealizableEntry is only minimum
non-vacuity, not complete profile coverage or proof that computed budgets are
appropriate for all callers. Later implementations still require nontrivial
successful/failing clients and actual source-derived capacity/budget evidence.
No global admission, source exclusion or semantic choice is changed.
