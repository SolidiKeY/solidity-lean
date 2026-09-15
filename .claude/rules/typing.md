---
paths:
  - "Solidity/StorageTyping.lean"
  - "Solidity/StoragePreservation.lean"
  - "Solidity/StateTyping.lean"
  - "Solidity/TypeSoundness.lean"
  - "Solidity/Reachability.lean"
  - "Solidity/WellFormedConsumers.lean"
  - "Solidity/SemanticsProperties.lean"
  - "Solidity/StuckShape.lean"
---

# Typing and well-formedness

The headline is `execStmt_sound`/`execBlock_sound`: **storage
well-typedness is an inductive invariant of execution**. Three separate
properties surround it, and a change to one usually needs a matching change
to another.

| Property | Where | Says |
|---|---|---|
| Sufficiency | `TypeSoundness.lean` | the invariant is preserved |
| Necessity | `Counterexamples/PreservationNecessity.lean` | nine refutations, each dropping exactly one conjunct, each with a positive twin |
| Tightness | `Reachability.lean` | nothing is missing: any storage property holding initially and preserved by well-typed programs *from well-typed states* already follows from `canonical` |

## Side conditions that are genuinely necessary

`nodupKeysB L.globals`, `nodupKeysB Γ`, `nodupKeysB H`, the `defaultOk` fuel
bound, `op.isArith`, `HeapWellFormed`, entry storage typing, env typing — each
has a numbered refutation in `PreservationNecessity.lean`. Do not drop one
without reading its refutation first. `heapTyNodup` is *not* needed by the
headline: `execStmt_sound_dupHeapTy` proves it without that conjunct, via
`dedupKeys`, since `HeapTy.Extends` reads through `lookupBy`.

`Reachability.lean`'s theorems all take `layoutOkB L` (nodup roots, nodup
`structDef` rows for every reachable struct, nesting depth ≤ 8), including
`initialState_wt`.

## Scope of v1

`stmtWt`'s language excludes `callStmt` (stuck by design), memory `delete`,
branch-declaring `ite`, `.length` reads, and non-`isArith` compound operators.
The docstrings carry the per-lemma notes. `uint` range is **not** an
invariant: `total = -5;` is well-typed (`Witness.uint_negative_reachable`).

`StateTyping.lean`'s `HeapTy` checks refs against `H`'s claim only — shallow,
no coinduction. `envTypedB` also forbids stray `spath`/`mref` bindings.

## Stuckness

`StuckShape.lean` is the interpreter's counterpart of `Coverage.lean`'s
`ResidueShape`, and deliberately has **no** Boolean mirror: unlike residue,
stuckness already has a decision procedure — the interpreter. It leans on the
wildcard expansion in `Semantics.lean`, which is what makes `SVal.find.induct`
a case table with one hypothesis per arm.

## Open

`reachable ⇒ canonical` (the two `_not_reachable` witnesses carry a documented
`sorry`), and its `delete` instance `saveStorage_canonical` in
`WellFormedConsumers.lean` row C6, which is proved at the value level only.
