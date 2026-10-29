# Feature work: index and cross-cutting decisions

Each group document says what its feature supports (with the module, API or
test that shows it), what is refused and why, the decisions in force and what
is left. An integrated foundation is not a full source-support verdict: the
inventory status ([solidity-feature-inventory.md](../solidity-feature-inventory.md))
is.

| Group | Supports | Not supported |
|---|---|---|
| [Source admission](source-admission.md) | compiler provenance, complete compilation units, imports/remappings, declaration-aware admission, exact literals, raw names, stored function projections | general function-value dispatch beyond [finite dispatch](finite-dispatch.md) |
| [Finite dispatch](finite-dispatch.md) (with [getter targets](finite-dispatch.md#getter-targets)) | internal and own-external function-value calls over a typed candidate set | reference signatures beyond zero-argument internal memory-byte returns, nominal signatures, source-kind collisions |
| [Declarations](declarations-metadata.md) | `type(C).name`, `type(I).interfaceId`, error/event selectors, primitive/UDVT getters, enum mapping keys, source ABI identities | reference results and enum/contract/function results, broader `using for` |
| [Operators](numeric-operators.md) | resolved scalar UDVT aliases, signed numeric lowering, declaration-indexed finite enum conversions | recursive aggregates and general numeric source correspondence |
| [Aggregates](aggregates.md), [calldata aliases](../calldata-slice-copies.md#calldata-origins-and-aliases), [slice copies](../calldata-slice-copies.md) | inline arrays, fixed memory snapshots, reference tuples, mixed storage/memory conditional joins, primitive tuple write order, slice effects, calldata alias origins, fixed primitive-row slice copies | other reference-element slices and general effectful nonlocal tuple targets |
| [Recursive storage](recursive-types.md) | a standalone typed graph storage API with copy admission and a bridge to ordinary values | recursive structs anywhere in the ordinary pipeline |
| [ABI and hashes](abi-hashes.md) | ERC-7201, `ecrecover`, `encodeCall` checks, decoder bounds, exact-width hex arguments | enum decoding, recursive ABI, external reference returns |
| [Transient storage](transient-storage.md) | typed ordinary transient roots, source reset/rollback, getters, opt-in owner/delegate controls, explicit outer frame composition | physical assembly/layout, gas and general source-world dispatch |
| [Contract world](contract-world.md) | typed creation/call/library frames, hash-checked source commands, explicit wrapper execution/reachability certificates | general world-aware source statements |
| [Calls and exceptions](calls-exceptions.md) | eager error/event operands, exact self-call panic and catch data, fixed-byte error words | named or qualified emits, callback catches |
| [Proof automation](../automation.md#guarded-symmetric-cancellation) | guarded symmetric cancellation `(a + b) - a` | the broader items of [automation.md](../automation.md) |

## Cloud tasks 01–10

[The 01–09 integration record](cloud-integration-01-09.md) covers the first nine
committed snapshots and their cross-lane fixes. [Task 10's integration record](cloud-integration-10.md)
adds raw ABI vector adaptation, exact failure observations, named error operands
and typed aggregate custom errors, with its own bounded validation and remaining
exclusions. The uncommitted recursive-storage migration is not included.
Use these combined records ahead of retained per-lane reports; neither claims
that every source fixture now passes.

## Feature-cloud integration

[The 2026-10-28 integration record](cloud-integration-20261028.md) combines eight
finished feature/baseline workstreams, their shared-file resolutions, historical
evidence replay repairs and combined checks. The still-active getter performance
repair and cancelled SolKey re-pin are excluded. Per-feature refusals remain
explicit; this record does not promote the historical corpus to a fresh merged
baseline.

## Cross-cutting decisions

- **Source input domain.** Imported source obligations, constructors included,
  assume `address(this) < 2^160`; native states keep their wider fields
  ([source-inputs.md](../source-inputs.md)). Source external-function dispatch
  cleans receivers to 160 bits ([finite-dispatch.md](finite-dispatch.md)).
- **Box safety is not termination.** Automation does not close diamond
  obligations across an external `try`, resolved self calls included, so
  source caller tests ask for `@custom:key box`. Positive concrete runs are
  kernel-checked with `runF` and transported to `Prog.run` by
  `Prog.runF_approx`, so they need completed runs, not fuel exhaustion
  (`Examples/Tactics/PublicGetters.lean`).
- **Callback rules** ([options.md](../options.md) O3). `ProvesC.closeFalse`
  requires the whole hypothesis wrapper to be callback-free. `ProvesC.update`
  is side-conditioned on `Stmt.callsBack`, not `Stmt.forksIn` (which marks
  every `if` as forking), so a joinable `if` before a callback-capable `try`
  still updates; its soundness equates callback runs with the typed run
  (`Stmt.eq_run`).
- **Frontend evidence.** Checks on the solc JSON are executable guards, not
  theorems about JSON. The `scripts/check-*.mjs` reference runners use EVM
  packages installed outside Lake. They check Solidity's behaviour, not the
  Lean model's correspondence to it.
- **Build memory.** A clean rebuild within 10 GiB is not established:
  `TestSuite/Derived17.lean` alone exceeded a 10 GiB cap. A fresh import that
  crashes while focused checks pass has usually read a stale transitive
  artifact, so rebuild with a fresh cache before suspecting the source.
  The [bounded validation procedure](../refactoring-progress.md#validation)
  records the passing library/TestSuite/sort checks, explicit worker flag and
  hard 12 GiB cap; it does not establish a 10 GiB bound.
