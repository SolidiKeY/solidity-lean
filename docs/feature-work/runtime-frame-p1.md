# P1 runtime frames: foundation and frozen interface v1

This is a partial checkpoint of the V12 runtime-frame producer (P1, roadmap
items G37–G39). It is not a general runtime-call or source-to-EVM theorem.
All modules are in `Solidity/Backend/InternalFlow/` and use the existing
intrinsic syntax, states, `Evm.run` and the published `Evm.Memory`
certificates. They add no evaluator, AST or world model. Every theorem is
proved, with no `sorry`, axiom or heartbeat change.

## Foundation modules

| Module | Content |
|---|---|
| `RuntimeFrameSemantics` | Replaces `callRec f d args ret thunk` by its finite body `thunk ()`. `statement_run`/`program_run` prove that execution is unchanged, including `recBase` exhaustion. |
| `RuntimeFrameTarget` | Transports published `Calls` certificates along that equation. `callRec_index` compares only the same thunk at two indices. |
| `RuntimeFrameTransport` | Argument evaluation, entry/body extension and result export at the checked target endpoint (`call_return`, `target_return`, `target_recursive_return`). |
| `RuntimeFrameStack` | Word push/pop through a pointer read from target memory (`push_run`, `pop_run`, `push_pop`). Positivity, nonoverlap and no-wrap are explicit premises. |
| `RuntimeFrameSaved` | A frame word written above the caller locals and below the heap preserves the full `StateRepr` (`reserved_write`, `pushed_repr`), and scalar or reference saves read represented caller cells. The `Arena` record packages these bounds but is not used yet. |
| `RuntimeFrameFootprint` | `Footprint.Words`: an interval of words left unchanged by actual allocation, private rebinding and represented array writes. These cover the listed emitter leaves only, not arbitrary callees. |
| `RuntimeFrameComposition` | `Program`/`Statement` pair an existing checked certificate with a derived scratch-safety proof. The proof is built by constructors (`nil`, `cons`, `block`, `branch`, `assign`, `allocate`, …). The selectors `compileCall` and `compileRecursive` return `Option` certificates and accept only call-free bodies. Public selectors and refusals are unchanged. |
| `RuntimeFrameRestore` | Pops a saved word back into the original caller cell (`run`). `local_repr` keeps `StateRepr` when the consumed word equals the cell's content. Heap contents are not restored. |
| `RuntimeFrameContext` | Captures and restores the whole caller context (`capture_context`, `restore_context`), and composes them with a checked body (`program`). |

## Frozen interface v1

`RuntimeFrameInterfaceV1.lean`, namespace
`Solidity.Backend.InternalFlow.RuntimeFrame.InterfaceV1`, is a signature-only
contract for consumers. Signature changes go to a new version.

- `Emission` gives code, fragment, workspace need, local limit, pointer cell
  and two separate budgets: runtime arena words and source heap cost.
- `Entry` is the initial `StateRepr`, the runtime cursor read from the same
  machine, word bounds, header/payload separation and `AllocationInput`.
  `RealizableEntry` asks for at least one such entry.
- `Returned` asks for a successful `Evm.run`, the final `StateRepr`, an
  unchanged evaluation stack, `BaseExtends`, `GrowsAllocator`, the restored
  cursor and the older frame words (`Footprint.Words`).
  `ReturnClaim`/`BareRevertClaim` quantify these over source runs.
  `BareRevertClaim` covers bare `revert` only.
- `PendingCallProducer` and `PendingFixedCallRecProducer` are for ordinary
  calls and a fixed `callRec` thunk. `PendingRecursiveReturns` is for one code
  image over the `recUnroll` family (`RecursiveEmission`, `recursiveSource`,
  `RecursiveReturnCoherence`). `PendingRestoration` holds
  `RestoredRepresentationClaim`, which needs `NoAliasPromotion`.

The `Pending*` structures are unproved premise structures, with no instance.
Consumers take them as parameters.

Known weakness of v1: `RealizableEntry` does not make the return obligations
non-vacuous. `arenaWords` and `heapCost` depend on the caller state, so a plan
can admit (through `Entry.noWrap`) only one caller whose source run fails, and
then `ReturnClaim` and `BareRevertClaim` hold trivially. In
`PendingRecursiveReturns` the entry can be realized only at index 0, where
`recBase` always exhausts. A later version should tie admission to callers
whose source run succeeds, or require entries at every index.

## Open

- G37.01: no `Pending*` instance yet. General caller save/restore agreement
  and runtime return control are still missing, and the scratch-safe
  selectors do not yet compile bodies that contain calls or loops.
- G37.02: unbounded recursion (running prefix, termination, divergence) is
  not covered. Source `recDepth` is unchanged.
- G38: payload and panic failures, the byte journal and world failure transport.
- G39: transient storage, reset and world composition.
- The P2 static-world premises (readonly-external) stay separate.

## Master integration review

Merged from f4fa6f12: the interface and its import closure only. The other
`RuntimeFrame*` modules (Bytes, CodeEquality, Mutation, Nested, Result,
Reference, ReferenceProgram), the `tests/runtime-frame/` fixtures and the
modules of other lanes on that branch were not merged.

Read-only finder and skeptic reviews found no `sorry`, axiom or heartbeat
change, and no import or layer problem. They found the vacuity weakness above,
which is now documented. They also found overstated descriptions of
`local_repr`, `Arena` and the call selectors, which are now corrected in the
docs and docstrings. Signatures are unchanged.
